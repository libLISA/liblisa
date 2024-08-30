use std::mem;

use fxhash::FxHashSet;
use liblisa::arch::{Arch, Scope};
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use log::{info, trace};
use rand::Rng;

use crate::Validity;

// Only public for the benchmark.
#[doc(hidden)]
pub fn random_instr_bytes<R: Rng>(rng: &mut R, start: Instruction, end: Option<Instruction>) -> [u8; 16] {
    // trace!("Random instr bytes with start={start:X}, end={end:X?}");
    let num_at_end = end
        .map(|instr| {
            if instr.byte_len() > 1 {
                rng.gen_range(0..instr.byte_len() - 1)
            } else {
                0
            }
        })
        .unwrap_or(0);
    let mut is_min = true;
    let mut is_max = true;
    let mut result = [0; 16];

    for (index, (b, max)) in result
        .iter_mut()
        .zip(end.as_ref().map(|end| end.bytes()).unwrap_or(&[]).iter().copied())
        .enumerate()
        .take(num_at_end)
    {
        let min = start.bytes().get(index).copied().unwrap_or(0);
        *b = max;

        // trace!("I[{index}] = 0x{b:X}");

        is_min &= min == max;
    }

    // The last index where we can avoid generating an instruction equal to `end`.
    let last_max_avoid_index = end
        .map(|end| end.byte_len() - 1 - end.bytes().iter().rev().take_while(|&&b| b == 0).count())
        .unwrap_or(16);
    for (index, b) in result.iter_mut().enumerate().skip(num_at_end) {
        let min = start.bytes().get(index).copied().unwrap_or(0);
        let max = end.and_then(|end| end.bytes().get(index).copied()).unwrap_or(0xFF);
        let max_inclusive = end.is_none() || index != last_max_avoid_index;
        // trace!("min=0x{min:X}, max=0x{max:X}, is_min={is_min}, is_max={is_max}, max_inclusive={max_inclusive}");

        *b = match (is_min, is_max) {
            (true, true) => {
                let r = if max_inclusive {
                    rng.gen_range(min..=max)
                } else {
                    rng.gen_range(min..max)
                };
                is_min &= min == r;
                is_max &= max == r;

                r
            },
            (true, false) => {
                let r = rng.gen_range(min..=0xFF);
                is_min &= min == r;

                r
            },
            (false, true) => {
                let r = if max_inclusive {
                    rng.gen_range(0..=max)
                } else {
                    rng.gen_range(0..max)
                };
                is_max &= max == r;

                r
            },
            (false, false) => {
                rng.fill_bytes(&mut result[index..]);
                break
            },
        };

        // trace!("I[{index}] = 0x{b:X}");
    }

    debug_assert!(
        end.map(|end| &result[..end.byte_len()] != end.bytes()).unwrap_or(true),
        "result should be less than end: {end:X?}"
    );

    result
}

fn min_length(prefixes: &FxHashSet<Instruction>, bytes: &[u8; 16]) -> usize {
    for len in 1..16 {
        if !prefixes.contains(&Instruction::new(&bytes[..len])) {
            return len
        }
    }

    16
}

/// Skip consecutive byte strings that are invalid instructions using randomized search.
pub fn random_search_skip_invalid_instrs<A: Arch>(
    rng: &mut impl Rng, start: Instruction, o: &mut impl Oracle<A>, scope: &impl Scope,
) -> (usize, Option<Instruction>) {
    let mut end = None;
    let mut last_change = 0;
    let mut prefixes = FxHashSet::default();
    let mut invalid = FxHashSet::default();

    let mut batch = Vec::new();
    let mut new_batch = Vec::new();
    let mut n = 0;

    loop {
        batch.clear();
        mem::swap(&mut new_batch, &mut batch);
        while batch.len() < 512 {
            let bytes = random_instr_bytes(rng, start, end);
            batch.push((bytes, min_length(&prefixes, &bytes)));
        }

        batch.retain(|(instr, len)| !invalid.contains(&Instruction::new(&instr[..*len])));
        n += 512 - batch.len();

        let instrs = batch
            .iter()
            .map(|(instr, len)| Instruction::new(&instr[..*len]))
            .collect::<Vec<_>>();
        for ((bytes, len), result) in batch.iter().copied().zip(Validity::infer_batch::<A, _>(o, &instrs, scope)) {
            n += 1;
            let instr = Instruction::new(&bytes[..len]);
            match result {
                Validity::TooShort => {
                    trace!("Too short: {instr:X}");
                    prefixes.insert(instr);
                    new_batch.push((bytes, len + 1));
                },
                Validity::TooLong => {
                    trace!("Too long: {instr:X}");
                },
                Validity::InvalidInstruction | Validity::Excluded | Validity::Error => {
                    trace!("Invalid: {instr:X}");
                    invalid.insert(instr);
                },
                Validity::Ok => {
                    trace!("OK: {instr:X}");
                    if end.map(|end| instr < end).unwrap_or(true) {
                        info!("  end: {instr:X}");
                        last_change = n;
                        end = Some(instr);
                    }
                },
            }
        }

        if n > last_change + 1_000_000 {
            break
        }
    }

    info!("Random search terminated on: {end:X?}");

    (last_change, end)
}
