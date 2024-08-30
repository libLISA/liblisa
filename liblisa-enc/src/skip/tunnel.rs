use std::time::{Duration, Instant};

use liblisa::arch::{Arch, Scope};
use liblisa::instr::{FilterList, InstructionCounter};
use liblisa::oracle::Oracle;
use log::{info, trace};

use crate::cache::EncodingAnalysisCache;
use crate::Validity;

/// Skip byte strings that are invalid instructions using tunneling.
pub fn tunnel_invalid_instrs<A: Arch, O: Oracle<A>>(counter: &mut InstructionCounter, o: &mut O, scope: &impl Scope) {
    let start_instr = counter.current();

    'outer_invalid: for _ in 0..200 {
        let mut steps: usize = 0;
        let mut can_go_fast = false;
        while steps < 500_000 {
            if let (true, Some(next256)) = (can_go_fast, counter.next_happy_group()) {
                let validities = Validity::infer_batch(o, &next256, scope);
                for (validity, instr) in validities.zip(next256.iter()) {
                    assert_eq!(instr, &counter.current());
                    steps += 1;
                    match validity {
                        Validity::InvalidInstruction | Validity::Excluded | Validity::Error => {
                            if !counter.tunnel_next(&FilterList::new(), 200) {
                                break 'outer_invalid
                            }
                        },
                        Validity::TooShort => {
                            if !counter.extend(&FilterList::new(), false) {
                                break 'outer_invalid
                            } else {
                                can_go_fast = false;
                                break
                            }
                        },
                        Validity::TooLong => {
                            if !counter.reduce(&FilterList::new(), false) {
                                break 'outer_invalid
                            } else {
                                can_go_fast = false;
                                break
                            }
                        },
                        Validity::Ok => break 'outer_invalid,
                    }
                }

                trace!("Fast-forward to {:X}", counter.current());
            } else {
                steps += 1;
                can_go_fast = false;
                let validity = if scope.is_instr_in_scope(counter.current().bytes()) {
                    Validity::infer(o, &counter.current())
                } else {
                    Validity::Excluded
                };
                trace!("{:X} = {validity:?}", counter.current());
                match validity {
                    Validity::TooShort => {
                        if !counter.extend(&FilterList::new(), false) {
                            break 'outer_invalid
                        }
                    },
                    Validity::TooLong => {
                        if !counter.reduce(&FilterList::new(), false) {
                            break 'outer_invalid
                        }
                    },
                    Validity::Ok => break 'outer_invalid,
                    Validity::InvalidInstruction | Validity::Excluded | Validity::Error => {
                        can_go_fast = true;
                        if !counter.tunnel_next(&FilterList::new(), 200) {
                            break 'outer_invalid
                        }
                    },
                }
            }
        }

        println!("Tunneling progress: {:X}", counter.current());
    }

    info!("Tunneled between {:X} and {:X}", start_instr, counter.current());
}

/// Skip instructions for which [`crate::MemoryAccessAnalysis`] returns an error using tunneling.
pub fn tunnel_memory_errors<A: Arch, O: Oracle<A>, S: Scope>(
    mut counter: InstructionCounter, scope: &S, o: &mut O, cache: &impl EncodingAnalysisCache<A>,
) -> InstructionCounter {
    let instr = counter.current();
    let end = counter.end();
    info!("Tunneling from {:X}", instr);
    let mut last_invalid = instr;
    let stopwatch = Instant::now();
    'outer_ma: for num in 0.. {
        for _ in 0..100 {
            let fast_tunnel = num >= 25;
            let result = if scope.is_instr_in_scope(counter.current().bytes()) {
                Validity::infer(o, &counter.current())
            } else {
                Validity::InvalidInstruction
            };
            trace!("{:X} = {result:?}", counter.current());
            match result {
                Validity::TooShort => {
                    if !counter.extend(&FilterList::new(), fast_tunnel) {
                        break 'outer_ma
                    }
                },
                Validity::TooLong => {
                    if !counter.reduce(&FilterList::new(), fast_tunnel) {
                        break 'outer_ma
                    }
                },
                Validity::InvalidInstruction | Validity::Excluded | Validity::Error => break 'outer_ma,
                Validity::Ok => match cache.infer_accesses(o, &counter.current()) {
                    Ok(_) => break 'outer_ma,
                    Err(_) => {
                        last_invalid = counter.current();
                        if !counter.tunnel_next(&FilterList::new(), 32) {
                            break 'outer_ma
                        }
                    },
                },
            }
        }

        info!("Tunneling progress: {:X}", counter.current());

        if stopwatch.elapsed() > Duration::from_secs(15 * 60) {
            break;
        }
    }

    info!("Tunneled between {:X} and {:X}", instr, last_invalid);

    counter.set_end(end);
    counter
}
