use std::iter::repeat_with;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{Dataflow, Source};
use liblisa::encoding::Encoding;
use liblisa::oracle::{Oracle, OracleError};
use liblisa::state::random::StateGen;
use liblisa::state::{AsSystemState, SystemState};
use log::{debug, info};
use rand::seq::IteratorRandom;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::Validity;

struct Test<'a, A: Arch> {
    output_dataflows: Vec<&'a Dataflow<A, ()>>,
    state: SystemState<A>,
}

impl<A: Arch> AsSystemState<A> for Test<'_, A> {
    type Output<'a>
        = &'a SystemState<A>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        &self.state
    }
}

pub fn remove_incorrect_generalizations<A: Arch, O: Oracle<A>>(o: &mut O, encoding: &mut Encoding<A, ()>) -> bool {
    info!("Removing incorrect generalizations...");
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
    let mut rng2 = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
    let mappable = o.mappable_area();
    let mut changed = false;

    for _ in 0..encoding.instr().bit_len() * 5 {
        if encoding.parts.is_empty() {
            break;
        }

        let mut bad_instrs = Vec::new();
        let mut ok_instrs = Vec::new();
        for n in 0..50_000 {
            let part_values = encoding
                .parts
                .iter()
                .map(|part| rng.gen::<u64>() & ((1 << part.size) - 1))
                .collect::<Vec<_>>();
            if let Ok(instance) = encoding.instantiate(&part_values) {
                let validity = Validity::infer(o, instance.instr());
                match validity {
                    Validity::TooShort
                    | Validity::TooLong
                    | Validity::InvalidInstruction
                    | Validity::Excluded
                    | Validity::Error => {
                        bad_instrs.push(*instance.instr());
                    },
                    Validity::Ok => {
                        if let Ok(state_gen) = StateGen::new(&instance.addresses, &mappable) {
                            if let Ok(mut base_state) = state_gen.randomize_new(&mut rng) {
                                if state_gen.adapt(&mut base_state, false) {
                                    let base_result = o.observe(&base_state);

                                    let checks = instance
                                        .output_dataflows()
                                        .map(|output_dataflow| vec![output_dataflow])
                                        .chain(
                                            repeat_with(|| {
                                                let amount = rng2.gen_range(1..instance.output_dataflows().count());
                                                instance.output_dataflows().choose_multiple(&mut rng2, amount)
                                            })
                                            .take(if instance.output_dataflows().count() > 1 { 10 } else { 0 }),
                                        )
                                        .flat_map(|output_dataflows| {
                                            let mut second_state = state_gen.randomize_new(&mut rng).unwrap();
                                            for flow in output_dataflows
                                                .iter()
                                                .copied()
                                                .chain(instance.overlapping_outputs(&output_dataflows))
                                            {
                                                if flow.unobservable_external_inputs {
                                                    return None
                                                }
                                            }

                                            let inputs_to_keep_identical = output_dataflows
                                                .iter()
                                                .flat_map(|output_dataflow| output_dataflow.inputs().iter())
                                                .chain(
                                                    instance
                                                        .overlapping_outputs(&output_dataflows)
                                                        .flat_map(|other_output| other_output.inputs.iter()),
                                                );
                                            for input in inputs_to_keep_identical {
                                                match input {
                                                    Source::Dest(d) => {
                                                        second_state.set_dest(d, &base_state.get_dest(d));
                                                    },
                                                    // We can't change the values of these.
                                                    // That is not a problem, because they will be the same for both states.
                                                    Source::Imm(_)
                                                    | Source::Const {
                                                        ..
                                                    } => (),
                                                }
                                            }

                                            if state_gen.adapt(&mut second_state, false) {
                                                Some(Test {
                                                    output_dataflows,
                                                    state: second_state,
                                                })
                                            } else {
                                                None
                                            }
                                        });

                                    let equal = o.batch_observe_iter(checks).all(|(test, new_result)| {
                                        test.output_dataflows.iter().all(|output_dataflow| {
                                            let dest = &output_dataflow.target;

                                            let equal = match (&base_result, &new_result) {
                                                (Ok(base), Ok(new)) => {
                                                    base.get_dest(dest) == new.get_dest(dest)
                                                },
                                                // This should never be possible. If it happens, we mis-mapped some bits.
                                                (Err(OracleError::InvalidInstruction), Err(OracleError::InvalidInstruction)) => false,
                                                (Err(OracleError::MultipleInstructionsExecuted), _) | (_, Err(OracleError::MultipleInstructionsExecuted)) => todo!("Multiple instructions executed"),
                                                (Ok(_), Err(OracleError::MemoryAccess(_))) | (Err(OracleError::MemoryAccess(_)), Ok(_)) => false,
                                                // TODO: Should we compare Err()s as well?
                                                _ => true,
                                            };

                                            if !equal {
                                                debug!("Not equal in dest {dest:?}. From states: {base_state:X?}, {:?}\n To states: {base_result:X?} {new_result:X?}", test.state);
                                            }

                                            equal
                                        })
                                    });

                                    if equal {
                                        ok_instrs.push(instance.addresses.instr);
                                    } else {
                                        bad_instrs.push(instance.addresses.instr);
                                    }
                                }
                            } else {
                                info!("randomize_new failed");
                            }
                        } else {
                            info!("Unable to construct StateGen for {instance}");
                        }
                    },
                }
            }

            // Allow early break if instruction seems to be OK
            if n > 8_000 + bad_instrs.len() * 2500 {
                break;
            }
        }

        if !bad_instrs.is_empty() {
            let instr = encoding.instr();
            let mut responsible_bits = (0..instr.bit_len())
                .map(|n| {
                    let num_different_in_bad = bad_instrs
                        .iter()
                        .filter(|bad| bad.nth_bit_from_right(n) != instr.nth_bit_from_right(n))
                        .count();
                    (n, num_different_in_bad as isize)
                })
                .collect::<Vec<_>>();
            responsible_bits.sort_by_key(|(b, c)| (-c, usize::MAX - b));
            info!(
                "Remove most responsible bit: {:?} in {} / {:?}",
                responsible_bits, encoding, encoding
            );

            let v = responsible_bits[0].1 * 8 / 10;
            responsible_bits.retain(|(_, c)| *c >= v);

            // Choose the entry that removes the least good values and the most invalid values
            responsible_bits.sort_by_cached_key(|(n, _)| {
                let (good, invalid) = encoding.preview_make_bit_fixed(*n);
                (good * 1000).checked_div(good + invalid).unwrap_or(usize::MAX)
            });

            info!("Choosing from: {:?}", responsible_bits);

            encoding.make_bit_fixed(responsible_bits[0].0).unwrap();

            info!("Resulting encoding: {} / {:?}", encoding, encoding);
            changed = true;
        } else {
            break;
        }
    }

    changed
}
