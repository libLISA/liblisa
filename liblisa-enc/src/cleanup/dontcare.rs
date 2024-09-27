use std::collections::HashMap;

use liblisa::arch::Arch;
use liblisa::encoding::bitpattern::Bit;
use liblisa::encoding::dataflows::Dataflows;
use liblisa::encoding::Encoding;
use liblisa::instr::Instruction;
use liblisa::oracle::{Oracle, OracleError};
use liblisa::state::random::StateGen;
use liblisa::state::{AsSystemState, SystemState};
use log::{debug, info, trace, warn};
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::encoding::EncodingError;
use crate::Validity;

pub struct DontCareValidator<'a, A: Arch> {
    dataflows: &'a Dataflows<A, ()>,
}

#[derive(Copy, Clone, Debug)]
struct BaseInfo<'a, A: Arch> {
    state: &'a SystemState<A>,
    result: &'a Result<SystemState<A>, OracleError>,
    dataflows: &'a Dataflows<A, ()>,
    modified_instr: Instruction,
}

impl<'a, A: Arch> BaseInfo<'a, A> {
    fn with_modified_instr(&self, modified_instr: Instruction) -> BaseInfo<'a, A> {
        let mut result = *self;
        result.modified_instr = modified_instr;
        result
    }
}

impl<'a, A: Arch> DontCareValidator<'a, A> {
    pub fn new(dataflows: &'a Dataflows<A, ()>) -> DontCareValidator<'a, A> {
        Self {
            dataflows,
        }
    }

    fn modified_instr_is_ok<O: Oracle<A>>(&mut self, oracle: &mut O, base: BaseInfo<A>) -> bool {
        let base_instr = base.dataflows.instr();
        let modified_state = {
            let mut s = base.state.clone();
            s.memory_mut().get_mut(0).set_data(base.modified_instr.bytes());
            s
        };
        let mut modified_result = oracle.observe(&modified_state);
        if let (Ok(base_result), Ok(modified_result)) = (&base.result, &mut modified_result) {
            // Replace the modified instruction with the base instruction so that the memory is identical
            modified_result
                .memory_mut()
                .get_mut(0)
                .set_data(&base_result.memory().get(0).2);
        }

        match (&base.result, &modified_result) {
            // We expect the instruction to either execute successfully or fail with a computation error
            // If we see anything else, something has gone horribly wrong during the previous steps.
            // In that case, it's probably best not to try and filter more bits because we can't be too sure
            // about the result.
            (Ok(a), Ok(b)) if a == b => true,
            (Err(OracleError::ComputationError), Err(OracleError::ComputationError)) => true,
            (Err(OracleError::GeneralFault), Err(OracleError::GeneralFault)) => true,
            (Err(OracleError::InstructionFetchMemoryAccess(a)), Err(OracleError::InstructionFetchMemoryAccess(b))) if a == b => {
                true
            },
            (Err(OracleError::MultipleInstructionsExecuted), _) | (_, Err(OracleError::MultipleInstructionsExecuted)) => {
                todo!("Multiple instructions executed")
            },
            _ => {
                warn!(
                    "Found invalid DontCare bits between instruction {:?} and {:?} because of differences for inputs: {:?}; Outputs: {:X?} vs {:X?}",
                    base_instr, base.modified_instr, base.state, base.result, modified_result
                );
                false
            },
        }
    }

    fn isolate_invalid_dontcare_bits<O: Oracle<A>>(
        &mut self, oracle: &mut O, randomize: bool, value: usize, dont_care_indices: &mut Vec<usize>,
        encoding: &mut Encoding<A, ()>, base: BaseInfo<A>,
    ) {
        let base_instr = base.dataflows.instr();
        if !randomize {
            // We are enumerating all possible DontCare values in ascending order.
            // All values before this were OK.
            // So the highest set bit must be the cause of this difference.
            // We remove that bit from the DontCare set, and try again.
            if let Some(highest_dontcare_index) = ((0usize).leading_zeros() - value.leading_zeros())
                .checked_sub(1)
                .map(|x| x as usize)
            {
                let bit_index = dont_care_indices.remove(highest_dontcare_index);
                encoding.bits[bit_index] = Bit::Fixed(encoding.dataflows.addresses.instr.nth_bit_from_right(bit_index));
            } else {
                assert_eq!(
                    &base.modified_instr, base_instr,
                    "There is no highest_dontcare_index, so the instruction should be equal"
                );
                // Just ignore this I guess? If we see this we are producing different results for multiple runs.
            }
        } else {
            // We could try a more sophisticated approach, but randomized DontCare checks don't occur often.
            // For now it does not seem worth it to make this more complicated.
            let mut responsible_bits = dont_care_indices
                .iter()
                .copied()
                .filter(|&bit_index| {
                    base_instr.nth_bit_from_right(bit_index) != base.modified_instr.nth_bit_from_right(bit_index)
                })
                .collect::<Vec<_>>();

            loop {
                info!("Responsible bits = {:?}", responsible_bits);

                let before = responsible_bits.len();
                responsible_bits.retain(|&bit_index| {
                    let modified_instr = base.modified_instr.with_nth_bit_from_right_flipped(bit_index);
                    self.modified_instr_is_ok(oracle, base.with_modified_instr(modified_instr))
                });

                info!("Filtered responsible bits down to = {:?}", responsible_bits);

                if before == responsible_bits.len() {
                    break;
                }
            }

            if responsible_bits.is_empty() {
                dont_care_indices.retain(|&bit_index| {
                    if base_instr.nth_bit_from_right(bit_index) != base.modified_instr.nth_bit_from_right(bit_index) {
                        info!(
                            "Removing DontCare bit at index {} because of modified instr {:X}",
                            bit_index, base.modified_instr
                        );
                        // Remove the bit from the encoding
                        encoding.bits[bit_index] = Bit::Fixed(encoding.dataflows.addresses.instr.nth_bit_from_right(bit_index));

                        false
                    } else {
                        true
                    }
                });
            } else {
                dont_care_indices.retain(|&bit_index| {
                    if !responsible_bits.contains(&bit_index) {
                        true
                    } else {
                        info!(
                            "Removing DontCare bit at index {} because of modified instr {:X}",
                            bit_index, base.modified_instr
                        );
                        // Remove the bit from the encoding
                        encoding.bits[bit_index] = Bit::Fixed(encoding.dataflows.addresses.instr.nth_bit_from_right(bit_index));

                        false
                    }
                });
            }

            info!("Remaining DontCare indices: {dont_care_indices:?}");
        }
    }

    pub fn validate_dontcare<O: Oracle<A>>(
        &mut self, oracle: &mut O, encoding: &mut Encoding<A, ()>,
    ) -> Result<(), EncodingError<A>> {
        let mappable = oracle.mappable_area();
        let mut dont_care_indices = encoding
            .bits
            .iter()
            .enumerate()
            .filter(|(_, bit)| matches!(bit, Bit::DontCare))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();

        info!(
            "DontCare indices are: {:?} for {} {:?}",
            dont_care_indices, encoding, encoding
        );

        let mut num_errs = 0;
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let mut validity_cache = HashMap::new();
        for num_inst in 0..500 {
            debug!("DontCare validation step: {num_inst} / 500");
            let part_values = encoding
                .parts
                .iter()
                .map(|part| rng.gen::<u64>() & ((1 << part.size) - 1))
                .collect::<Vec<_>>();
            if let Ok(instance) = encoding.instantiate(&part_values) {
                debug!("Checking instance {instance}");
                if let Ok(state_gen) = StateGen::new(&instance.addresses, &mappable) {
                    let base_instr = instance.addresses.instr;

                    if Validity::infer(oracle, &base_instr) != Validity::Ok {
                        if let Ok(base_state) = state_gen.randomize_new(&mut rng) {
                            self.isolate_invalid_dontcare_bits(
                                oracle,
                                true,
                                0,
                                &mut dont_care_indices,
                                encoding,
                                BaseInfo {
                                    dataflows: &instance,
                                    state: &base_state,
                                    result: &Err(OracleError::GeneralFault),
                                    modified_instr: *self.dataflows.instr(),
                                },
                            );
                        }
                    } else {
                        for _ in 0..5 {
                            debug!("Using {:?} as base ({:X})", base_instr, base_instr);
                            if let Ok(base_state) = state_gen.randomize_new(&mut rng) {
                                let base_result = oracle.observe(&base_state);
                                let randomize = dont_care_indices.len() > 14;
                                let modified_instrs =
                                    self.generate_modified_instrs(randomize, &dont_care_indices, &mut rng, base_instr);

                                let invalid_case = match Self::check_modified_instr_validity(
                                    modified_instrs,
                                    &mut validity_cache,
                                    oracle,
                                    &base_state,
                                ) {
                                    Ok(testcases) => {
                                        let observed_testcases = oracle.batch_observe_iter(testcases.into_iter());
                                        self.validate_dontcare_for_testcases(&base_state, &base_result, observed_testcases)
                                    },
                                    Err(invalid_case) => Some(invalid_case),
                                };

                                if let Some((value, modified_instr)) = invalid_case {
                                    self.isolate_invalid_dontcare_bits(
                                        oracle,
                                        randomize,
                                        value,
                                        &mut dont_care_indices,
                                        encoding,
                                        BaseInfo {
                                            dataflows: &instance,
                                            state: &base_state,
                                            result: &base_result,
                                            modified_instr,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            } else {
                num_errs += 1;
            }
        }

        info!("DontCare validation, num_errs = {}", num_errs);

        Ok(())
    }

    fn generate_modified_instrs<'x>(
        &self, randomize: bool, dont_care_indices: &'x [usize], rng: &'x mut Xoshiro256PlusPlus, base_instr: Instruction,
    ) -> impl Iterator<Item = (usize, Instruction)> + 'x {
        (0..(1usize << dont_care_indices.len().min(14))).map(move |value| {
            let value = if randomize {
                rng.gen::<usize>() & ((1usize << dont_care_indices.len()) - 1)
            } else {
                value
            };

            let modified_instr = dont_care_indices.iter().enumerate().fold(base_instr, |acc, (n, bit_index)| {
                // Flip the bits that correspond to the bits that are set in `value`
                acc.with_nth_bit_from_right(
                    *bit_index,
                    base_instr.nth_bit_from_right(*bit_index) ^ ((value >> n) as u8 & 1),
                )
            });

            trace!("Modified({:0b}) = {:?}", value, modified_instr);

            (value, modified_instr)
        })
    }

    fn check_modified_instr_validity<O: Oracle<A>>(
        modified_instrs: impl Iterator<Item = (usize, Instruction)>, validity_cache: &mut HashMap<Instruction, Validity>,
        oracle: &mut O, base_state: &SystemState<A>,
    ) -> Result<Vec<TestCase<A>>, (usize, Instruction)> {
        let mut valid_modified_instrs = Vec::new();
        for (value, modified_instr) in modified_instrs {
            let is_valid = Validity::Ok
                == *validity_cache
                    .entry(modified_instr)
                    .or_insert_with(|| Validity::infer(oracle, &modified_instr));
            if !is_valid {
                return Err((value, modified_instr))
            }

            valid_modified_instrs.push(TestCase {
                value,
                modified_instr,
                state: {
                    let mut s = base_state.clone();
                    s.memory_mut().get_mut(0).set_data(modified_instr.bytes());
                    s
                },
            });
        }

        Ok(valid_modified_instrs)
    }

    fn validate_dontcare_for_testcases(
        &self, base_state: &SystemState<A>, base_result: &Result<SystemState<A>, OracleError>,
        testcases: impl IntoIterator<Item = (TestCase<A>, Result<SystemState<A>, OracleError>)>,
    ) -> Option<(usize, Instruction)> {
        for (testcase, mut modified_result) in testcases {
            if let (Ok(base_result), Ok(modified_result)) = (&base_result, &mut modified_result) {
                // Replace the modified instruction with the base instruction so that the memory is identical
                modified_result
                    .memory_mut()
                    .get_mut(0)
                    .set_data(&base_result.memory().get(0).2);
            }

            let is_ok = match (&base_result, &modified_result) {
                // We expect the instruction to either execute successfully or fail with a computation error
                // If we see anything else, something has gone horribly wrong during the previous steps.
                // In that case, it's probably best not to try and filter more bits because we can't be too sure
                // about the result.
                (Ok(a), Ok(b)) if a == b => true,
                (Err(OracleError::ComputationError), Err(OracleError::ComputationError)) => true,
                (Err(OracleError::GeneralFault), Err(OracleError::GeneralFault)) => true,
                (Err(OracleError::InstructionFetchMemoryAccess(a)), Err(OracleError::InstructionFetchMemoryAccess(b)))
                    if a == b =>
                {
                    true
                },
                (Err(OracleError::MultipleInstructionsExecuted), _) | (_, Err(OracleError::MultipleInstructionsExecuted)) => {
                    todo!("Multiple instructions executed")
                },
                _ => {
                    warn!(
                        "Found invalid DontCare bits between instruction {:?} and {:?} because of differences for inputs: {:?}; Outputs: {:X?} vs {:X?}",
                        Instruction::new(&base_state.memory().get(0).2),
                        testcase.modified_instr,
                        base_state,
                        base_result,
                        modified_result
                    );
                    false
                },
            };

            if !is_ok {
                return Some((testcase.value, testcase.modified_instr))
            }
        }

        None
    }
}

struct TestCase<A: Arch> {
    value: usize,
    modified_instr: Instruction,
    state: SystemState<A>,
}

impl<A: Arch> AsSystemState<A> for TestCase<A> {
    type Output<'a>
        = &'a SystemState<A>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        &self.state
    }
}
