use std::fmt::Debug;

use liblisa::encoding::bitpattern::{FlowInputLocation, FlowOutputLocation, FlowValueLocation};
use liblisa::encoding::dataflows::{AddressComputation, Dataflows};
use liblisa::state::random::{RandomizationError, StateGen};
use log::{error, info, warn};
use serde::{Deserialize, Serialize};

use super::*;
use crate::accesses::{AccessAnalysisError, FindInputError};
use crate::dataflow::DataflowAnalysis;
use crate::validity::Validity;

mod addrs;
mod imm;
mod inputs;
mod outputs;

pub(crate) use addrs::find_memory_access_imm;
pub use imm::{JsonThresholdValue, JsonThresholdValues, ThresholdValues};
pub(crate) use inputs::DataflowChange;

/// The location in the [`Dataflows`](liblisa::encoding::dataflows::Dataflows) where a change occurred.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ChangeLocation {
    Output(usize),
    InputForOutput { output_index: usize, input_index: usize },
    MemoryAddress { memory_index: usize, input_index: usize },
}

impl ChangeLocation {
    pub fn is_input(&self) -> bool {
        matches!(
            self,
            ChangeLocation::InputForOutput {
                output_index: _,
                input_index: _
            }
        )
    }

    pub fn into_output(self) -> ChangeLocation {
        match self {
            ChangeLocation::Output(n) => ChangeLocation::Output(n),
            ChangeLocation::InputForOutput {
                output_index, ..
            } => ChangeLocation::Output(output_index),
            ChangeLocation::MemoryAddress {
                ..
            } => panic!("Memory addresses do not have an output"),
        }
    }
}

impl From<FlowInputLocation> for ChangeLocation {
    fn from(location: FlowInputLocation) -> Self {
        match location {
            FlowInputLocation::InputForOutput {
                output_index,
                input_index,
            } => ChangeLocation::InputForOutput {
                output_index,
                input_index,
            },
            FlowInputLocation::MemoryAddress {
                memory_index,
                input_index,
            } => ChangeLocation::MemoryAddress {
                memory_index,
                input_index,
            },
        }
    }
}

impl From<ChangeLocation> for FlowValueLocation {
    fn from(location: ChangeLocation) -> Self {
        match location {
            ChangeLocation::Output(index) => FlowValueLocation::Output(index),
            ChangeLocation::InputForOutput {
                output_index,
                input_index,
            } => FlowValueLocation::InputForOutput {
                output_index,
                input_index,
            },
            ChangeLocation::MemoryAddress {
                memory_index,
                input_index,
            } => FlowValueLocation::MemoryAddress {
                memory_index,
                input_index,
            },
        }
    }
}

impl From<&ChangeLocation> for FlowValueLocation {
    fn from(location: &ChangeLocation) -> Self {
        (*location).into()
    }
}

/// A difference between two [`Dataflows`](liblisa::encoding::dataflows::Dataflows).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Change<A: Arch> {
    None,
    Invalid,
    Error,
    UnknownMemoryError {
        access_index: usize,
    },
    Register {
        locations: Vec<ChangeLocation>,
        from: A::Reg,
        to: A::Reg,
    },
    Multiple(Vec<Change<A>>),
    ValueImm {
        output_indexes: Vec<usize>,
    },
    MemoryOffset {
        locations: Vec<FlowOutputLocation>,
        offset: i64,
        decreasing: bool,
        bit_indexes: Vec<usize>,
        guessed: bool,
    },
    MemoryComputation {
        memory_indexes: Vec<usize>,
        from: AddressComputation,
        to: AddressComputation,
    },
}

impl<A: Arch> Change<A> {
    pub fn is_invalid_or_error(&self) -> bool {
        matches!(self, Change::Invalid | Change::Error)
    }

    pub(crate) fn as_base(&self) -> ChangeBase<A> {
        match self {
            Change::None => ChangeBase::None,
            Change::Invalid | Change::Error => ChangeBase::Invalid,
            Change::UnknownMemoryError {
                access_index,
            } => ChangeBase::UnknownMemoryError {
                access_index: *access_index,
            },
            Change::Register {
                locations,
                from,
                to: _,
            } => ChangeBase::Register {
                locations,
                from: *from,
            },
            Change::ValueImm {
                output_indexes,
            } => ChangeBase::ValueImm {
                output_indexes,
            },
            Change::MemoryOffset {
                locations: memory_indexes,
                ..
            } => ChangeBase::MemoryOffset {
                memory_indexes,
            },
            Change::MemoryComputation {
                memory_indexes,
                from,
                ..
            } => ChangeBase::MemoryComputation {
                memory_indexes,
                from: *from,
            },
            Change::Multiple(_) => panic!("Do not call as_base() on Change::Multiple"),
        }
    }

    pub fn normalize(&mut self) {
        if let Change::Multiple(items) = self {
            items.retain(|item| !item.is_invalid_or_error());
            if items.is_empty() {
                *self = Change::Invalid
            } else if items.len() == 1 {
                *self = items.remove(0)
            }
        }
    }

    pub fn sort(&mut self) {
        match self {
            Change::Register {
                locations, ..
            } => locations.sort(),
            Change::ValueImm {
                output_indexes,
            } => output_indexes.sort(),
            Change::MemoryOffset {
                locations: memory_indexes,
                ..
            } => memory_indexes.sort(),
            Change::MemoryComputation {
                memory_indexes, ..
            } => memory_indexes.sort(),
            Change::Multiple(items) => {
                for item in items.iter_mut() {
                    item.sort()
                }
            },
            _ => {},
        }
    }

    pub fn combine(self, other: Change<A>) -> Change<A> {
        match (self, other) {
            (Change::None, other) | (other, Change::None) => other,
            (Change::Error, _) | (_, Change::Error) => Change::Error,
            (
                Change::UnknownMemoryError {
                    access_index: a,
                },
                Change::UnknownMemoryError {
                    access_index: b,
                },
            ) if a == b => Change::UnknownMemoryError {
                access_index: a,
            },
            (
                Change::Register {
                    locations: locations_a,
                    from: from_a,
                    to: to_a,
                },
                Change::Register {
                    locations: locations_b,
                    from: from_b,
                    to: to_b,
                },
            ) if from_a == from_b && to_a == to_b => {
                let mut locations = locations_a;
                locations.extend(locations_b);
                Change::Register {
                    locations,
                    from: from_a,
                    to: to_a,
                }
            },
            (Change::Multiple(a), Change::Multiple(b)) => {
                let mut result = Change::Multiple(
                    a.iter()
                        .flat_map(|a| b.iter().cloned().map(|b| a.clone().combine(b)))
                        .collect(),
                );
                result.normalize();
                result
            },
            (Change::Multiple(a), other) => Change::Multiple(a.into_iter().map(|item| other.clone().combine(item)).collect()),
            (
                Change::ValueImm {
                    output_indexes: a,
                },
                Change::ValueImm {
                    output_indexes: b,
                },
            ) => {
                let mut output_indexes = a;
                output_indexes.extend(b);
                Change::ValueImm {
                    output_indexes,
                }
            },
            (
                Change::MemoryOffset {
                    locations: memory_indexes_a,
                    offset: offset_a,
                    decreasing: decreasing_a,
                    bit_indexes: bit_indexes_a,
                    guessed: guessed_a,
                },
                Change::MemoryOffset {
                    locations: memory_indexes_b,
                    offset: offset_b,
                    decreasing: decreasing_b,
                    bit_indexes: bit_indexes_b,
                    guessed: guessed_b,
                },
            ) if offset_a == offset_b && decreasing_a == decreasing_b && bit_indexes_a == bit_indexes_b => {
                let mut memory_indexes = memory_indexes_a;
                memory_indexes.extend(memory_indexes_b);
                Change::MemoryOffset {
                    locations: memory_indexes,
                    offset: offset_a,
                    decreasing: decreasing_a,
                    bit_indexes: bit_indexes_a,
                    guessed: guessed_a && guessed_b,
                }
            },
            (
                Change::MemoryComputation {
                    memory_indexes: memory_indexes_a,
                    from: from_a,
                    to: to_a,
                },
                Change::MemoryComputation {
                    memory_indexes: memory_indexes_b,
                    from: from_b,
                    to: to_b,
                },
            ) if from_a == from_b && to_a == to_b => {
                let mut memory_indexes = memory_indexes_a;
                memory_indexes.extend(memory_indexes_b);
                Change::MemoryComputation {
                    memory_indexes,
                    from: from_a,
                    to: to_a,
                }
            },
            _ => Change::Invalid,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ChangeBase<'a, A: Arch> {
    None,
    Invalid,
    UnknownMemoryError {
        access_index: usize,
    },
    Register {
        locations: &'a [ChangeLocation],
        from: A::Reg,
    },
    ValueImm {
        output_indexes: &'a [usize],
    },
    MemoryOffset {
        memory_indexes: &'a [FlowOutputLocation],
    },
    MemoryComputation {
        memory_indexes: &'a [usize],
        from: AddressComputation,
    },
}

/// Determines [`Change`]s between the dataflows of two instructions.
pub struct ChangeAnalysis<'a, A: Arch, O: Oracle<A>, C: EncodingAnalysisCache<A>> {
    pub o: &'a mut O,
    pub cache: &'a C,
    pub dataflows: &'a Dataflows<A, ()>,
    pub state_gen: StateGen<'a, A, O::MappableArea>,
    pub use_trap_flag: &'a mut bool,
    pub threshold_values: &'a ThresholdValues<A>,
    pub found_dependent_bytes: &'a mut bool,
}

impl<A: Arch, O: Oracle<A>, C: EncodingAnalysisCache<A>> ChangeAnalysis<'_, A, O, C> {
    pub fn detect_change<R: Rng>(&mut self, rng: &mut R, new_instr: &Instruction) -> Result<Change<A>, EncodingError<A>> {
        Ok(match Validity::infer(self.o, new_instr) {
            v
            @ (Validity::TooShort | Validity::InvalidInstruction | Validity::TooLong | Validity::Excluded | Validity::Error) => {
                info!("Validity check failed: {:?}", v);
                Change::Invalid
            },
            Validity::Ok => {
                let new_memory_accesses = self.cache.infer_accesses(self.o, new_instr);
                info!("New memory accesses: {:X?}", new_memory_accesses);
                match new_memory_accesses {
                    Ok(new_memory_accesses) => {
                        *self.use_trap_flag |= new_memory_accesses.use_trap_flag;

                        let mappable = self.o.mappable_area();
                        let new_state_gen = StateGen::new(&new_memory_accesses, &mappable)?;
                        let changes = DataflowChange::compare_memory_accesses(&self.dataflows.addresses, &new_memory_accesses);
                        let memory_change = DataflowChange::into_change(changes);
                        info!("Change after comparing memory accesses: {:?}", memory_change);
                        if memory_change.is_invalid_or_error() {
                            return Ok(memory_change);
                        }

                        let memory_change =
                            addrs::find_memory_access_imm(&self.dataflows.addresses, &new_memory_accesses, memory_change);
                        info!("Change after checking for memory access imm: {:?}", memory_change);
                        if memory_change.is_invalid_or_error() {
                            return Ok(memory_change);
                        }

                        match self.cache.infer_dataflow(self.o, &new_memory_accesses) {
                            Ok(new_dataflows) => {
                                info!("New dataflow: {:#X?}", new_dataflows);

                                let is_memory_offset = matches!(memory_change, Change::MemoryOffset { .. });

                                let changes = DataflowChange::compare_dataflows(self.dataflows, &new_dataflows);
                                let dataflow_change = DataflowChange::into_change(changes);
                                let change = memory_change.clone().combine(dataflow_change);
                                info!("Changes after comparing dataflow: {:?}", change);
                                let change = if change.is_invalid_or_error() {
                                    if is_memory_offset {
                                        info!("Retrying to try and get proper MemoryImm");
                                        match DataflowAnalysis::infer(rng, self.o, &new_memory_accesses) {
                                            Ok(new_dataflows) => {
                                                let changes = DataflowChange::compare_dataflows(self.dataflows, &new_dataflows);
                                                let dataflow_change = DataflowChange::into_change(changes);
                                                let change = memory_change.combine(dataflow_change);

                                                if !change.is_invalid_or_error() {
                                                    change
                                                } else {
                                                    return Ok(change);
                                                }
                                            },
                                            Err(_) => return Ok(change),
                                        }
                                    } else {
                                        return Ok(change);
                                    }
                                } else {
                                    change
                                };

                                let change = match (imm::ImmAnalysis {
                                    dataflows: self.dataflows,
                                    state_gen: &self.state_gen,
                                    o: self.o,
                                })
                                .find_dataflow_imm(
                                    rng,
                                    &new_state_gen,
                                    &new_dataflows,
                                    self.threshold_values,
                                    change,
                                ) {
                                    Ok(change) => change,
                                    Err(e) => {
                                        error!("Error while searching for dataflow imms: {}", e);
                                        return Ok(Change::Error);
                                    },
                                };

                                let mut change = change;
                                change.normalize();

                                info!("Changes finding dataflow imm: {:?}", change);
                                change
                            },
                            Err(e) => {
                                warn!("Inferring dataflow failed: {}", e);
                                Change::Error
                            },
                        }
                    },
                    Err(AccessAnalysisError::Randomization(RandomizationError::UnmappableFixedOffset(access_index)))
                    | Err(AccessAnalysisError::Randomization(RandomizationError::Unsatisfiable(access_index)))
                    | Err(AccessAnalysisError::UnaccessibleMemoryAccess(access_index))
                    | Err(AccessAnalysisError::AccessNotAnalyzable(access_index))
                    | Err(AccessAnalysisError::FindInputFailed(access_index, FindInputError::UnobservableExternalInputs)) => {
                        // When access analysis fails, we might still want to consider the bit a MemoryImm.
                        // It might for example be the highest bit in a fixed memory address, making the address negative and unmappable from userspace.
                        // We might merge this bit into a parts later on, if they're located between other MemoryImm bits.
                        Change::UnknownMemoryError {
                            access_index,
                        }
                    },
                    Err(e) => {
                        warn!("detect_change failed with error: {}", e);
                        Change::Error
                    },
                }
            },
        })
    }
}
