use std::collections::HashSet;
use std::fmt::Debug;
use std::iter::once;

use arrayvec::ArrayVec;
use liblisa::arch::{Arch, Register};
use liblisa::encoding::bitpattern::{FlowInputLocation, MappingOrBitOrder, PartMapping, PartValue};
use liblisa::encoding::dataflows::{Dataflows, Dest, Source};
use liblisa::encoding::Encoding;
use liblisa::oracle::{Oracle, OracleError};
use liblisa::semantics::IoType;
use liblisa::state::random::{RandomizationError, StateGen};
use liblisa::state::SystemState;
use liblisa::value::{AsValue, OwnedValue, Value, ValueType};
use log::{debug, trace};

use crate::Requester;

/// A synthesis output. Corresponds to a dataflow output in an [`Encoding`].
#[derive(Debug, Clone)]
pub struct Output<'a, A: Arch> {
    pub output_index: usize,
    pub num_inputs: usize,
    pub fixed_instantiation_choices: Vec<Option<u64>>,
    pub encoding: &'a Encoding<A, ()>,
}

impl<'a, A: Arch> Output<'a, A> {
    pub fn extract_from_encoding(encoding: &'a Encoding<A, ()>) -> Vec<Self> {
        encoding.dataflows.output_dataflows().enumerate().map(move |(output_index, output)| {
            Output {
                encoding,
                output_index,
                num_inputs: output.inputs.len(),
                fixed_instantiation_choices: encoding.find_best_reg_choices(true, |choices| {
                    match encoding.instantiate(choices) {
                        Ok(dataflows) => {
                            let dataflow = dataflows.output_dataflow(output_index);
                            let others = dataflows.output_dataflows().enumerate()
                                .filter(|(index, _)| *index != output_index)
                                .map(|(_, v)| v)
                                .collect::<Vec<_>>();
                            // Priority 1: Map all inputs to a different register
                            let registers = match dataflow.target() {
                                Dest::Reg(reg, _) => once(Some(reg)),
                                _ => once(None),
                            }.chain(dataflow.inputs.iter().map(|input| match input {
                                Source::Dest(Dest::Reg(reg, _)) => Some(reg),
                                _ => None,
                            })).flatten().collect::<Vec<_>>();
                            let registers_hashset = registers.iter().collect::<HashSet<_>>();

                            // Priority 2: Use registers that don't overlap with any other dataflow
                            let overlapping = others.iter().map(|flow| {
                                let s = match flow.target() {
                                    Dest::Reg(reg, _) if registers_hashset.contains(&reg) => 1,
                                    _ => 0,
                                };

                                s + dataflow.inputs.iter().filter(|input| matches!(input, Source::Dest(Dest::Reg(reg, _)) if registers_hashset.contains(&reg))).count()
                            }).sum::<usize>();

                            let overlapping_with_addr_regs = dataflows.addresses.iter()
                                .flat_map(|addr| addr.inputs.iter())
                                .filter(|input| matches!(input, Source::Dest(Dest::Reg(reg, _)) if registers_hashset.contains(&reg)))
                                .count();

                            (registers.len() - registers_hashset.len()) * 1_000 + overlapping_with_addr_regs * 100 + overlapping
                        },
                        Err(_) => 999_999,
                    }
                }).unwrap_or_else(|| encoding.parts.iter().map(|_| None).collect()),
            }
        }).collect::<Vec<_>>()
    }
}

#[derive(thiserror::Error, Debug)]
pub enum EvaluationError {
    #[error("Randomization of the base state failed: {}", .0)]
    RandomizeFailed(RandomizationError),

    #[error("This evaluation involves a storage location that has not been implemented")]
    NotImplemented,

    #[error("Encountered an error while observing: {}", .0)]
    OracleError(OracleError),

    #[error("Memory size too big")]
    MemorySizeTooBig,

    #[error("Adapt failed")]
    AdaptFailed,

    #[error("Cannot change the value of the zero register to a non-zero value")]
    CannotSetZeroReg,

    #[error("Generic error (TODO: Error specialization)")]
    Generic,
}

pub fn extract_io<'i, 'o, A: Arch>(
    output_index: usize, instance: &Dataflows<A, ()>, state_in: &'i SystemState<A>, part_values: &[u64],
    state_out: &'o SystemState<A>,
) -> (ArrayVec<Value<'i>, 32>, Value<'o>) {
    let dataflow = instance.output_dataflow(output_index);
    let inputs = dataflow
        .inputs
        .iter()
        .map(|item| match item {
            Source::Dest(d) => state_in.get_dest(d),
            Source::Imm(index) => Value::Num(part_values[*index]),
            Source::Const {
                value,
                num_bits,
            } => Value::Num(*value & ((1 << num_bits) - 1)),
        })
        .collect();

    let output = state_out.get_dest(dataflow.target());
    (inputs, output)
}

impl<A: Arch> Output<'_, A> {
    pub fn evaluate_once_internal<const DEBUG: bool, V: AsValue, O: Oracle<A>>(
        &self, oracle: &mut O, inputs: &[V],
    ) -> Result<OwnedValue, EvaluationError> {
        // TODO: The OracleRequester instantiates new dataflows on its own, which is very slow.
        // TODO: Can we either speed it up, or re-use the instantiated dataflows we already have (instance)?
        let mut rng = rand::thread_rng();
        let final_instantiations = self
            .encoding
            .parts
            .iter()
            .zip(self.fixed_instantiation_choices.iter())
            .map(|(part, fixed_choice)| {
                Ok(match fixed_choice {
                    Some(val) => *val,
                    None => match &part.mapping {
                        // TODO: Is this correct? Let's double-check that this makes correct observations...
                        PartMapping::Imm {
                            locations,
                            mapping,
                            ..
                        } => {
                            match locations.iter().find(|loc| match loc {
                                FlowInputLocation::InputForOutput {
                                    output_index, ..
                                } => *output_index == self.output_index,
                                FlowInputLocation::MemoryAddress {
                                    ..
                                } => false,
                            }) {
                                Some(FlowInputLocation::InputForOutput {
                                    input_index, ..
                                })
                                | Some(FlowInputLocation::MemoryAddress {
                                    input_index, ..
                                }) => {
                                    let new_value = inputs[*input_index].unwrap_num();
                                    match mapping {
                                        Some(MappingOrBitOrder::Mapping(mapping)) => {
                                            if mapping.get(new_value as usize) == Some(&PartValue::Valid) {
                                                new_value
                                            } else {
                                                return Err(EvaluationError::Generic);
                                            }
                                        },
                                        _ => new_value, // TODO: We need to reverse-apply the bitordering here...
                                    }
                                },
                                _ => part.value,
                            }
                        },
                        _ => part.value,
                    },
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let dataflows = self
            .encoding
            .instantiate(&final_instantiations)
            .unwrap_or_else(|_| panic!("Failed to instantiate with {:X?}: {}", final_instantiations, self.encoding));
        let dataflow = dataflows.output_dataflow(self.output_index);

        if DEBUG {
            println!("Evaluating {dataflow:?} in {dataflows} with inputs {inputs:X?}");
        }

        debug!("Evaluating {inputs:X?}");
        debug!("Instantiated dataflows: {dataflows:?}");
        debug!("We are interested in: {dataflow:?}");

        let mappable = oracle.mappable_area();
        let state_gen = StateGen::new(&dataflows.addresses, &mappable).map_err(EvaluationError::RandomizeFailed)?;
        let mut base = state_gen.randomize_new(&mut rng).map_err(EvaluationError::RandomizeFailed)?;
        for (input, value) in dataflow.inputs.iter().zip(inputs.iter()) {
            if DEBUG {
                println!("{input:?} = {value:X?}");
            }

            match input {
                Source::Dest(Dest::Reg(reg, _)) if reg.is_zero() => {
                    if value.unwrap_num() != 0 {
                        return Err(EvaluationError::CannotSetZeroReg);
                    }
                },
                Source::Dest(dest) => {
                    base.set_dest(dest, &value.as_value());
                },
                Source::Imm(_)
                | Source::Const {
                    ..
                } => (), // We have already instantiated the instruction with this immediate value
            }
        }

        if !state_gen.adapt(&mut base, false) {
            if DEBUG {
                println!("Adapt failed for: {base:?}");
            }

            trace!("Unable to adapt {:?}", base);
            return Err(EvaluationError::AdaptFailed);
        }

        if DEBUG {
            println!("Prepared state: {base:X?}");
        }

        debug!("Observing via: {base:X?}");

        let result = oracle.observe(&base).map_err(EvaluationError::OracleError)?;

        if DEBUG {
            println!("Observation result: {result:X?}");
        }

        debug!("Result (reading {:?}): {result:X?}", dataflow.target());

        let value = result.get_dest(dataflow.target()).to_owned_value();

        if DEBUG {
            println!("{:?} = {value:X?}", dataflow.target());
        }

        Ok(value)
    }

    // TODO: Split fixed instantiation from rest of code, add case generation from observations.
    pub fn evaluate_once<V: AsValue, O: Oracle<A>>(&self, oracle: &mut O, inputs: &[V]) -> Result<OwnedValue, EvaluationError> {
        self.evaluate_once_internal::<false, _, _>(oracle, inputs)
    }

    pub fn evaluate_debug<V: AsValue, O: Oracle<A>>(&self, oracle: &mut O, inputs: &[V]) -> Result<OwnedValue, EvaluationError> {
        self.evaluate_once_internal::<true, _, _>(oracle, inputs)
    }

    /// Runs evaluate_once multiple times, to hopefully filter out the occasional error because of (for example) remapping.
    pub fn evaluate<V: AsValue, O: Oracle<A>>(&self, oracle: &mut O, inputs: &[V]) -> Result<OwnedValue, EvaluationError> {
        for _ in 0..10 {
            if let Ok(result) = self.evaluate_once(oracle, inputs) {
                return Ok(result)
            }
        }

        self.evaluate_once(oracle, inputs)
    }

    pub fn extract_io<'i, 'o>(
        &self, instance: &Dataflows<A, ()>, state_in: &'i SystemState<A>, part_values: &[u64], state_out: &'o SystemState<A>,
    ) -> (ArrayVec<Value<'i>, 32>, Value<'o>) {
        extract_io(self.output_index, instance, state_in, part_values, state_out)
    }

    fn dest_to_iotype(&self, dest: &Dest<A>) -> IoType {
        match dest {
            Dest::Mem(_, size) => IoType::Bytes {
                num_bytes: size.num_bytes(),
            },
            Dest::Reg(reg, size) => {
                if reg.reg_type() == ValueType::Num {
                    let num_bits = if let Some(mask) = reg.mask()
                        && size.num_bytes() == 1
                    {
                        let mask = (mask >> (size.start_byte * 8)) as u8;
                        (8 - mask.leading_zeros()) as usize
                    } else {
                        size.num_bytes() * 8
                    };

                    IoType::Integer {
                        num_bits,
                    }
                } else {
                    IoType::Bytes {
                        num_bytes: size.num_bytes(),
                    }
                }
            },
        }
    }

    pub fn input_types(&self) -> Vec<IoType> {
        let final_instantiations = self.encoding.parts.iter().map(|part| part.value).collect::<Vec<_>>();
        let dataflows = self.encoding.instantiate(&final_instantiations).unwrap(); // TODO: handle error
        let flow = dataflows.output_dataflow(self.output_index);
        flow.inputs
            .iter()
            .map(|s| match s {
                Source::Imm(n) => {
                    if *n >= self.encoding.parts.len() {
                        panic!("Invalid encoding: {}", self.encoding);
                    }

                    IoType::Integer {
                        num_bits: self.encoding.parts[*n].size,
                    }
                },
                Source::Const {
                    num_bits, ..
                } => IoType::Integer {
                    num_bits: *num_bits,
                },
                Source::Dest(dest) => self.dest_to_iotype(dest),
            })
            .collect::<Vec<_>>()
    }

    pub fn output_type(&self) -> IoType {
        // TODO: Do we need to instantiate for this?
        let final_instantiations = self.encoding.parts.iter().map(|part| part.value).collect::<Vec<_>>();
        let dataflows = self.encoding.instantiate(&final_instantiations).unwrap(); // TODO: handle error
        let flow = dataflows.output_dataflow(self.output_index);

        self.dest_to_iotype(flow.target())
    }

    pub fn dest(&self) -> Dest<A> {
        *self.encoding.dataflows.output_dataflow(self.output_index).target()
    }
}

pub struct OracleRequester<'a, 'o, A: Arch, O: Oracle<A>> {
    pub(crate) output: &'a mut Output<'o, A>,
    pub(crate) oracle: &'a mut O,
}

impl<A: Arch, O: Oracle<A>> Requester<OwnedValue> for OracleRequester<'_, '_, A, O> {
    fn request<V: AsValue>(&mut self, inputs: &[V]) -> Option<OwnedValue> {
        self.output.evaluate(self.oracle, inputs).ok()
    }

    fn request_debug<V: AsValue>(&mut self, inputs: &[V]) -> Option<OwnedValue> {
        let result = self.output.evaluate_debug(self.oracle, inputs);

        println!("Final evaluation result: {result:X?}");

        result.ok()
    }
}
