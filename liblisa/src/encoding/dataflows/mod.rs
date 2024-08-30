//! Types representing the dataflows in an [`Encoding`](super::Encoding).

use std::fmt::{Debug, Display};
use std::ops::{Index, IndexMut};

use log::trace;
use serde::{Deserialize, Serialize};

use crate::arch::{Arch, Register};
use crate::encoding::bitpattern::{FlowInputLocation, FlowOutputLocation, FlowValueLocation};
use crate::instr::Instruction;
use crate::semantics::{Computation, ARG_NAMES};
use crate::state::{Area, SystemState};
use crate::value::{OwnedValue, Value};

mod accesses;
mod address_computation;
mod inputs;
mod locs;

pub use accesses::*;
pub use address_computation::*;
pub use inputs::*;
pub use locs::*;

/// A collection of dataflows and memory accesses.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema, C: schemars::JsonSchema")
)]
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct Dataflows<A: Arch, C> {
    /// The memory accesses of these dataflows.
    pub addresses: MemoryAccesses<A>,

    /// The outputs of the dataflows.
    pub outputs: Vec<Dataflow<A, C>>,

    /// Whether any dependent bytes were found during Dataflow Analysis.
    pub found_dependent_bytes: bool,
}

fn none<T>() -> Option<T> {
    None
}

/// A single dataflow.
/// Has one target (destination), and zero or more inputs (sources).
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema, C: schemars::JsonSchema")
)]
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct Dataflow<A: Arch, C> {
    /// The storage location in which the result of the computation of this dataflow is saved.
    pub target: Dest<A>,

    /// The sources of the dataflow.
    pub inputs: Inputs<A>,

    /// The computation applied to the inputs to compute the value that is written to `target`.
    #[serde(default = "none::<C>")]
    pub computation: Option<C>,

    /// Whether this dataflow has unobservable external inputs.
    /// If true, `computation` must be `None` and `inputs` should be empty.
    #[serde(default)]
    pub unobservable_external_inputs: bool,
}

impl<A: Arch, C> Dataflow<A, C> {
    /// Returns the inputs of the dataflow.
    #[inline(always)]
    pub fn inputs(&self) -> &Inputs<A> {
        &self.inputs
    }

    /// Returns the storage locatin to which the result of the computation is written.
    #[inline(always)]
    pub fn target(&self) -> &Dest<A> {
        &self.target
    }
}

impl<A: Arch, C> Index<usize> for Dataflows<A, C> {
    type Output = Dataflow<A, C>;

    fn index(&self, index: usize) -> &Dataflow<A, C> {
        &self.outputs[index]
    }
}

impl<A: Arch, C> IndexMut<usize> for Dataflows<A, C> {
    fn index_mut(&mut self, index: usize) -> &mut Dataflow<A, C> {
        &mut self.outputs[index]
    }
}

impl<A: Arch, C> Debug for Dataflow<A, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{:?}] <{}= {{ ",
            self.target,
            if self.unobservable_external_inputs { "*?" } else { "" }
        )?;

        for input in self.inputs.iter() {
            write!(f, "{input:?} ")?;
        }

        write!(f, "}}")?;

        Ok(())
    }
}

impl<A: Arch, C> Dataflows<A, C> {
    /// Returns the instruction for which these dataflow apply.
    pub fn instr(&self) -> &Instruction {
        &self.addresses.instr
    }

    /// Iterates over all dataflows.
    pub fn output_dataflows(&self) -> impl Iterator<Item = &Dataflow<A, C>> {
        self.outputs.iter()
    }

    /// Returns the dataflow at position `index`.
    pub fn output_dataflow(&self, index: usize) -> &Dataflow<A, C> {
        &self.outputs[index]
    }

    fn iter_with_locations(&self) -> impl Iterator<Item = FlowGroup<'_, A>> {
        self.outputs.iter().enumerate().map(|(output_index, output)| FlowGroup {
            inputs: &output.inputs,
            target: Some(&output.target),
            location: FlowOutputLocation::Output(output_index),
        })
    }

    fn inputs(&self) -> impl Iterator<Item = (FlowInputLocation, &Source<A>)> {
        self.iter_with_locations().flat_map(|g| g.iter_with_locations())
    }

    /// Returns all sources in these dataflows.
    pub fn values(&self) -> impl Iterator<Item = (FlowValueLocation, Source<A>)> + '_ {
        self.inputs().map(|(loc, input)| (loc.into(), *input)).chain(
            self.iter_with_locations()
                .map(|g| (g.location(), g.target()))
                .filter_map(|x| match x {
                    (FlowOutputLocation::Output(output_index), Some(dest)) => {
                        Some((FlowValueLocation::Output(output_index), Source::Dest(*dest)))
                    },
                    (FlowOutputLocation::MemoryAccess(_), None) => None,
                    _ => unreachable!(),
                }),
        )
    }

    /// Returns the dataflow with `target` set to `loc`.
    pub fn get(&self, loc: &Dest<A>) -> Option<&Dataflow<A, C>> {
        self.outputs.iter().find(|flow| &flow.target == loc)
    }

    /// Returns the memory areas read or written by these dataflows.
    pub fn extract_memory_areas<'a>(&'a self, state: &'a SystemState<A>) -> impl Iterator<Item = Area> + 'a {
        self.addresses
            .iter()
            .map(|access| Area::new(access.compute_address(state), access.size.end))
    }

    /// Executes the dataflows on `state`, modifying the `state`.
    pub fn execute(&self, state: &mut SystemState<A>)
    where
        C: Computation,
    {
        // TODO: Verify addresses are mapped correctly
        let outputs = self
            .outputs
            .iter()
            .map(|flow| {
                let inputs = flow
                    .inputs
                    .iter()
                    .map(|input| match input {
                        Source::Dest(dest) => state.get_dest(dest),
                        Source::Imm(_) => panic!("No imms should be here"),
                        Source::Const {
                            value, ..
                        } => Value::Num(*value),
                    })
                    .collect::<Vec<_>>();
                let output = flow.computation.as_ref().unwrap().evaluate(&inputs);
                trace!(
                    "{:X?} with {} -> {:X?}",
                    inputs,
                    flow.computation.as_ref().unwrap().display(ARG_NAMES),
                    output
                );
                (flow.target, output)
            })
            .collect::<Vec<_>>();

        for (target, value) in outputs {
            state.set_dest(
                &target,
                &match &value {
                    OwnedValue::Num(n) => Value::Num(*n),
                    OwnedValue::Bytes(b) => Value::Bytes(b),
                },
            );
        }
    }

    /// Maps all computations in the dataflows to new values.
    pub fn map_computations<CNew>(&self, f: impl Fn(&Inputs<A>, &C) -> Option<CNew>) -> Dataflows<A, CNew> {
        let outputs = self
            .outputs
            .iter()
            .map(|flow| Dataflow {
                target: flow.target,
                inputs: flow.inputs.clone(),
                unobservable_external_inputs: flow.unobservable_external_inputs,
                computation: flow.computation.as_ref().and_then(|c| f(&flow.inputs, c)),
            })
            .collect();

        Dataflows {
            addresses: self.addresses.clone(),
            outputs,
            found_dependent_bytes: self.found_dependent_bytes,
        }
    }

    /// Splits flag outputs in the dataflow with position `index` into individual bytes.
    pub fn split_flag_output(&mut self, index: usize) -> usize {
        let output = self.outputs.remove(index);
        let mut num = 0;
        match output.target {
            Dest::Reg(r, size) if r.is_flags() => {
                for byte in size.start_byte..=size.end_byte {
                    let mut inputs = output.inputs.clone();
                    let s = Source::Dest(Dest::Reg(r, Size::new(byte, byte)));
                    if !inputs.contains(&s) {
                        inputs.push(s);
                    }

                    num += 1;
                    self.outputs.push(Dataflow {
                        target: Dest::Reg(r, Size::new(byte, byte)),
                        inputs,
                        unobservable_external_inputs: output.unobservable_external_inputs,
                        computation: None,
                    });
                }
            },
            _ => unimplemented!(),
        }

        num
    }

    /// Maps each source and destination in the dataflows and memory accesses to new values.
    pub fn map(
        &self, instr: Instruction, map_flows: impl Fn(FlowValueLocation, &Source<A>) -> Option<Source<A>>,
        map_address_computations: impl Fn(usize, &AddressComputation) -> Option<AddressComputation>,
    ) -> Dataflows<A, C>
    where
        C: Clone,
    {
        let addresses = self.addresses.map(instr, &map_flows, map_address_computations);
        let outputs = self
            .outputs
            .iter()
            .enumerate()
            .map(|(output_index, flow)| Dataflow {
                target: map_flows(FlowValueLocation::Output(output_index), &Source::Dest(flow.target))
                    .unwrap()
                    .unwrap_dest(),
                inputs: Inputs::unsorted(
                    flow.inputs
                        .iter()
                        .enumerate()
                        .flat_map(|(input_index, input)| {
                            map_flows(
                                FlowValueLocation::InputForOutput {
                                    output_index,
                                    input_index,
                                },
                                input,
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
                unobservable_external_inputs: flow.unobservable_external_inputs,
                computation: flow.computation.clone(),
            })
            .collect::<Vec<_>>();

        Dataflows {
            addresses,
            outputs,
            found_dependent_bytes: self.found_dependent_bytes,
        }
    }

    /// Adds an immediate value to all outputs in `output_indices`.
    /// Returns a list containing the locations of the inserted [`Source::Imm`]s.
    pub fn insert_imm_value(&mut self, output_indices: impl Iterator<Item = usize>, part_index: usize) -> Vec<FlowInputLocation> {
        let mut result = Vec::new();
        for index in output_indices {
            let values = &mut self.outputs[index].inputs;

            result.push(FlowInputLocation::InputForOutput {
                output_index: index,
                input_index: values.len(),
            });
            values.push(Source::Imm(part_index));
        }

        result
    }

    /// Adds an immediate value to all memory accesses and outputs in `locations`.
    /// Returns a list containing the locations of the inserted [`Source::Imm`]s.
    pub fn insert_memory_imms(
        &mut self, locations: &[FlowOutputLocation], offset: i64, part_index: usize,
    ) -> Vec<FlowInputLocation>
    where
        C: Debug,
    {
        let mut result = Vec::new();

        for &location in locations.iter() {
            match location {
                FlowOutputLocation::Output(index) => {
                    let inputs = &mut self.outputs[index].inputs;
                    result.push(location.input(inputs.len()));
                    inputs.push(Source::Imm(part_index));
                },
                FlowOutputLocation::MemoryAccess(index) => {
                    let access = &mut self.addresses[index];
                    assert!(
                        access.inputs.iter().all(|input| !matches!(input, Source::Imm(_))),
                        "Memory access {index} already contains an immediate value: {self:?}"
                    );

                    result.push(FlowInputLocation::MemoryAddress {
                        memory_index: index,
                        input_index: access.inputs.len(),
                    });

                    access.inputs.push(Source::Imm(part_index));
                    access.calculation.offset = access.calculation.offset.wrapping_sub(offset);
                    access.calculation.add_constant_term();
                },
            }
        }

        result
    }

    /// Returns a list of dataflows that overlap with the list provided in `output_dataflows`.
    pub fn overlapping_outputs<'a>(
        &'a self, output_dataflows: &'a [&'a Dataflow<A, C>],
    ) -> impl Iterator<Item = &'a Dataflow<A, C>> {
        self.output_dataflows().filter(|other_output| {
            output_dataflows
                .iter()
                .any(|output_dataflow| other_output.target.overlaps(&output_dataflow.target))
        })
    }
}

#[derive(Debug)]
struct FlowGroup<'a, A: Arch> {
    inputs: &'a Inputs<A>,
    target: Option<&'a Dest<A>>,
    location: FlowOutputLocation,
}

impl<'a, A: Arch> FlowGroup<'a, A> {
    pub fn location(&self) -> FlowOutputLocation {
        self.location
    }

    pub fn iter_with_locations(&self) -> impl Iterator<Item = (FlowInputLocation, &'a Source<A>)> {
        let location = self.location;
        self.inputs
            .iter()
            .enumerate()
            .map(move |(index, el)| (location.input(index), el))
    }

    pub fn target(&self) -> Option<&'a Dest<A>> {
        self.target
    }
}

impl<A: Arch, C: Computation> Display for Dataflows<A, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?} {:02X?}", self.instr(), self.instr().bytes())?;

        for (index, access) in self.addresses.iter().enumerate() {
            write!(
                f,
                "{:10} = ",
                format!(
                    "Addr{}(m{})",
                    match access.kind {
                        AccessKind::Executable => "X ",
                        AccessKind::Input => "R ",
                        AccessKind::InputOutput => "RW",
                    },
                    index
                )
            )?;

            let names = access.inputs.iter().map(|input| format!("{}", input)).collect::<Vec<_>>();

            writeln!(f, "{}", access.calculation.display(&names))?;
        }

        for output in self.output_dataflows() {
            match &output.computation {
                Some(computation) => {
                    let names = output.inputs.iter().map(|input| input.to_string()).collect::<Vec<_>>();

                    writeln!(
                        f,
                        "{:10} := {}",
                        format!("{}", output.target.clone()),
                        computation.display(&names)
                    )?;
                },
                None => {
                    writeln!(f, "{:10} := {}", format!("{}", output.target.clone()), output.inputs)?;
                },
            }
        }

        Ok(())
    }
}
