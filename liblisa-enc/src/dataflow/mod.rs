use std::fmt::Debug;
use std::marker::PhantomData;

use liblisa::arch::{Arch, Register};
use liblisa::encoding::dataflows::{
    AddrTermSize, Dataflow, Dataflows, Dest, Inputs, IntoDestWithSize, IntoSourceWithSize, MemoryAccesses, Size, Source,
};
use liblisa::oracle::Oracle;
use liblisa::state::random::{RandomizationError, StateGen};
use liblisa::state::{StateByte, SystemStateByteView};
use rand::Rng;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use self::analyzer::FlowAnalyzer3;

mod analyzer;
mod flow;
mod fuzz;
mod results;
mod spec;

#[derive(Debug, PartialEq, Copy, Clone, Eq, Hash, PartialOrd, Ord)]
pub struct IsDataflow(pub StateByte, pub StateByte);

/// Error returned when [`DataflowAnalysis`] fails.
#[derive(Error, Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub enum DataflowAnalysisError<A: Arch> {
    #[error("unable to fuzz locations: {:?}", .0)]
    UnableToFuzz(Vec<(String, usize)>),

    #[error("generating states failed: {}", .0)]
    StateGenFailed(RandomizationError),

    #[error("not all bytes are independently modifyable")]
    NotAllBytesAreIndependentlyModifyable,

    #[error("a timeout occurred")]
    Timeout,

    #[error("instructions can fault based on unobservable inputs")]
    Unreliable,

    #[error("multiple instructions were executed")]
    MultipleInstructionsExecuted,

    #[error("the instruction keeps fauting")]
    InstructionKeepsFaulting,

    #[error("TODO: Remove the A generic if we never end up needing it")]
    #[serde(skip)]
    Phantom(PhantomData<A>),
}

/// Infers dataflows given an instruction and its [`MemoryAccesses`](liblisa::encoding::dataflows::MemoryAccesses).
pub struct DataflowAnalysis;

impl DataflowAnalysis {
    pub fn infer<A: Arch, O: Oracle<A>>(
        rng: &mut impl Rng, o: &mut O, memory_accesses: &MemoryAccesses<A>,
    ) -> Result<Dataflows<A, ()>, DataflowAnalysisError<A>> {
        let view = SystemStateByteView::new(memory_accesses);
        let mappable = o.mappable_area();
        let state_gen = StateGen::new(memory_accesses, &mappable).map_err(DataflowAnalysisError::StateGenFailed)?;
        let mut analyzer = FlowAnalyzer3::new(state_gen, view);
        let mut likely_dependent = Vec::new();

        for access in memory_accesses.memory.iter() {
            for (input, term) in access.inputs.iter().zip(access.calculation.terms.iter()) {
                if term.primary.size != AddrTermSize::U64 {
                    continue;
                }

                if let Source::Dest(Dest::Reg(reg, _)) = input {
                    let reg = view.arch_reg_to_reg(*reg);
                    likely_dependent.push(vec![
                        // ARCHITECTURE ASSUMPTION: Memory address size = 64, canonical addresses are 48bits.
                        view.reg_to_byte(reg, 5),
                        view.reg_to_byte(reg, 6),
                        view.reg_to_byte(reg, 7),
                    ])
                }
            }
        }

        for reg in A::iter_gpregs() {
            if reg.is_addr_reg() {
                let reg = view.arch_reg_to_reg(A::reg(reg));
                likely_dependent.push(vec![
                    // ARCHITECTURE ASSUMPTION: Memory address size = 64, canonical addresses are 48bits.
                    view.reg_to_byte(reg, 5),
                    view.reg_to_byte(reg, 6),
                    view.reg_to_byte(reg, 7),
                ])
            }
        }

        likely_dependent.sort();
        likely_dependent.dedup();

        let result = analyzer.run(rng, o, &likely_dependent)?;

        Ok(Dataflows {
            addresses: memory_accesses.clone(),
            outputs: result
                .dataflows
                .into_iter()
                .map(|flow| Dataflow {
                    target: view
                        .to_location(flow.dest.reg)
                        .into_dest_with_size(Size::new(flow.dest.start_byte, flow.dest.end_byte)),
                    inputs: if flow.unobservable_inputs {
                        Inputs::default()
                    } else {
                        Inputs::sorted(
                            flow.sources
                                .into_iter()
                                .map(|source| {
                                    view.to_location(source.reg)
                                        .into_source_with_size(Size::new(source.start_byte, source.end_byte))
                                })
                                .collect(),
                        )
                    },
                    computation: None,
                    unobservable_external_inputs: flow.unobservable_inputs,
                })
                .collect(),
            found_dependent_bytes: result.found_dependent_bytes,
        })
    }
}
