#![feature(let_chains)]
#![doc(html_no_source)]

//! This library contains libLISA's encoding analysis and some parts of enumeration.
//!
//! # Encoding Analysis
//! Encoding analysis can be invoked as follows:
//!
//! ```
//! use liblisa::arch::x64::X64Arch;
//! use liblisa::instr::Instruction;
//! use liblisa_enc::infer_encoding;
//! use liblisa_x64_observer::with_oracle;
//!
//! let instr = Instruction::new(&[0x90]);
//! let encoding = with_oracle(|mut oracle| infer_encoding(&instr, &mut oracle)).unwrap();
//!
//! println!("{encoding}");
//! ```
//!
//! # Enumeration
//! Two techniques for skipping invalid instructions or errors are implemented: tunneling and randomized search.
//! See [`crate::random_search_skip_invalid_instrs`] and [`tunnel_invalid_instrs`]/[`tunnel_memory_errors`].

mod accesses;
pub mod cache;
mod changes;
mod cleanup;
mod dataflow;
mod encoding;
mod skip;
mod validity;

pub use accesses::{AccessAnalysisError, FindInputError, MemoryAccessAnalysis};
use cache::{CombinedCache, EncodingAnalysisCache};
pub use changes::{Change, ChangeAnalysis, ChangeLocation, JsonThresholdValue, JsonThresholdValues, ThresholdValues};
pub use dataflow::{DataflowAnalysis, DataflowAnalysisError};
pub use encoding::{EncodingAnalysis, EncodingError};
use liblisa::arch::{Arch, Scope};
use liblisa::encoding::Encoding;
use liblisa::instr::{FilterList, Instruction, InstructionCounter, InstructionFilter};
use liblisa::oracle::Oracle;
use log::{error, info, warn};
use rand::prelude::*;
use rand_xoshiro::Xoshiro256PlusPlus;
pub use skip::{random_instr_bytes, random_search_skip_invalid_instrs, tunnel_invalid_instrs, tunnel_memory_errors};
pub use validity::Validity;

/// Error returned by [`infer_encoding`]
#[derive(Clone, Debug, thiserror::Error)]
pub enum InferEncodingError {
    #[error("instruction is too long")]
    TooLong,

    #[error("instruction is too short")]
    TooShort,
}

fn infer_encoding_internal<A: Arch, O: Oracle<A>>(
    instr: &Instruction, cache: &impl EncodingAnalysisCache<A>, oracle: &mut O,
) -> AnalysisResult<A> {
    let validity = Validity::infer(oracle, instr);

    match validity {
        Validity::Ok => match analyze(oracle, cache, instr) {
            Ok(e) => AnalysisResult::Ok(e),
            Err(e) => {
                warn!("Analysis error: {}", e);
                AnalysisResult::SkipError
            },
        },
        Validity::TooShort => AnalysisResult::TooShort,
        Validity::TooLong => AnalysisResult::TooLong,
        Validity::InvalidInstruction | Validity::Error => AnalysisResult::SkipInvalidUntil {
            counter: {
                let mut c = InstructionCounter::range(instr, None);
                c.tunnel_next(&FilterList::new(), 200);
                c
            },
            done: false,
        },
        Validity::Excluded => unreachable!(),
    }
}

/// Infers an [`Encoding`] for the provided [`Instruction`].
pub fn infer_encoding<A: Arch, O: Oracle<A>>(instr: &Instruction, oracle: &mut O) -> Result<Encoding<A, ()>, InferEncodingError> {
    let cache = CombinedCache::default();
    let result = infer_encoding_internal(instr, &cache, oracle);

    match result {
        AnalysisResult::Ok(encoding) => Ok(if let Some(perfect_instr) = encoding.best_instr() {
            info!("Perfect instr: {:X}", perfect_instr);
            let result = infer_encoding_internal(&perfect_instr, &cache, oracle);

            if let AnalysisResult::Ok(best_encoding) = result {
                if best_encoding.filters().iter().any(|f| f.matches(instr)) {
                    best_encoding
                } else {
                    encoding
                }
            } else {
                encoding
            }
        } else {
            info!("No perfect instruction");
            encoding
        }),
        AnalysisResult::TooShort => Err(InferEncodingError::TooShort),
        AnalysisResult::TooLong => Err(InferEncodingError::TooLong),
        _ => todo!("{:?}", result),
    }
}

/// The result of running Encoding Analysis on an [`Instruction`].
#[derive(Debug)]
pub enum AnalysisResult<A: Arch> {
    Ok(Encoding<A, ()>),
    SkipInvalidUntil { counter: InstructionCounter, done: bool },
    SkipMemoryErrorUntil { counter: InstructionCounter, done: bool },
    SkipError,
    TooShort,
    TooLong,
}

impl<A: Arch> AnalysisResult<A> {
    pub fn filters(&self) -> Vec<InstructionFilter> {
        match self {
            AnalysisResult::Ok(e) => e.filters(),
            _ => Vec::new(),
        }
    }

    pub fn run(
        scope: &impl Scope, o: &mut impl Oracle<A>, cache: &impl EncodingAnalysisCache<A>, counter: &InstructionCounter,
        next_filtered_instruction: Option<Instruction>,
    ) -> Self {
        let instr = counter.current();
        let validity = if scope.is_instr_in_scope(instr.bytes()) {
            Validity::infer(o, &instr)
        } else {
            Validity::InvalidInstruction
        };

        if validity != Validity::InvalidInstruction {
            info!("");

            info!("Instruction: {:X} = {:?}", instr, instr);
            info!("   Validity: {}", validity);
        }

        let end = match (next_filtered_instruction, counter.end()) {
            (Some(end), None) | (None, Some(end)) => Some(end),
            (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
            (None, None) => None,
        };

        info!("End: {:?}", end);

        match validity {
            Validity::Ok => match analyze(o, cache, &instr) {
                Ok(encoding) => AnalysisResult::Ok(encoding),
                Err(AnalysisError::AccessAnalysis(e)) => {
                    error!("Analysis failed: {} -- tunneling to next", e);

                    let counter = crate::skip::tunnel_memory_errors(counter.clone(), scope, o, cache);
                    AnalysisResult::SkipMemoryErrorUntil {
                        counter,
                        done: false,
                    }
                },
                Err(e) => {
                    error!("Analysis failed: {}", e);
                    AnalysisResult::SkipError
                },
            },
            Validity::TooShort => AnalysisResult::TooShort,
            Validity::TooLong => AnalysisResult::TooLong,
            Validity::InvalidInstruction | Validity::Excluded | Validity::Error => {
                let instr = counter.current();
                info!(
                    "Tunneling from {:X} no further than {:?}",
                    instr,
                    end.map(|instr| format!("{instr:X}"))
                );

                let mut counter = counter.clone();
                counter.set_end(end);

                let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
                let (_, next_instr) = crate::skip::random_search_skip_invalid_instrs(&mut rng, counter.current(), o, scope);
                if let Some(next_instr) = next_instr {
                    if counter.current() == next_instr {
                        // Something went wrong during analysis. We first saw an invalid instruction, and during the random search it suddenly became valid?
                        counter.tunnel_next(&FilterList::new(), 200);
                    } else {
                        counter.set_current(&next_instr);
                    }
                } else if let Some(end) = counter.end() {
                    counter.set_current(&end);
                }

                counter.set_end(counter.end());
                AnalysisResult::SkipInvalidUntil {
                    counter,
                    done: next_instr.is_none(),
                }
            },
        }
    }
}

/// Wrapper that can contain an [`AccessAnalysisError`], [`DataflowAnalysisError`] or [`EncodingError`].
#[derive(thiserror::Error)]
pub enum AnalysisError<A: Arch> {
    #[error("memory access analysis failed: {}", .0)]
    AccessAnalysis(AccessAnalysisError<A>),

    #[error("dataflow analysis failed: {}", .0)]
    Dataflow(DataflowAnalysisError<A>),

    #[error("encoding analysis failed: {}", .0)]
    Encoding(EncodingError<A>),
}

/// Runs Encoding Analysis on the provided [`Instruction`].
pub fn analyze<A: Arch, O: Oracle<A>>(
    o: &mut O, cache: &impl EncodingAnalysisCache<A>, instr: &Instruction,
) -> Result<Encoding<A, ()>, AnalysisError<A>> {
    let memory_accesses = cache.infer_accesses(o, instr).map_err(|e| {
        error!("MemoryAccesses failed: {}", e);
        AnalysisError::AccessAnalysis(e)
    })?;
    info!("Accesses: {}", memory_accesses);

    let dataflow = cache.infer_dataflow(o, &memory_accesses).map_err(|e| {
        error!("Dataflow failed: {}", e);
        AnalysisError::Dataflow(e)
    })?;
    info!("Dataflow: {:#?}", dataflow);

    let encoding = EncodingAnalysis::infer(o, cache, &dataflow).map_err(|e| {
        error!("Encoding failed: {}", e);
        AnalysisError::Encoding(e)
    })?;
    info!("Encoding: {}", format!("{encoding}").replace('\n', "\n        "));

    Ok(encoding)
}
