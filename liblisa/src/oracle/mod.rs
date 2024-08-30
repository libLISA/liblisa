//! Defines the trait [`Oracle`], which represents a CPU observer oracle.

use std::error::Error;
use std::fmt::Debug;

use rand::Rng;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::arch::Arch;
use crate::state::{Addr, AsSystemState, Page, SystemState};
use crate::utils::bitmask_u64;

mod careful;
mod counter;
mod iter;
mod verifier;

pub use careful::CarefulOracle;
pub use counter::InvocationCountingOracle;
pub(crate) use iter::FallbackBatchObserveIter;
pub use verifier::VerifyOracle;

/// Error returned when an error occurs in an [`Oracle`] during instruction observation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Error, Debug, Clone, Serialize, Deserialize)]
pub enum OracleError {
    #[error("Encountered a memory access at {:X}", .0)]
    /// Represents any page fault. Might be an instruction fetch or data fetch.
    MemoryAccess(Addr),

    #[error("Encountered an instruction fetch at {:X}", .0)]
    /// A memory access that occurred while trying to fetch the next instruction.
    /// This is an optimization that is returned if possible by the oracle.
    /// The oracle may fall back to returning a `MemoryAccess` error instead,
    /// if it is not possible to distinguish between instruction fetches and
    /// normal data fetches.
    InstructionFetchMemoryAccess(Addr),

    /// The undefined instruction fault was raised.
    #[error("Invalid instruction")]
    InvalidInstruction,

    /// A general fault was raised.
    #[error("General fault")]
    GeneralFault,

    /// The intruction execution produces different results when executed multiple times.
    #[error("Instruction execution is unreliable: executing multiple times with the same state gives different results")]
    Unreliable,

    /// A computation error fault or exception was raised. For example: dividing by zero.
    #[error("A computation error occurred")]
    ComputationError,

    /// Observation timeout occurred.
    #[error("The observation timed out")]
    Timeout,

    /// Instruction execution did not halt after executing a single instruction.
    /// This makes it impossible to observe the instruction execution.
    #[error("Multiple instructions were executed")]
    MultipleInstructionsExecuted,

    /// An API error occurred.
    #[error("Oracle failed with {}", .0)]
    ApiError(String),
}

impl OracleError {
    /// Creates an API error.
    pub fn api<E: Error + Send + Sync + 'static>(e: E) -> Self {
        OracleError::ApiError(e.to_string())
    }
}

/// The result of an observation.
pub type ObservationResult<A> = Result<SystemState<A>, OracleError>;

/// A tuple of `(state_in, state_out)` representing an input to the observation and the observed output.
pub type Observation<S, A> = (S, ObservationResult<A>);

/// The memory addresses that can be mapped by an oracle.
pub trait MappableArea: Clone + Debug {
    /// Returns true if the address `addr` can be mapped.
    fn can_map(&self, addr: Addr) -> bool;
}

/// Provides oracles.
pub trait OracleSource {
    /// The type of the oracle this source can provide.
    type Oracle;

    /// Starts one or more new oracles.
    /// Only starts multiple oracles if this is as efficent as starting a single.
    ///
    /// For example, the x86-64 oracle uses a 2:1 mapping of 2 shared memory queues on the host going to the same observation VM.
    /// This means that any time a VM is started, two new oracles are available.
    fn start(&self) -> Vec<Self::Oracle>;
}

/// An oracle that can observe instruction execution.
pub trait Oracle<A: Arch> {
    /// The memory addresses that can be mapped by this oracle.
    type MappableArea: MappableArea;

    /// Set to true if the instruction fetch errors are unreliable.
    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool;

    /// Returns the memory addresses that can be mapped by this oracle.
    fn mappable_area(&self) -> Self::MappableArea;

    /// Returns a random mappable page.
    fn random_mappable_page(&self, rng: &mut impl Rng) -> Page<A> {
        let mappable = self.mappable_area();
        loop {
            let addr = Addr::new(rng.gen::<u64>() & !bitmask_u64(A::PAGE_BITS as u32));
            if mappable.can_map(addr) {
                return addr.page::<A>()
            }
        }
    }

    /// Returns the page size of the oracle.
    fn page_size(&mut self) -> u64;

    /// Observes the output state after executing a single instruction in the `before` state.
    fn observe(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError>;

    /// Performs many observations in one go.
    /// Behaves idential to [`Self::observe`], but is much more efficient.
    fn batch_observe_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>>;

    /// Performs many observations in one go.
    /// Only reads and writes the general-purpose registers.
    /// Other registers may have arbitrary values.
    fn batch_observe_gpreg_only_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>>;

    /// Observes the output state after executing a single instruction in the `before` state.
    /// If possible, uses debugging registers to exhaustively check the exact memory locations that are accessed.
    /// Returns a memory access error if a memory is accessed that is not set in `before`.
    ///
    /// [`Self::observe`] may not return the proper memory access error if a memory access occurs outside the areas mapped in `before`,
    /// but on the same page as a mapped area.
    fn observe_carefully(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        let result = self.observe(before)?;
        let mut accesses = self.scan_memory_accesses(before)?;

        // Keep only the accesses outside the mapped areas
        accesses.retain(|&found_addr| {
            before
                .memory()
                .iter()
                .all(|(mapped_addr, _, data)| !mapped_addr.into_area(data.len() as u64).contains(found_addr))
        });

        if !accesses.is_empty() {
            Err(OracleError::MemoryAccess(accesses[0]))
        } else {
            Ok(result)
        }
    }

    /// Performs many observations in one go.
    /// Behaves idential to [`Self::observe`], but is much more efficient.
    fn batch_observe<'a, const N: usize, S: AsSystemState<A> + 'a>(&mut self, states: [S; N]) -> [Observation<S, A>; N] {
        let mut iter = self.batch_observe_iter(<[S; N] as IntoIterator>::into_iter(states));
        [(); N].map(|_| iter.next().unwrap())
    }

    /// Uses debugging registers to determine all memory addresses accessed by the instruction.
    /// If this is not supported, returns an empty `Vec`.
    fn scan_memory_accesses(&mut self, before: &SystemState<A>) -> Result<Vec<Addr>, OracleError>;

    /// Prints debugging information about the oracle.
    fn debug_dump(&mut self);

    /// Restart the oracle, if possible.
    fn restart(&mut self);

    /// Kills the oracle, if possible.
    fn kill(self);
}
