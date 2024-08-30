use std::marker::PhantomData;

use super::{FallbackBatchObserveIter, Observation, Oracle, OracleError};
use crate::arch::Arch;
use crate::state::{Addr, AsSystemState, SystemState};

/// An oracle that always executes [`Oracle::observe_carefully`].
pub struct CarefulOracle<'o, A: Arch, O: Oracle<A>> {
    oracle: &'o mut O,
    _phantom: PhantomData<A>,
}

impl<'o, A: Arch, O: Oracle<A>> Oracle<A> for CarefulOracle<'o, A, O> {
    type MappableArea = O::MappableArea;

    fn mappable_area(&self) -> Self::MappableArea {
        self.oracle.mappable_area()
    }

    fn page_size(&mut self) -> u64 {
        self.oracle.page_size()
    }

    fn observe(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        match self.oracle.observe(before) {
            Ok(_) => self.observe_carefully(before),
            other => other,
        }
    }

    fn debug_dump(&mut self) {
        self.oracle.debug_dump()
    }

    fn observe_carefully(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        self.oracle.observe_carefully(before)
    }

    fn scan_memory_accesses(&mut self, before: &SystemState<A>) -> Result<Vec<Addr>, OracleError> {
        self.oracle.scan_memory_accesses(before)
    }

    fn restart(&mut self) {
        self.oracle.restart()
    }

    fn kill(self) {
        todo!()
    }

    fn batch_observe_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        FallbackBatchObserveIter::new(self, states.into_iter())
    }

    fn batch_observe_gpreg_only_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        self.batch_observe_iter(states)
    }

    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool = O::UNRELIABLE_INSTRUCTION_FETCH_ERRORS;
}

impl<'a, A: Arch, O: Oracle<A>> CarefulOracle<'a, A, O> {
    /// Wraps `oracle` in a [`CarefulOracle`].
    pub fn new(oracle: &'a mut O) -> Self {
        CarefulOracle {
            oracle,
            _phantom: Default::default(),
        }
    }
}
