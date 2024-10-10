use std::fmt::Debug;
use std::marker::PhantomData;

use super::{Observation, Oracle, OracleError};
use crate::arch::Arch;
use crate::state::{Addr, AsSystemState, SystemState};

/// An oracle that counts how many times it was invoked.
pub struct InvocationCountingOracle<A: Arch, O: Oracle<A>> {
    oracle: O,
    observations: usize,
    _phantom: PhantomData<A>,
}

impl<A: Arch, O: Oracle<A>> Oracle<A> for InvocationCountingOracle<A, O> {
    type MappableArea = O::MappableArea;

    fn mappable_area(&self) -> Self::MappableArea {
        self.oracle.mappable_area()
    }

    fn page_size(&mut self) -> u64 {
        self.oracle.page_size()
    }

    fn observe(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        self.observations += 1;
        self.oracle.observe(before)
    }

    fn debug_dump(&mut self) {
        self.oracle.debug_dump()
    }

    fn scan_memory_accesses(&mut self, before: &SystemState<A>) -> Result<Vec<Addr>, OracleError> {
        self.observations += 1;
        self.oracle.scan_memory_accesses(before)
    }

    fn restart(&mut self) {
        self.oracle.restart()
    }

    fn kill(self) {
        self.oracle.kill()
    }

    fn batch_observe_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        InvocationCounterIter {
            iter: self.oracle.batch_observe_iter(states),
            num_invocations: &mut self.observations,
            _phantom: PhantomData,
        }
    }

    fn batch_observe_gpreg_only_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        InvocationCounterIter {
            iter: self.oracle.batch_observe_gpreg_only_iter(states),
            num_invocations: &mut self.observations,
            _phantom: PhantomData,
        }
    }

    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool = O::UNRELIABLE_INSTRUCTION_FETCH_ERRORS;
}

struct InvocationCounterIter<'a, A: Arch, S, I: Iterator<Item = Observation<S, A>>> {
    iter: I,
    num_invocations: &'a mut usize,
    _phantom: PhantomData<A>,
}

impl<A: Arch, S, I: Iterator<Item = Observation<S, A>>> Iterator for InvocationCounterIter<'_, A, S, I> {
    type Item = Observation<S, A>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(item) => {
                *self.num_invocations += 1;
                Some(item)
            },
            None => None,
        }
    }
}

impl<A: Arch, O: Oracle<A>> Debug for InvocationCountingOracle<A, O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InvocationCountingOracle")
            .field("observations", &self.observations)
            .finish()
    }
}

impl<A: Arch, O: Oracle<A>> InvocationCountingOracle<A, O> {
    /// Wraps `oracle` in an invocation-counting oracle.
    pub fn new(oracle: O) -> Self {
        InvocationCountingOracle {
            oracle,
            observations: 0,
            _phantom: Default::default(),
        }
    }
}
