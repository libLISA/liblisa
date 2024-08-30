use std::marker::PhantomData;

use super::Observation;
use crate::arch::Arch;
use crate::oracle::{FallbackBatchObserveIter, MappableArea, Oracle, OracleError};
use crate::state::{Addr, AsSystemState, SystemState};

/// An oracle that observes execution on two oracles, and panics if the results are not identical.
pub struct VerifyOracle<A: Arch, O1: Oracle<A>, O2: Oracle<A>>(O1, O2, PhantomData<A>);

impl<A: Arch, O1: Oracle<A>, O2: Oracle<A>> VerifyOracle<A, O1, O2> {
    /// Creates a new [`VerifyOracle`], which verifies the observations of `o1` against the observations of `o2`.
    pub fn new(o1: O1, o2: O2) -> VerifyOracle<A, O1, O2> {
        VerifyOracle(o1, o2, PhantomData)
    }
}

#[derive(Clone, Debug)]
pub struct DoubleCheckedMappableArea<A: MappableArea, B: MappableArea>(A, B);

impl<A: MappableArea, B: MappableArea> MappableArea for DoubleCheckedMappableArea<A, B> {
    fn can_map(&self, addr: Addr) -> bool {
        self.0.can_map(addr) && self.1.can_map(addr)
    }
}

impl<A: Arch, O1: Oracle<A>, O2: Oracle<A>> Oracle<A> for VerifyOracle<A, O1, O2> {
    type MappableArea = DoubleCheckedMappableArea<O1::MappableArea, O2::MappableArea>;
    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool =
        O1::UNRELIABLE_INSTRUCTION_FETCH_ERRORS || O2::UNRELIABLE_INSTRUCTION_FETCH_ERRORS;

    fn mappable_area(&self) -> Self::MappableArea {
        DoubleCheckedMappableArea(self.0.mappable_area(), self.1.mappable_area())
    }

    fn page_size(&mut self) -> u64 {
        assert_eq!(self.0.page_size(), self.1.page_size());
        self.0.page_size()
    }

    fn observe(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        use OracleError::*;
        let r1 = self.0.observe(before);
        let r2 = self.1.observe(before);

        assert!(
            match (&r1, &r2) {
                (Ok(a), Ok(b)) if a == b => true,
                (Err(a), Err(b)) => match (a, b) {
                    (MemoryAccess(a), MemoryAccess(b)) if a == b => true,
                    (InvalidInstruction, InvalidInstruction) => true,
                    (GeneralFault, GeneralFault) => true,
                    (ComputationError, ComputationError) => true,
                    _ => false,
                },
                _ => {
                    self.debug_dump();

                    for _ in 0..1000 {
                        let rprime1 = self.0.observe(before);
                        let rprime2 = self.1.observe(before);

                        println!(
                            "Repeating yields: equal={} for first / equal={} for second",
                            rprime1.as_ref().unwrap() == r1.as_ref().unwrap(),
                            rprime2.as_ref().unwrap() == r2.as_ref().unwrap()
                        );
                    }

                    false
                },
            },
            "Observations don't match: {before:X?} results in {r1:X?} vs {r2:X?}"
        );

        r1
    }

    fn scan_memory_accesses(&mut self, before: &SystemState<A>) -> Result<Vec<Addr>, OracleError> {
        let r1 = self.0.scan_memory_accesses(before)?;
        let r2 = self.1.scan_memory_accesses(before)?;

        assert_eq!(r1, r2);
        Ok(r1)
    }

    fn debug_dump(&mut self) {
        println!("First:");
        self.0.debug_dump();

        println!();
        println!("Second:");
        self.1.debug_dump();
    }

    fn restart(&mut self) {
        self.0.restart();
        self.1.restart();
    }

    fn kill(self) {
        self.0.kill();
        self.1.kill();
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
}
