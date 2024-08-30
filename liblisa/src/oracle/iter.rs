use std::marker::PhantomData;

use super::{Observation, Oracle};
use crate::arch::Arch;
use crate::state::AsSystemState;

pub(crate) struct FallbackBatchObserveIter<'a, A: Arch, O: Oracle<A>, S: AsSystemState<A>, I: Iterator<Item = S>> {
    oracle: &'a mut O,
    iter: I,
    _phantom: PhantomData<A>,
}

impl<'a, A: Arch, O: Oracle<A>, S: AsSystemState<A>, I: Iterator<Item = S>> FallbackBatchObserveIter<'a, A, O, S, I> {
    pub fn new(oracle: &'a mut O, iter: I) -> Self {
        FallbackBatchObserveIter {
            oracle,
            iter,
            _phantom: PhantomData,
        }
    }
}

impl<'a, A: Arch, O: Oracle<A>, S: AsSystemState<A>, I: Iterator<Item = S>> Iterator
    for FallbackBatchObserveIter<'a, A, O, S, I>
{
    type Item = Observation<S, A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|item| {
            let result = self.oracle.observe(item.as_system_state().as_ref());
            (item, result)
        })
    }
}
