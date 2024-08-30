//! Cache for analysis results.

use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Mutex;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{Dataflows, MemoryAccesses};
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::state::random::StateGen;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::accesses::{AccessAnalysisError, MemoryAccessAnalysis};
use crate::changes::ThresholdValues;
use crate::dataflow::{DataflowAnalysis, DataflowAnalysisError};

/// Generic trait for an encoding analysis cache.
pub trait EncodingAnalysisCache<A: Arch> {
    fn infer_accesses<O: Oracle<A>>(&self, o: &mut O, instr: &Instruction) -> Result<MemoryAccesses<A>, AccessAnalysisError<A>>;
    fn infer_dataflow<O: Oracle<A>>(
        &self, o: &mut O, memory_accesses: &MemoryAccesses<A>,
    ) -> Result<Dataflows<A, ()>, DataflowAnalysisError<A>>;
    fn infer_threshold_values<O: Oracle<A>>(
        &self, o: &mut O, dataflows: &Dataflows<A, ()>, state_gen: &StateGen<'_, A, O::MappableArea>,
    ) -> ThresholdValues<A>;

    fn num_entries(&self) -> usize;
}

/// Generic trait for a cache.
pub trait Cache<T: Clone> {
    fn get_or_insert_with(&self, instr: &Instruction, new: impl FnOnce(&Instruction) -> T) -> T;

    fn num_entries(&self) -> usize;
}

/// A type that never caches results.
pub struct NoCache;

impl<T: Clone> Cache<T> for NoCache {
    fn get_or_insert_with(&self, instr: &Instruction, new: impl FnOnce(&Instruction) -> T) -> T {
        new(instr)
    }

    fn num_entries(&self) -> usize {
        0
    }
}

/// A type that caches results in a [`HashMap`].
pub struct HashMapCache<T: Clone> {
    data: Mutex<HashMap<Instruction, T>>,
}

impl<T: Clone> HashMapCache<T> {
    pub fn new() -> Self {
        HashMapCache {
            data: Mutex::new(HashMap::new()),
        }
    }

    pub fn insert(&self, instruction: Instruction, item: T) {
        let mut lock = self.data.lock().unwrap();

        let prev = lock.insert(instruction, item);
        assert!(prev.is_none());
    }
}

impl<T: Clone> Cache<T> for HashMapCache<T> {
    fn get_or_insert_with(&self, instruction: &Instruction, f: impl FnOnce(&Instruction) -> T) -> T {
        let lock = self.data.lock().unwrap();
        if let Some(result) = lock.get(instruction) {
            result.clone()
        } else {
            drop(lock);
            let new = f(instruction);
            let mut lock = self.data.lock().unwrap();
            lock.insert(*instruction, new.clone());
            new
        }
    }

    fn num_entries(&self) -> usize {
        self.data.lock().unwrap().len()
    }
}

impl<T: Clone> Default for HashMapCache<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Default implementation of [`EncodingAnalysisCache`].
pub struct CombinedCache<A, X, Y, Z> {
    accesses: X,
    dataflow: Y,
    threshold_values: Z,
    _phantom: PhantomData<fn() -> A>,
}

impl<A: Arch, X, Y, Z> CombinedCache<A, X, Y, Z>
where
    X: Cache<MemoryAccessEntry<A>>,
    Y: Cache<DataflowsEntry<A>>,
    Z: Cache<ThresholdValues<A>>,
{
    pub fn new(accesses: X, dataflow: Y, threshold_values: Z) -> Self {
        CombinedCache {
            accesses,
            dataflow,
            threshold_values,
            _phantom: PhantomData,
        }
    }

    pub fn force_infer_dataflow<O: Oracle<A>>(
        &self, o: &mut O, memory_accesses: &MemoryAccesses<A>,
    ) -> Result<Dataflows<A, ()>, DataflowAnalysisError<A>> {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        DataflowAnalysis::infer(&mut rng, o, memory_accesses)
    }
}

impl<A: Arch, X, Y, Z> EncodingAnalysisCache<A> for CombinedCache<A, X, Y, Z>
where
    X: Cache<MemoryAccessEntry<A>>,
    Y: Cache<DataflowsEntry<A>>,
    Z: Cache<ThresholdValues<A>>,
{
    fn infer_accesses<O: Oracle<A>>(&self, o: &mut O, instr: &Instruction) -> Result<MemoryAccesses<A>, AccessAnalysisError<A>> {
        self.accesses
            .get_or_insert_with(instr, |_| MemoryAccessAnalysis::infer(o, instr))
    }

    fn infer_dataflow<O: Oracle<A>>(
        &self, o: &mut O, memory_accesses: &MemoryAccesses<A>,
    ) -> Result<Dataflows<A, ()>, DataflowAnalysisError<A>> {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        self.dataflow.get_or_insert_with(&memory_accesses.instr, |_| {
            DataflowAnalysis::infer(&mut rng, o, memory_accesses)
        })
    }

    fn infer_threshold_values<O: Oracle<A>>(
        &self, o: &mut O, dataflows: &Dataflows<A, ()>, state_gen: &StateGen<'_, A, O::MappableArea>,
    ) -> ThresholdValues<A> {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        self.threshold_values.get_or_insert_with(dataflows.instr(), |_| {
            ThresholdValues::infer(o, &mut rng, state_gen, dataflows)
        })
    }

    fn num_entries(&self) -> usize {
        self.accesses.num_entries() + self.dataflow.num_entries() + self.threshold_values.num_entries()
    }
}

type MemoryAccessEntry<A> = Result<MemoryAccesses<A>, AccessAnalysisError<A>>;
type DataflowsEntry<A> = Result<Dataflows<A, ()>, DataflowAnalysisError<A>>;

impl<A: Arch> Default
    for CombinedCache<A, HashMapCache<MemoryAccessEntry<A>>, HashMapCache<DataflowsEntry<A>>, HashMapCache<ThresholdValues<A>>>
{
    fn default() -> Self {
        Self::new(HashMapCache::new(), HashMapCache::new(), HashMapCache::new())
    }
}
