use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use liblisa::arch::Arch;
use liblisa::oracle::{Observation, Oracle, OracleError, OracleSource};
use liblisa::state::{Addr, AsSystemState, SystemState};

pub struct PooledOracle<O> {
    source_id: u64,
    oracle: O,
}

impl<A: Arch, O: Oracle<A>> Oracle<A> for PooledOracle<O> {
    type MappableArea = <O as Oracle<A>>::MappableArea;

    fn mappable_area(&self) -> Self::MappableArea {
        self.oracle.mappable_area()
    }

    fn page_size(&mut self) -> u64 {
        self.oracle.page_size()
    }

    fn observe(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        self.oracle.observe(before)
    }

    fn scan_memory_accesses(&mut self, before: &SystemState<A>) -> Result<Vec<Addr>, OracleError> {
        self.oracle.scan_memory_accesses(before)
    }

    fn debug_dump(&mut self) {
        self.oracle.debug_dump()
    }

    fn restart(&mut self) {
        self.oracle.restart()
    }

    fn kill(self) {
        self.oracle.kill()
    }

    fn observe_carefully(&mut self, before: &SystemState<A>) -> Result<SystemState<A>, OracleError> {
        self.oracle.observe_carefully(before)
    }

    fn batch_observe_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        self.oracle.batch_observe_iter(states)
    }

    fn batch_observe_gpreg_only_iter<'a, S: AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        self.oracle.batch_observe_gpreg_only_iter(states)
    }

    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool = O::UNRELIABLE_INSTRUCTION_FETCH_ERRORS;
}

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

pub struct OracleGroup<O> {
    num_oracles: usize,
    oracles: Vec<O>,
}

pub struct OraclePool<S: OracleSource> {
    source: S,
    idle: HashMap<u64, OracleGroup<S::Oracle>>,
}

impl<S: OracleSource> OraclePool<S> {
    pub fn new(source: S) -> Self {
        Self {
            source,
            idle: HashMap::new(),
        }
    }

    pub fn get(&mut self) -> PooledOracle<S::Oracle> {
        // Try to find the best available oracle
        let mut choices = self.idle.iter_mut().collect::<Vec<_>>();
        choices.sort_by_key(|(_, entry)| entry.oracles.len());
        for (&key, entry) in choices {
            if let Some(oracle) = entry.oracles.pop() {
                println!("Returning observer from VM {key}");
                return PooledOracle {
                    source_id: key,
                    oracle,
                }
            }
        }

        // Create a new oracle
        // SAFETY: This ID must be globally unique to ensure that oracles cannot be returned to the wrong VM.
        let key = NEXT_ID.fetch_add(1, Ordering::SeqCst);

        println!("Spawning new VM {key}");
        let mut oracles = self.source.start();
        let num_oracles = oracles.len();
        let oracle = oracles.pop().unwrap();

        self.idle.insert(
            key,
            OracleGroup {
                num_oracles,
                oracles,
            },
        );

        PooledOracle {
            source_id: key,
            oracle,
        }
    }

    pub fn release(&mut self, oracle: PooledOracle<S::Oracle>) {
        let key = oracle.source_id;

        println!("Returning observer to {key}");
        if let Some(entry) = self.idle.get_mut(&key) {
            println!("Pushing on list of {} observers", entry.oracles.len());
            entry.oracles.push(oracle.oracle);

            // If all oracles are idle, we can kill the process.
            if entry.oracles.len() >= entry.num_oracles {
                println!("Killing VM {key}");
                self.idle.remove(&key).unwrap();
            }
        } else {
            panic!("You released an oracle that does not belong to this pool.");
        }
    }
}
