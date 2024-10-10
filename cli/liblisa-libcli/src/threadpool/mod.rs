//! An implementation of a CPU-topography aware threadpool.
//!
//! On some CPUs (such as AMD CPUs with multiple CCUs), not all cores are equal.
//! Shared memory access between two different CCUs is much slower than shared memory on the same CCU.
//!
//! This threadpool identifies the CPU cores that share the same L3 cache, and then spawns threads with CPU affinity set.
//! The CPU observer uses a ring buffer in shared memory, and its performance is highly dependent on shared memory performance.
//!
//! Each thread is provided with an observer instance that is guaranteed to run on a CPU that shares L3 cache.

use std::collections::HashSet;
use std::error::Error;
use std::fmt::Display;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{Scope, ScopedJoinHandle};
use std::time::Duration;

use liblisa::arch::Arch;
use liblisa::oracle::{Oracle, OracleSource};
use log::info;
use nix::sched::CpuSet;
use nix::unistd::Pid;

pub mod cache;
pub mod cpu;
pub mod enumeration;
pub mod oracle;
pub mod synthesis;
pub mod work;

pub trait OracleProvider<A: Arch> {
    type O: Oracle<A> + 'static;

    fn oracle(&self) -> Result<Self::O, Box<dyn Error>>;
}

use self::cpu::CpuInfo;
use self::oracle::{OraclePool, PooledOracle};
use self::work::Work;

#[derive(Copy, Clone, Debug)]
pub struct ThreadId(usize);

impl Display for ThreadId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:02}", self.0)
    }
}

struct CoreGroup<S: OracleSource> {
    cpus: CpuSet,
    oracle_pool: OraclePool<S>,
}

pub struct ThreadControl<'borrow, O> {
    thread_active: Arc<AtomicBool>,
    handle: ScopedJoinHandle<'borrow, O>,
    core_group_index: usize,
}

pub struct ThreadPool<'borrow, 'scope, F, S: OracleSource> {
    work: F,
    scope: &'borrow Scope<'borrow, 'scope>,
    threads: Vec<ThreadControl<'borrow, PooledOracle<S::Oracle>>>,
    core_groups: Vec<CoreGroup<S>>,
}

fn cpuset_is_empty(set: &CpuSet) -> bool {
    for n in 0..CpuSet::count() {
        if set.is_set(n).unwrap() {
            return false
        }
    }

    true
}

fn filter_cpuset(allowed: CpuSet, set: CpuSet) -> CpuSet {
    let mut result = CpuSet::new();
    for n in 0..CpuSet::count() {
        if allowed.is_set(n).unwrap() && set.is_set(n).unwrap() {
            result.set(n).unwrap();
        }
    }

    result
}

impl<'borrow, 'scope, S: OracleSource, F: Fn(ThreadId, &mut PooledOracle<S::Oracle>) + Clone + Send + 'scope>
    ThreadPool<'borrow, 'scope, F, S>
where
    S::Oracle: Send + 'borrow,
{
    pub fn new(
        scope: &'borrow Scope<'borrow, 'scope>, mut source_for_affinity: impl FnMut(CpuSet) -> S, work: F,
    ) -> ThreadPool<'borrow, 'scope, F, S> {
        let current_affinity = nix::sched::sched_getaffinity(Pid::from_raw(0)).unwrap();
        let cpus = CpuInfo::all().unwrap();
        let core_groups = cpus
            .iter()
            .map(|cpu| cpu.caches().caches().find(|cache| cache.level() == 3).unwrap())
            .map(|l3cache| filter_cpuset(current_affinity, l3cache.shared_with()))
            .filter(|set| !cpuset_is_empty(set))
            .collect::<HashSet<_>>();
        info!("Identified {} core groups", core_groups.len());

        if core_groups.is_empty() {
            let available_groups = cpus
                .iter()
                .map(|cpu| cpu.caches().caches().find(|cache| cache.level() == 3).unwrap())
                .map(|l3cache| l3cache.shared_with())
                .collect::<HashSet<_>>();
            panic!(
                "No core groups found in current thread affinity: {current_affinity:?}; The affinity must be a superset of one or more of the following groups: {available_groups:#?}"
            );
        }

        ThreadPool {
            work,
            scope,
            threads: Vec::new(),
            core_groups: core_groups
                .into_iter()
                .map(|cpus| CoreGroup {
                    cpus,
                    oracle_pool: OraclePool::new(source_for_affinity(cpus)),
                })
                .collect(),
        }
    }

    pub fn current_num_threads(&self) -> usize {
        self.threads.len()
    }

    pub fn resize(&mut self, num_threads: usize) {
        if num_threads < self.threads.len() {
            let threads = self.threads.drain(num_threads..).collect::<Vec<_>>();
            for thread in threads.iter() {
                thread.thread_active.store(false, Ordering::Release);
            }

            let num = threads.len();
            for (index, thread) in threads.into_iter().enumerate() {
                println!("Waiting on thread {}/{num}...", index + 1);
                let observer = match thread.handle.join() {
                    Ok(v) => v,
                    Err(e) => std::panic::resume_unwind(e),
                };

                println!("Releasing observer to core group {}...", thread.core_group_index);
                self.core_groups[thread.core_group_index].oracle_pool.release(observer);
            }
        } else {
            while self.threads.len() < num_threads {
                let thread_id = ThreadId(self.threads.len());
                let work = self.work.clone();

                let threads = &self.threads;
                let (core_group_index, core_group) = self
                    .core_groups
                    .iter_mut()
                    .enumerate()
                    .min_by_key(|(index, _)| threads.iter().filter(|t| t.core_group_index == *index).count())
                    .unwrap();

                let affinity = core_group.cpus;
                let mut oracle = core_group.oracle_pool.get();

                let thread_active = Arc::new(AtomicBool::new(true));
                let thread_active_clone = thread_active.clone();
                let handle = std::thread::Builder::new()
                    .name(format!("Worker #{thread_id}"))
                    .spawn_scoped(self.scope, move || {
                        nix::sched::sched_setaffinity(Pid::from_raw(0), &affinity).unwrap();
                        println!(
                            "[{thread_id}] Running on CPUs {:?}...",
                            (0..256).filter(|i| affinity.is_set(*i).unwrap_or(false)).collect::<Vec<_>>()
                        );

                        while thread_active_clone.load(Ordering::SeqCst) {
                            work(thread_id, &mut oracle);
                        }

                        thread_active_clone.store(false, Ordering::SeqCst);

                        println!("[{thread_id}] Stopped.");

                        oracle
                    })
                    .unwrap();

                self.threads.push(ThreadControl {
                    thread_active,
                    handle,
                    core_group_index,
                });
            }
        }
    }
}

impl<'borrow, 'scope, S: OracleSource> ThreadPool<'borrow, 'scope, (), S> {
    pub fn from_work<A: Arch, C: Send + Sync, W: Work<A, C> + Send, F: Fn(W::Artifact) + Send + Sync>(
        scope: &'borrow Scope<'borrow, 'scope>, source_for_affinity: impl FnMut(CpuSet) -> S, cache: &'scope C,
        work: &'scope Mutex<(W, W::RuntimeData)>, save_artifact: &'scope F,
    ) -> ThreadPool<'borrow, 'scope, impl Fn(ThreadId, &mut PooledOracle<S::Oracle>) + Clone + Send + 'scope, S>
    where
        W::RuntimeData: Send,
        W::Request: std::fmt::Debug,
        S::Oracle: Oracle<A> + Send + 'borrow,
    {
        ThreadPool::new(scope, source_for_affinity, move |thread_id, oracle| {
            let next_item = {
                let (work, data) = &mut *work.lock().unwrap();
                work.next(data)
            };

            println!("Thread {thread_id}: {next_item:?}");

            match next_item {
                Some(request) => {
                    let result = W::run(oracle, cache, &request);
                    let (work, data) = &mut *work.lock().unwrap();
                    if let Some(artifact) = work.complete(data, request, result) {
                        save_artifact(artifact);
                    }
                },
                None => std::thread::sleep(Duration::from_secs(15)),
            }
        })
    }
}

impl<F, P: OracleSource> Drop for ThreadPool<'_, '_, F, P> {
    fn drop(&mut self) {
        for thread in self.threads.iter() {
            thread.thread_active.store(false, Ordering::Release);
        }

        for thread in self.threads.drain(..) {
            let observer = thread.handle.join().unwrap();
            self.core_groups[thread.core_group_index].oracle_pool.release(observer);
        }
    }
}
