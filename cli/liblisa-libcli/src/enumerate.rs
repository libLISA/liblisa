use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::marker::PhantomData;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use colored::Colorize;
use itertools::Itertools;
use liblisa::arch::{Arch, Scope};
use liblisa::encoding::dataflows::AddressComputation;
use liblisa::encoding::mcs::{filter_overlapping_encodings, verify_and_fix};
use liblisa::encoding::Encoding;
use liblisa::instr::{FilterMap, Instruction, InstructionFilter};
use liblisa::oracle::{Oracle, OracleSource};
use liblisa_enc::cache::EncodingAnalysisCache;
use log::info;
use nix::sched::CpuSet;
use rayon::prelude::*;
use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::threadpool::cache::FileBackedCacheLoader;
use crate::threadpool::enumeration::{
    EnumWorkItem, Enumeration, EnumerationArtifact, EnumerationArtifactData, EnumerationRuntimeData,
};
use crate::threadpool::ThreadPool;

#[derive(Copy, Clone, Debug, clap::ValueEnum)]
enum Sorting {
    Time,
}

#[derive(Clone, Debug, clap::Parser)]
enum Verb {
    /// Creates a new enumeration
    Create {
        #[clap(long = "work-items")]
        work_items: Option<usize>,

        #[clap(long = "scan")]
        scan: Option<PathBuf>,

        #[clap(long = "weights")]
        weights: Option<PathBuf>,
    },

    /// Runs a previously created enumeration
    Run {
        #[clap(long)]
        threads: Option<usize>,

        #[clap(long)]
        exit_after: Option<u64>,
    },

    /// Prints the status of the enumeration
    Status {
        #[clap(long)]
        scan: Option<PathBuf>,

        #[clap(long)]
        weights: Option<PathBuf>,

        #[clap(long)]
        hide_done: bool,

        #[clap(long)]
        group_by_stall: bool,

        #[clap(long)]
        print_remaining: bool,
    },

    GuessSplit {
        weights: PathBuf,
    },

    /// Prints statistics of found encodings
    Stats,

    /// Dumps all encodings found during enumeration
    Dump {
        #[clap(long)]
        postprocess: bool,

        #[clap(long)]
        sort: Option<Sorting>,
    },

    /// Debugging only
    CounterStep {
        num: usize,
    },

    Convert,

    Extract {
        path: PathBuf,

        #[clap(long)]
        postprocess: bool,

        #[clap(long)]
        filter: Vec<InstructionFilter>,
    },

    ExtractInvalidRanges {
        path: PathBuf,
    },

    /// Explains why a certain instruction is missing an encoding
    Explain {
        instruction: Vec<Instruction>,
    },

    ExtractWeights {
        path: PathBuf,
    },
}

#[derive(Clone, Debug, clap::Parser)]
#[clap(verbatim_doc_comment)]
/// Discover instructions and infer encodings.
///
/// Since enumeration can take a long time, intermediate state is saved in a working directory.
/// This working directory can be created using the `create` subcommand.
/// After creating the working directory, enumeration can be run using the `run` subcommand.
///
/// When enumeration is complete, the synthesized semantics can be extracted using the `extract` subcommand.
pub struct EnumerationCommand<A> {
    dir: PathBuf,

    #[clap(subcommand)]
    verb: Verb,

    #[clap(skip)]
    _phantom: PhantomData<fn() -> A>,
}

#[derive(Copy, Clone, Default, Debug)]
struct Stats {
    found_seen: usize,
    found_unseen: usize,
    missed: usize,
    total: usize,
    total_seen: usize,
}

struct Format<'a> {
    hide_done: bool,
    group_by_stall: bool,
    min_virtual_runtime_ms: u128,
    from_pad: usize,
    to_pad: usize,
    counts: &'a Option<Vec<Stats>>,
    current_pad: usize,
}

impl<'a> Format<'a> {
    fn print_workers(&self, workers: &Vec<EnumWorkItem>, indent: usize, indent_pad: usize, match_stalled_by: Option<usize>) {
        for (index, worker) in workers.iter().enumerate() {
            if worker.done && self.hide_done {
                continue;
            }

            if worker.stalled_by != match_stalled_by && self.group_by_stall {
                continue;
            }

            self.print_worker(worker, index, indent, indent_pad);

            if self.group_by_stall {
                self.print_workers(workers, indent + 2, indent_pad.saturating_sub(2), Some(index));
            }
        }
    }

    fn print_worker(&self, worker: &EnumWorkItem, index: usize, indent: usize, indent_pad: usize) {
        let work_hours = worker.runtime_ms as f64 / (1000 * 60 * 60) as f64;
        let virtual_runtime_offset_secs = (worker.virtual_runtime_ms.saturating_sub(self.min_virtual_runtime_ms)) / 1000;
        let empty = "";
        let from = format!("{:X}", worker.from()).dimmed();
        let to = worker.to().map(|x| format!("{x:X}")).unwrap_or_default().dimmed();
        print!(
            "{empty:indent$}[#{index:3}] {work_hours:5.1}h +{virtual_runtime_offset_secs:4}s: {empty:indent_pad$}{from:from_pad$} → {to:to_pad$} ",
            from_pad = self.from_pad,
            to_pad = self.to_pad,
        );
        if let Some(counts) = self.counts {
            let Stats {
                found_seen,
                found_unseen,
                missed,
                total,
                total_seen,
            } = &counts[index];
            let total_seen = *total_seen as f64 / *total as f64 * 100.;
            let found_unseen = *found_unseen as f64 / *total as f64 * 100.;
            let miss = *missed as f64 / (found_seen + missed) as f64 * 100.;
            print!("{total_seen:>4.1}% (+{found_unseen:>4.1}%) miss: {miss:>4.1}% ");
        }
        if worker.done {
            print!("done: ");
        } else if let Some(next) = &worker.next {
            print!("^ {:pad$}: ", format!("{next:X}").bold(), pad = self.current_pad);
        } else {
            print!(
                "@ {:pad$}: ",
                format!("{:X}", worker.counter.current()).bold(),
                pad = self.current_pad
            );
        }
        println!("found {} encodings", worker.encodings_found);
    }
}

impl<A: Arch> EnumerationCommand<A> {
    pub fn save_state<S: Scope + Serialize>(&self, state: &Enumeration<S>) {
        {
            let file = File::create(self.tmp_state_path()).unwrap();
            serde_json::to_writer(file, state).unwrap();
        }

        fs::rename(self.tmp_state_path(), self.state_path()).unwrap();
    }

    pub fn load_state<S: Scope + DeserializeOwned>(&self) -> Enumeration<S> {
        let file = File::open(self.state_path()).unwrap();
        serde_json::from_reader(file).unwrap()
    }

    pub fn load_artifacts(&self) -> Result<Vec<EnumerationArtifact<A, ()>>, Box<dyn Error>> {
        println!("Loading encodings...");
        let file = File::open(self.artifact_path()).unwrap();
        Ok(BufReader::new(file)
            .lines()
            .map(|line| line.unwrap())
            .filter(|line| !line.is_empty())
            .enumerate()
            .map(|(index, line)| match serde_json::from_str(&line) {
                Ok(v) => v,
                Err(e) => panic!("Error loading encoding on line {index}: {e}"),
            })
            .collect::<Vec<_>>())
    }

    fn state_path(&self) -> PathBuf {
        self.dir.join("state.json")
    }

    fn tmp_state_path(&self) -> PathBuf {
        self.dir.join(".tmp.state.json")
    }

    fn artifact_path(&self) -> PathBuf {
        self.dir.join("encodings.ndjson")
    }

    pub fn run<S: OracleSource, E: Scope + Serialize + DeserializeOwned>(
        &self, create_oracle_source: impl FnMut(CpuSet) -> S, scope: E,
    ) where
        S::Oracle: Oracle<A> + Send,
    {
        // let save_paths = EnumerationPaths::from(self.dir.clone());
        match &self.verb {
            Verb::Create {
                work_items,
                scan,
                weights,
            } => {
                let sampled_instrs = if let Some(scan_file) = scan {
                    let v: Vec<Instruction> = serde_json::from_reader(BufReader::new(File::open(scan_file).unwrap())).unwrap();
                    let mut v = v.into_iter().map(|instr| (instr, 1)).collect::<Vec<_>>();
                    v.insert(0, (Instruction::new(&[0]), 1));
                    v
                } else if let Some(path) = weights {
                    let v: Vec<(Instruction, u128)> = serde_json::from_reader(BufReader::new(File::open(path).unwrap())).unwrap();
                    v
                } else {
                    (0..=255u8).map(|i| (Instruction::new(&[i]), 1)).collect::<Vec<_>>()
                };

                fs::create_dir_all(&self.dir).unwrap();

                let enumeration = Enumeration::create(work_items.unwrap_or(80), &sampled_instrs, scope);
                let file = File::create(self.state_path()).unwrap();
                serde_json::to_writer(file, &enumeration).unwrap();

                // Clear the artifacts file that might still store previous entries
                File::create(self.artifact_path()).unwrap();

                println!("Created {:?}", self.dir);
            },
            Verb::Run {
                threads,
                exit_after,
            } => {
                let enumeration = Mutex::new({
                    let enumeration = self.load_state::<E>();
                    let runtime_data = EnumerationRuntimeData::from_enumeration(&enumeration);
                    (enumeration, runtime_data)
                });

                let artifact_file = Mutex::new(BufWriter::new(
                    File::options().append(true).create(true).open(self.artifact_path()).unwrap(),
                ));

                println!("Loading cache...");
                let cache_ma = self.dir.join("memory_accesses.cache");
                let cache_tv = self.dir.join("threshold_values.cache");
                let cache_df = self.dir.join("dataflows.cache");
                let mut cache_loader = FileBackedCacheLoader::open(&cache_ma, &cache_df, &cache_tv).unwrap();
                let cache = cache_loader.load::<A>();
                println!("Entries in cache: {}", cache.num_entries());

                let save_artifact = move |artifact| {
                    let mut w = artifact_file.lock().unwrap();
                    serde_json::to_writer(&mut *w, &artifact).unwrap();
                    writeln!(w).unwrap();
                    w.flush().unwrap();
                };

                let running = AtomicBool::new(true);
                std::thread::scope(|scope| -> Result<(), Box<dyn Error>> {
                    scope.spawn(|| {
                        let mut last_save = Instant::now();
                        while running.load(Ordering::SeqCst) {
                            std::thread::sleep(Duration::from_secs(5));

                            if last_save.elapsed() >= Duration::from_secs(60) {
                                println!("Saving state...");
                                self.save_state(&enumeration.lock().unwrap().0);
                                last_save = Instant::now();
                                println!("Save complete");
                            }
                        }
                    });

                    {
                        let mut pool = ThreadPool::from_work(scope, create_oracle_source, &cache, &enumeration, &save_artifact);

                        // TODO: Automatically determine the right size
                        pool.resize(threads.unwrap_or(2));

                        if let Some(exit_after) = exit_after {
                            println!("WARNING: Running for only {exit_after} seconds!");
                            std::thread::sleep(Duration::from_secs(*exit_after))
                        } else {
                            for line in std::io::stdin().lines() {
                                let line = line?;
                                let command = line.split(' ').map(str::trim).collect::<Vec<_>>();
                                match &command[..] {
                                    ["stop"] => break,
                                    ["threads", num] => match num.parse::<usize>() {
                                        Ok(num) => {
                                            println!("Resizing thread pool to {num}...");
                                            pool.resize(num);
                                            println!("Thread pool resized to {num}");
                                        },
                                        Err(e) => println!("{e}"),
                                    },
                                    ["split", instr] => match hex::decode(instr) {
                                        Ok(data) => {
                                            let instruction = Instruction::new(&data);
                                            let (enumeration, runtime_data) = &mut *enumeration.lock().unwrap();
                                            match enumeration.split_on_instr(&mut *runtime_data, instruction) {
                                                Ok(_) => println!("Work item split"),
                                                Err(e) => println!("{e}"),
                                            }
                                        },
                                        Err(e) => println!("{e}"),
                                    },
                                    _ => println!("Commands available: stop | threads [n] | split [instr]"),
                                }
                            }
                        }

                        // By resizing to 0, all threads will be terminated
                        println!("Stopping all threads...");
                        pool.resize(0);
                    }

                    running.store(false, Ordering::SeqCst);

                    println!("Waiting for all scoped threads to terminate...");

                    Ok(())
                })
                .unwrap();

                println!("Performing last save...");
                self.save_state(&enumeration.lock().unwrap().0);

                println!("OK!");
            },
            Verb::Status {
                scan,
                weights,
                hide_done,
                group_by_stall,
                print_remaining,
            } => {
                let enumeration = self.load_state::<E>();
                let workers = &enumeration.work;
                let _unique_sequences: u128 = workers.iter().map(|s| s.unique_sequences).sum();
                let seconds_running = enumeration.runtime_ms / 1000;
                let total_cputime: u128 = workers.iter().map(|s| s.runtime_ms).sum::<u128>() / 1000;
                let avg_concurrency = (total_cputime * 100 / seconds_running.max(1)) as f64 / 100.0;

                if let Some(weights) = weights {
                    let weights: Vec<(Instruction, u128)> =
                        serde_json::from_reader(BufReader::new(File::open(weights).unwrap())).unwrap();
                    let mut filter_map = FilterMap::new();
                    {
                        let artifacts = self.load_artifacts().unwrap();
                        for e in artifacts.iter() {
                            if let EnumerationArtifactData::Encoding(e) = &e.data {
                                let filters = e.filters();
                                if filters.is_empty() {
                                    panic!("No filters for {e}");
                                }

                                for filter in filters {
                                    filter_map.add(filter, 0);
                                }
                            }
                        }
                    };

                    println!("Processing {} weights", weights.len());
                    let mut ms_done = 0;
                    let mut ms_remaining = 0;
                    let mut n = 0;
                    for (instr, time) in weights {
                        let worker = workers
                            .iter()
                            .position(|w| &instr >= w.from() && w.to().as_ref().map(|to| &instr <= to).unwrap_or(true))
                            .unwrap();
                        let seen = workers[worker].done || workers[worker].counter.current() > instr;
                        if seen || filter_map.filters(&instr).is_some() {
                            ms_done += time;
                        } else {
                            ms_remaining += time;
                        }

                        n += 1;
                        if n % 2500 == 0 {
                            println!("Processed {n} weights");
                        }
                    }

                    const MS_PER_H: u128 = 1000 * 60 * 60;
                    let speed_factor = (ms_done / 1000) as f64 / total_cputime as f64;
                    println!(
                        "Time done: {}h; Time remaining: {}h",
                        ms_done / MS_PER_H,
                        ms_remaining / MS_PER_H
                    );
                    println!("Speed factor: {speed_factor:.5}x");
                    let cpu_hours_remaining = (ms_remaining / MS_PER_H) as f64 / speed_factor;
                    let hours_remaining = cpu_hours_remaining / avg_concurrency;
                    println!(
                        "Expected time remaining: {cpu_hours_remaining:.1} CPU-hours, which is ~{hours_remaining:.1}h based on the average concurrency"
                    );
                }

                let (counts, encodings_seen) = if let Some(scan) = scan {
                    let mut filter_map = FilterMap::new();
                    let num_encodings = {
                        let artifacts = self.load_artifacts().unwrap();
                        let mut num_encodings = 0;
                        for e in artifacts.iter() {
                            if let EnumerationArtifactData::Encoding(e) = &e.data {
                                let filters = e.filters();
                                if filters.is_empty() {
                                    panic!("No filters for {e}");
                                }

                                for filter in filters {
                                    filter_map.add(filter, num_encodings);
                                }
                                num_encodings += 1;
                            }
                        }

                        num_encodings
                    };

                    let mut v: Vec<Instruction> = serde_json::from_reader(BufReader::new(File::open(scan).unwrap())).unwrap();
                    v.retain(|instr| scope.is_instr_in_scope(instr.bytes()));
                    print!("Checking progress");

                    let (counts, encodings_seen) = v
                        .par_iter()
                        .chunks(5000)
                        .map(|chunk| {
                            let mut counts = vec![Stats::default(); workers.len()];
                            let mut encodings_seen = vec![false; num_encodings];

                            for instr in chunk {
                                let worker = workers
                                    .iter()
                                    .position(|w| instr >= w.from() && w.to().as_ref().map(|to| instr <= to).unwrap_or(true))
                                    .unwrap();

                                let mut match_found = false;
                                if let Some(index) = filter_map.filters(instr) {
                                    match_found = true;
                                    encodings_seen[*index] = true;
                                }

                                let seen = workers[worker].done || &workers[worker].counter.current() > instr;

                                if match_found {
                                    if seen {
                                        counts[worker].found_seen += 1;
                                    } else {
                                        counts[worker].found_unseen += 1;
                                    }
                                } else if seen {
                                    counts[worker].missed += 1;
                                    println!("Worker {worker:02} has MISSED {instr:X}");
                                } else if *print_remaining {
                                    println!("Worker {worker:02} remaining = {instr:X}");
                                }

                                if seen {
                                    counts[worker].total_seen += 1;
                                }

                                counts[worker].total += 1;
                            }

                            print!(".");
                            std::io::stdout().lock().flush().expect("Could not flush stdout");

                            (counts, encodings_seen)
                        })
                        .reduce(
                            || (vec![Stats::default(); workers.len()], vec![false; num_encodings]),
                            |(mut counts, mut seen), (other_counts, other_seen)| {
                                for (count, other_count) in counts.iter_mut().zip(other_counts.iter()) {
                                    count.missed += other_count.missed;
                                    count.total += other_count.total;
                                    count.found_seen += other_count.found_seen;
                                    count.found_unseen += other_count.found_unseen;
                                    count.total_seen += other_count.total_seen;
                                }

                                for (seen, other_seen) in seen.iter_mut().zip(other_seen.iter()) {
                                    *seen = *seen || *other_seen;
                                }

                                (counts, seen)
                            },
                        );

                    println!();

                    (Some(counts), encodings_seen)
                } else {
                    (None, Vec::new())
                };

                let num_encodings = workers.iter().map(|x| x.encodings_found).sum::<u64>();
                let num_active_workers = workers.iter().filter(|w| !w.done && w.stalled_by.is_none()).count();
                let num_stalled_workers = workers.iter().filter(|w| !w.done && w.stalled_by.is_some()).count();
                let num_workers_done = workers.iter().filter(|w| w.done).count();

                let hours_running = seconds_running as f64 / 3600.0;
                let cpu_hours = total_cputime as f64 / 3600.0;
                println!(
                    "Found {num_encodings} encodings in {hours_running:.1}h | CPU time: {cpu_hours:.0}h | Concurrency factor: {avg_concurrency:.2}×"
                );
                println!("{num_active_workers} active | {num_stalled_workers} stalled | {num_workers_done} done");
                println!();

                let mut depth = vec![0; workers.len()];

                for (worker_index, worker) in workers.iter().enumerate() {
                    if let Some(index) = worker.stalled_by {
                        depth[index] = depth[index].max(depth[worker_index] + 1);
                    }
                }

                let max_depth = depth.iter().copied().max().unwrap();

                let current_pad = workers.iter().map(|s| s.counter.current().bytes().len() * 2).max().unwrap();
                let from_pad = workers.iter().map(|s| s.from().bytes().len() * 2).max().unwrap();
                let to_pad = workers
                    .iter()
                    .map(|s| s.to().map(|s| s.bytes().len() * 2).unwrap_or(0))
                    .max()
                    .unwrap();
                let min_virtual_runtime_ms = workers
                    .iter()
                    .filter(|w| !w.done || !hide_done)
                    .map(|w| w.virtual_runtime_ms)
                    .min()
                    .unwrap();
                let indent_pad = if *group_by_stall { max_depth * 2 } else { 0 };
                Format {
                    hide_done: *hide_done,
                    group_by_stall: *group_by_stall,
                    min_virtual_runtime_ms,
                    from_pad,
                    to_pad,
                    counts: &counts,
                    current_pad,
                }
                .print_workers(workers, 0, indent_pad, None);

                if let Some(counts) = counts {
                    let found_seen = counts.iter().map(|s| s.found_seen).sum::<usize>();
                    let found_unseen = counts.iter().map(|s| s.found_unseen).sum::<usize>();
                    let total = counts.iter().map(|s| s.total).sum::<usize>();
                    let missed = counts.iter().map(|s| s.missed).sum::<usize>();

                    println!();
                    println!(
                        "Overall progress: {:3.1}%, {:3.1}% missed ({}:{} / {}) - {} remaining",
                        (found_seen + missed) as f64 / total as f64 * 100.,
                        missed as f64 / (found_seen + missed) as f64 * 100.,
                        found_seen,
                        missed,
                        total,
                        total - (found_seen + missed)
                    );
                    println!(
                        "Discovered: {:3.1}% ({}:{} / {}) - {} remaining",
                        (found_seen + found_unseen + missed) as f64 / total as f64 * 100.,
                        found_seen + found_unseen,
                        missed,
                        total,
                        total - (found_seen + found_unseen + missed)
                    );
                    let encodings_seen = encodings_seen.iter().filter(|s| **s).count();
                    println!(
                        "Our scan contains entries for {} / {} encodings that we found => {:3.1} ",
                        encodings_seen,
                        num_encodings,
                        encodings_seen as f64 / num_encodings as f64 * 100.
                    );
                }
            },
            Verb::GuessSplit {
                weights,
            } => {
                let enumeration = self.load_state::<E>();
                let workers = &enumeration.work;

                let weights: Vec<(Instruction, u128)> =
                    serde_json::from_reader(BufReader::new(File::open(weights).unwrap())).unwrap();
                let mut filter_map = FilterMap::new();
                {
                    let artifacts = self.load_artifacts().unwrap();
                    for e in artifacts.iter() {
                        if let EnumerationArtifactData::Encoding(e) = &e.data {
                            let filters = e.filters();
                            if filters.is_empty() {
                                panic!("No filters for {e}");
                            }

                            for filter in filters {
                                filter_map.add(filter, 0);
                            }
                        }
                    }
                };

                println!("Processing {} weights", weights.len());
                let unseen_weights = weights
                    .into_par_iter()
                    .filter(|&(instr, _)| {
                        let worker = workers
                            .iter()
                            .position(|w| &instr >= w.from() && w.to().as_ref().map(|to| &instr <= to).unwrap_or(true))
                            .unwrap();
                        let seen = workers[worker].done || workers[worker].counter.current() > instr;

                        !seen && filter_map.filters(&instr).is_none()
                    })
                    .collect::<Vec<_>>();

                for (worker_index, worker) in workers.iter().enumerate() {
                    if !worker.done {
                        let unseen_weights = unseen_weights
                            .iter()
                            .filter(|&&(instr, _)| {
                                &instr >= worker.from() && worker.to().as_ref().map(|to| &instr <= to).unwrap_or(true)
                            })
                            .collect::<Vec<_>>();
                        let total_time = unseen_weights.iter().map(|&(_, w)| w).sum::<u128>();
                        let mut time = 0;

                        println!("Worker #{worker_index:02}:");

                        for &(instr, w) in unseen_weights.iter() {
                            time += w;
                            if time >= total_time / 10 {
                                time = 0;
                                println!(" - {instr:X}");
                            }
                        }
                    }
                }
            },
            Verb::Dump {
                postprocess,
                sort,
            } => {
                let mut artifacts = self.load_artifacts().unwrap();
                if let Some(Sorting::Time) = sort {
                    artifacts.sort_by_key(|a| a.ms_taken)
                }

                let mut seen = HashSet::new();
                let encodings = artifacts
                    .into_iter()
                    .flat_map(|a| match a.data {
                        EnumerationArtifactData::Encoding(encoding) => Some(encoding),
                        EnumerationArtifactData::Failed(_)
                        | EnumerationArtifactData::Excluded(_)
                        | EnumerationArtifactData::InvalidInstructions(_)
                        | EnumerationArtifactData::MemoryErrorInstructions(_) => None,
                    })
                    .collect::<Vec<_>>();
                println!("Cleaning up encodings..");
                let encodings = if *postprocess {
                    postprocess_encodings(&encodings)
                } else {
                    encodings
                };

                for (index, encoding) in encodings.iter().enumerate() {
                    println!("Encoding #{index:5}: {encoding}");

                    let filters = encoding.filters();
                    if !seen.contains(&filters) {
                        seen.insert(filters);
                    } else {
                        println!("(duplicate encoding)");
                    }

                    println!("Perfect variant: {:?}", encoding.best_instr().map(|i| format!("{i:X}")));
                    println!();
                    println!();
                }

                println!(
                    "Unique encodings: {} out of {} ({} duplicates)",
                    seen.len(),
                    encodings.len(),
                    encodings.len() - seen.len()
                );

                let mut counts = HashMap::new();
                for encoding in encodings.iter() {
                    let num = encoding.dataflows.addresses.len();
                    *counts.entry(num).or_insert(0) += 1;
                }

                println!("Counts per number of memory accesses: {counts:?}");

                let mut counts = HashMap::new();
                for encoding in encodings.iter() {
                    let num = encoding
                        .dataflows
                        .output_dataflows()
                        .map(|o| o.inputs.len())
                        .max()
                        .unwrap_or(0);
                    *counts.entry(num).or_insert(0) += 1;
                }

                println!(
                    "Counts per number of inputs: {:?}",
                    counts.iter().sorted_by_key(|(n, _)| *n).collect::<Vec<_>>()
                );
            },
            Verb::Extract {
                path,
                postprocess,
                filter,
            } => {
                let artifacts = self.load_artifacts().unwrap();
                let mut encodings = artifacts
                    .into_iter()
                    .flat_map(|a| match a.data {
                        EnumerationArtifactData::Encoding(encoding) => Some(encoding),
                        EnumerationArtifactData::Failed(_)
                        | EnumerationArtifactData::Excluded(_)
                        | EnumerationArtifactData::InvalidInstructions(_)
                        | EnumerationArtifactData::MemoryErrorInstructions(_) => None,
                    })
                    .collect::<Vec<_>>();

                if !filter.is_empty() {
                    println!("Filtering encodings on {filter:?}");
                    encodings.retain(|encoding| filter.iter().any(|f| f.matches(encoding.dataflows.instr())));

                    println!("{} encodings remaining", encodings.len());
                }

                println!("Verifying and fixing encodings...");
                verify_and_fix(&mut encodings, true);

                println!("Cleaning up encodings..");
                let mut encodings = if *postprocess {
                    postprocess_encodings(&encodings)
                } else {
                    encodings
                };

                println!(
                    "Removing encodings that cover no instructions in {} encodings...",
                    encodings.len()
                );
                encodings.retain(|e| e.covers_some_instr());

                println!("Splitting flags...");
                let mut encodings = encodings
                    .into_par_iter()
                    .map(|mut encoding| {
                        encoding.split_flag_output();
                        encoding
                    })
                    .collect::<Vec<_>>();
                encodings.sort_by_key(|e| e.dataflows.outputs.len());

                verify_and_fix(&mut encodings, false);

                println!("Extracted {} encodings", encodings.len());
                println!("Saving results...");
                serde_json::to_writer(BufWriter::new(File::create(path).unwrap()), &encodings).unwrap();
            },
            Verb::ExtractInvalidRanges {
                path,
            } => {
                let artifacts = self.load_artifacts().unwrap();
                let ranges = artifacts
                    .into_iter()
                    .flat_map(|a| match a.data {
                        EnumerationArtifactData::InvalidInstructions(range) => Some((range.start, range.end)),
                        EnumerationArtifactData::Encoding(_)
                        | EnumerationArtifactData::Failed(_)
                        | EnumerationArtifactData::Excluded(_)
                        | EnumerationArtifactData::MemoryErrorInstructions(_) => None,
                    })
                    .collect::<Vec<_>>();

                println!("Saving results...");
                serde_json::to_writer(BufWriter::new(File::create(path).unwrap()), &ranges).unwrap();
            },
            Verb::ExtractWeights {
                path,
            } => {
                let artifacts = self.load_artifacts().unwrap();
                let mut instrs = HashMap::new();

                for a in artifacts.into_iter() {
                    match a.data {
                        EnumerationArtifactData::Encoding(encoding) => {
                            *instrs.entry(*encoding.instr()).or_insert(0) += a.ms_taken;
                        },
                        EnumerationArtifactData::Failed(instr) | EnumerationArtifactData::Excluded(instr) => {
                            *instrs.entry(instr).or_insert(0) += a.ms_taken;
                        },
                        EnumerationArtifactData::InvalidInstructions(range)
                        | EnumerationArtifactData::MemoryErrorInstructions(range) => {
                            *instrs.entry(range.start).or_insert(0) += a.ms_taken;
                        },
                    }
                }

                let mut instrs = instrs.into_iter().collect::<Vec<_>>();

                instrs.sort();
                instrs.dedup();

                println!("Saving results...");
                serde_json::to_writer(File::create(path).unwrap(), &instrs).unwrap();
            },
            Verb::CounterStep {
                num,
            } => {
                let enumeration = self.load_state::<E>();
                let mut worker = enumeration.work[*num].clone();
                worker.counter.apply_filters_to_current(&enumeration.filters, false);
            },
            Verb::Convert => {
                println!("Loading artifacts...");
                let file = File::open(self.artifact_path()).unwrap();
                let artifacts: Vec<EnumerationArtifactData<A, AddressComputation>> = BufReader::new(file)
                    .lines()
                    .map(|line| line.unwrap())
                    .filter(|line| !line.is_empty())
                    .map(|line| serde_json::from_str(&line).unwrap())
                    .collect::<Vec<_>>();
                let mut output = BufWriter::new(
                    File::options()
                        .create(true)
                        .write(true)
                        .append(false)
                        .truncate(true)
                        .open(self.artifact_path())
                        .unwrap(),
                );

                for data in artifacts {
                    serde_json::to_writer(
                        &mut output,
                        &EnumerationArtifact {
                            ms_taken: 0,
                            worker_index: 0,
                            data,
                        },
                    )
                    .unwrap();
                    writeln!(&mut output).unwrap();
                }
            },
            Verb::Explain {
                instruction,
            } => {
                let artifacts = self.load_artifacts().unwrap();
                let enumeration = self.load_state::<E>();
                let workers = &enumeration.work;

                for instruction in instruction {
                    let responsible_worker = workers
                        .iter()
                        .enumerate()
                        .find(|(_, w)| instruction >= w.from() && w.to().map(|x| instruction < x).unwrap_or(true));
                    if let Some((worker_index, worker)) = responsible_worker {
                        println!("Worker #{worker_index} is responsible for enumerating {instruction:X}");

                        if worker.counter.current() < *instruction {
                            println!("The worker is still enumerating, and has not encountered this instruction just yet.");
                        } else {
                            let mut closest_before = None;
                            let mut closest_after = None;
                            let mut matching = None;
                            for artifact in artifacts.iter() {
                                let (lo, hi, eq) = match &artifact.data {
                                    EnumerationArtifactData::Encoding(e) => {
                                        let filters = e.filters();
                                        let eq = filters.iter().any(|f| f.matches(instruction));
                                        let lo = filters.iter().map(|f| f.smallest_matching_instruction()).max().unwrap();
                                        let hi = filters.iter().map(|f| f.largest_matching_instruction()).min().unwrap();

                                        (lo, hi, eq)
                                    },
                                    EnumerationArtifactData::Failed(instr) | EnumerationArtifactData::Excluded(instr) => {
                                        (*instr, *instr, instr == instruction)
                                    },
                                    EnumerationArtifactData::InvalidInstructions(range)
                                    | EnumerationArtifactData::MemoryErrorInstructions(range) => {
                                        (range.start, range.end, range.contains(instruction))
                                    },
                                };

                                if eq {
                                    matching = Some(artifact);
                                }

                                if artifact.worker_index == worker_index {
                                    if lo < *instruction && closest_before.map(|(best, _)| lo > best).unwrap_or(true) {
                                        closest_before = Some((lo, artifact));
                                    }

                                    if hi > *instruction && closest_after.map(|(best, _)| hi < best).unwrap_or(true) {
                                        closest_after = Some((lo, artifact));
                                    }
                                }
                            }

                            if let Some(artifact) = matching {
                                match &artifact.data {
                                    EnumerationArtifactData::Encoding(e) => {
                                        println!("Instruction is matched by this encoding: {e}");
                                        println!("It has the following filters:");

                                        for filter in e.filters() {
                                            println!(
                                                " - {filter:?}{}",
                                                if filter.matches(instruction) {
                                                    format!(" <-- This one matches {instruction:X}")
                                                } else {
                                                    String::new()
                                                }
                                            );
                                        }
                                    },
                                    EnumerationArtifactData::Failed(_) => println!("Analysis of this instruction failed."),
                                    EnumerationArtifactData::Excluded(_) => {
                                        println!("This instruction was excluded by the ExclusionPolicy")
                                    },
                                    EnumerationArtifactData::InvalidInstructions(range) => println!(
                                        "Instructions in the range {:X}..{:X} were skipped (via tunneling), because they are invalid and/or excluded instructions.",
                                        range.start, range.end
                                    ),
                                    EnumerationArtifactData::MemoryErrorInstructions(range) => println!(
                                        "Instructions in the range {:X}..{:X} were skipped (via tunneling), because memory errors were encountered during analysis.",
                                        range.start, range.end
                                    ),
                                }
                            } else {
                                // TODO: Find closest artifact before and closest artifact after
                                println!("We do not have a record of processing this instruction.");

                                if let Some((instr, before)) = closest_before {
                                    println!("Closest before: {instr:X}={before:?}");
                                }

                                if let Some((instr, after)) = closest_after {
                                    println!("Closest after: {instr:X}={after:?}");
                                }
                            }
                        }
                    } else {
                        println!("No worker covers this instruction. Did you maybe exclude it intentionally?");
                    }
                }
            },
            Verb::Stats => {
                todo!();
                // let artifacts = self.load_artifacts().unwrap();

                // println!("Grouping instructions by prefixes...");
                // let mut prefix_group_timings = HashMap::new();
                // for artifact in artifacts.iter() {
                //     let instr = match &artifact.data {
                //         EnumerationArtifactData::Encoding(e) => e.instr(),
                //         EnumerationArtifactData::Failed(instr) => instr,
                //         EnumerationArtifactData::Excluded(instr) => instr,
                //         EnumerationArtifactData::InvalidInstructions(range) => &range.start,
                //         EnumerationArtifactData::MemoryErrorInstructions(range) => &range.start,
                //     };
                //     let (parsed, _) = ParsedInstructionPrefixes::parse(instr.bytes());
                //     let prefix_names = parsed.prefixes().iter().map(|p| p.name()).collect::<Vec<_>>();

                //     if prefix_names == [ PrefixName::Vex3, PrefixName::Vex2 ] {
                //         println!("{instr:X}");
                //     }

                //     *prefix_group_timings.entry(prefix_names).or_insert(0u128) += artifact.ms_taken;
                // }

                // let likely_stack_mismatch_mmx = artifacts.iter().map(|artifact| if let EnumerationArtifactData::Encoding(e) = &artifact.data {
                //     if e.dataflows.outputs.len() > 32 && e.dataflows.iter_with_locations().any(|fg| fg.iter().any(|source| matches!(source, Source::Dest(Dest::Reg(X64Reg::X87(X87Reg::Fpr(_)), _))))) {
                //         artifact.ms_taken
                //     } else {
                //         0
                //     }
                // } else {
                //     0
                // }).sum::<u128>();

                // println!("Time taken for mmx operations with stack mismatch: {}h", (likely_stack_mismatch_mmx / 1000) as f64 / 3600.0);

                // println!("Time taken per prefix group:");
                // let mut prefix_groups = prefix_group_timings.into_iter().collect::<Vec<_>>();
                // prefix_groups.sort_by_key(|(_, ms_taken)| *ms_taken);

                // let total_time = (prefix_groups.iter().map(|(_, ms_taken)| *ms_taken).sum::<u128>() / 1000) as f64 / 3600.0;
                // println!("Total time spent: {total_time:.2}h");
                // for (prefixes, ms_taken) in prefix_groups.iter() {
                //     let hours = (ms_taken / 1000) as f64 / 3600.0;
                //     println!("    {hours:.2}h {prefixes:?}");
                // }
            },
        }
    }
}

fn postprocess_encodings<A: Arch>(encodings: &[Encoding<A, ()>]) -> Vec<Encoding<A, ()>> {
    info!("Canonicalizing encodings...");
    let encodings: Vec<_> = encodings.iter().map(|e| e.canonicalize()).collect();

    info!("Merging encodings...");
    let encodings = liblisa::encoding::merge_encodings_structurally(encodings);

    info!("Canonicalizing encodings again...");
    let mut encodings: Vec<_> = encodings.into_iter().map(|e| e.canonicalize()).collect();

    info!("Sorting and deduplicating {} encodings", encodings.len());
    encodings.sort_by_cached_key(|e| *e.instr());
    encodings.dedup();

    filter_overlapping_encodings(encodings)
}
