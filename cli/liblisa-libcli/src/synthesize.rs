use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::marker::PhantomData;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, RecvTimeoutError};
use std::sync::Mutex;
use std::thread::{scope, spawn};
use std::time::{Duration, Instant};

use liblisa::arch::Arch;
use liblisa::encoding::Encoding;
use liblisa::oracle::{Oracle, OracleSource};
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa_synth::{merge_semantics_into_encoding, prepare_templates, DefaultTreeTemplateSynthesizer};
use nix::sched::CpuSet;

use crate::clear_screen;
use crate::threadpool::synthesis::{Synthesis, SynthesisArtifact, SynthesisRuntimeData};
use crate::threadpool::ThreadPool;

#[derive(Copy, Clone, Debug, clap::ValueEnum)]
enum SortBy {
    Duration,
}

#[derive(Clone, Debug, clap::Parser)]
#[clap(verbatim_doc_comment)]
/// Synthesize semantics for a set of encodings.
///
/// Since synthesis can take a long time, intermediate state is saved in a working directory.
/// This working directory can be created using the `create` subcommand.
/// After creating the working directory, synthesis can be run using the `run` subcommand.
///
/// When synthesis is complete, the synthesized semantics can be extracted using the `extract` subcommand.
enum Verb {
    Create {
        encodings: PathBuf,
    },
    Run {
        #[clap(long)]
        threads: Option<usize>,

        #[clap(
            long,
            help = "ramps the number of threads up to this value by adding 4 threads every 15 minutes"
        )]
        ramp_up: Option<usize>,
    },
    Status {
        #[clap(long)]
        watch: bool,

        #[clap(short = 't', long)]
        time: Option<u64>,
    },
    Extract {
        output: PathBuf,

        #[clap(long)]
        include_partial: bool,

        #[clap(long)]
        include_unprocessed: bool,
    },
    ExtractFailed {
        output: PathBuf,

        #[clap(long)]
        exclude_unprocessed: bool,
    },
    Dump {
        #[clap(long)]
        hide_complete: bool,

        #[clap(long)]
        hide_failed: bool,

        #[clap(long)]
        show_unprocessed: bool,

        #[clap(long)]
        json: bool,

        #[clap(long)]
        sort_by: Option<SortBy>,
    },
}

/// Runs synthesis.
#[derive(Clone, Debug, clap::Parser)]
pub struct SynthesizeCommand<A> {
    dir: PathBuf,

    #[clap(long)]
    override_encodings_path: Option<PathBuf>,

    #[clap(subcommand)]
    verb: Verb,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SynthesizeCommand<A> {
    fn save_state<S>(&self, state: &Synthesis<S>) {
        {
            let file = File::create(self.tmp_state_path()).unwrap();
            serde_json::to_writer(file, state).unwrap();
        }

        fs::rename(self.tmp_state_path(), self.state_path()).unwrap();
    }

    fn load_synthesis_and_encodings(
        &self,
    ) -> (
        Synthesis<DefaultTreeTemplateSynthesizer>,
        Vec<Encoding<A, SynthesizedComputation>>,
    ) {
        let file = File::open(self.state_path()).unwrap();
        let synthesis: Synthesis<DefaultTreeTemplateSynthesizer> = serde_json::from_reader(file).unwrap();
        let encodings: Vec<Encoding<A, ()>> = serde_json::from_reader(BufReader::new(
            File::open(self.override_encodings_path.as_ref().unwrap_or(&synthesis.encodings_path)).unwrap(),
        ))
        .unwrap();
        let encodings: Vec<Encoding<A, SynthesizedComputation>> = encodings
            .into_iter()
            .map(|encoding| encoding.map_computations(|_, _| None))
            .collect::<Vec<_>>();

        (synthesis, encodings)
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

    pub fn run<S: OracleSource>(&self, create_oracle_source: impl FnMut(CpuSet) -> S)
    where
        S::Oracle: Oracle<A> + Send,
    {
        match &self.verb {
            Verb::Create {
                encodings: encodings_path,
            } => {
                fs::create_dir_all(&self.dir).unwrap();
                let encodings: Vec<Encoding<A, ()>> =
                    serde_json::from_reader(BufReader::new(File::open(encodings_path).unwrap())).unwrap();

                let synthesis: Synthesis<DefaultTreeTemplateSynthesizer> =
                    Synthesis::create(encodings_path.clone(), encodings.len());
                let file = File::create(self.state_path()).unwrap();
                serde_json::to_writer(file, &synthesis).unwrap();

                // Clear the artifacts file that might still store previous entries
                File::create(self.artifact_path()).unwrap();
            },
            Verb::Run {
                threads,
                mut ramp_up,
            } => {
                println!("Loading base data...");
                let file = File::open(self.state_path()).unwrap();
                let synthesis: Synthesis<DefaultTreeTemplateSynthesizer> = serde_json::from_reader(file).unwrap();
                let encodings: Vec<Encoding<A, ()>> = serde_json::from_reader(BufReader::new(
                    File::open(self.override_encodings_path.as_ref().unwrap_or(&synthesis.encodings_path)).unwrap(),
                ))
                .unwrap();
                let synthesis: Mutex<(Synthesis<DefaultTreeTemplateSynthesizer>, SynthesisRuntimeData<_>)> = Mutex::new({
                    let runtime_data = SynthesisRuntimeData {
                        last_check: Instant::now(),
                        encodings: &encodings,
                        pending: Vec::new(),
                        second_chances: HashSet::new(),
                    };
                    (synthesis, runtime_data)
                });

                let artifact_file = Mutex::new(BufWriter::new(
                    File::options().append(true).create(true).open(self.artifact_path()).unwrap(),
                ));

                let save_artifact = move |artifact| {
                    let mut w = artifact_file.lock().unwrap();
                    serde_json::to_writer(&mut *w, &artifact).unwrap();
                    writeln!(w).unwrap();
                    w.flush().unwrap();
                };

                // Do the work to const-expand the templates upfront, so it doesn't count against the synthesis time.
                println!("Preparing templates...");
                prepare_templates();
                println!("Templates prepared!");

                let (send, recv) = channel();
                spawn(|| {
                    for line in std::io::stdin().lines() {
                        send.send(line).unwrap();
                    }

                    drop(send);
                });

                let running = AtomicBool::new(true);
                scope(|scope| -> Result<(), Box<dyn Error>> {
                    scope.spawn(|| {
                        let mut last_save = Instant::now();
                        while running.load(Ordering::SeqCst) {
                            std::thread::sleep(Duration::from_secs(5));

                            if last_save.elapsed() >= Duration::from_secs(30) {
                                self.save_state(&synthesis.lock().unwrap().0);
                                last_save = Instant::now();
                            }
                        }
                    });

                    {
                        let mut pool = ThreadPool::from_work(scope, create_oracle_source, &(), &synthesis, &save_artifact);

                        // TODO: Automatically determine the right size
                        pool.resize(threads.unwrap_or(2));

                        let mut last_ramp_up = Instant::now();
                        loop {
                            match recv.recv_timeout(Duration::from_secs(5)) {
                                Ok(line) => {
                                    let line = line?;
                                    let command = line.split(' ').map(str::trim).collect::<Vec<_>>();
                                    match &command[..] {
                                        ["stop"] => break,
                                        ["threads", num] => match num.parse::<usize>() {
                                            Ok(num) => {
                                                println!("Resizing thread pool to {num}...");
                                                pool.resize(num);
                                                println!("Thread pool resized to {num}");

                                                if ramp_up.take().is_some() {
                                                    println!("Ramp-up cancelled because of manual input");
                                                }
                                            },
                                            Err(e) => println!("{e}"),
                                        },
                                        _ => println!("Commands available: stop"),
                                    }
                                },
                                Err(RecvTimeoutError::Disconnected) => break,
                                Err(RecvTimeoutError::Timeout) => (),
                            }

                            if last_ramp_up.elapsed() >= Duration::from_secs(30 * 60) {
                                if let Some(ramp_up) = ramp_up {
                                    let current = pool.current_num_threads();
                                    let new_num = (current + 4).min(ramp_up);
                                    pool.resize(new_num);
                                }

                                last_ramp_up = Instant::now();
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
                self.save_state(&synthesis.lock().unwrap().0);

                println!("OK!");
            },
            Verb::Status {
                watch,
                time,
            } => {
                println!("Loading base data...");
                let file = File::open(self.state_path()).unwrap();
                let synthesis: Synthesis<DefaultTreeTemplateSynthesizer> = serde_json::from_reader(file).unwrap();
                let encodings: Vec<Encoding<A, ()>> = serde_json::from_reader(BufReader::new(
                    File::open(self.override_encodings_path.as_ref().unwrap_or(&synthesis.encodings_path)).unwrap(),
                ))
                .unwrap();

                if *watch {
                    loop {
                        // TODO: Watch artifacts file and reload on write!
                        let file = File::open(self.state_path()).unwrap();
                        let synthesis: Synthesis<DefaultTreeTemplateSynthesizer> = serde_json::from_reader(file).unwrap();
                        let artifacts = self.load_artifacts().unwrap();
                        clear_screen();
                        Self::print_status(&encodings, &artifacts, &synthesis);

                        if let Some(time) = time {
                            std::thread::sleep(Duration::from_secs(*time));
                        } else {
                            std::io::stdin().read_line(&mut String::new()).unwrap();
                        }
                    }
                } else {
                    let artifacts = self.load_artifacts().unwrap();
                    Self::print_status(&encodings, &artifacts, &synthesis);
                }
            },
            Verb::Extract {
                output,
                include_partial,
                include_unprocessed,
            } => {
                if !include_partial {
                    todo!("extract without --partial flag is not supported yet");
                }
                let (_, encodings) = self.load_synthesis_and_encodings();
                let artifacts = self.load_artifacts().unwrap();

                println!("Processing artifacts...");
                let semantics = Self::artifacts_to_semantics(artifacts, &encodings, *include_unprocessed);

                println!("Writing results...");
                serde_json::to_writer(BufWriter::new(File::create(output).unwrap()), &semantics).unwrap();
            },
            Verb::ExtractFailed {
                output,
                exclude_unprocessed,
            } => {
                let (_, encodings) = self.load_synthesis_and_encodings();
                let artifacts = self.load_artifacts().unwrap();

                println!("Processing artifacts...");
                let mut semantics = Self::artifacts_to_semantics(artifacts, &encodings, !exclude_unprocessed);
                semantics.retain(|e| e.dataflows.output_dataflows().any(|f| f.computation.is_none()));
                semantics.sort_by_key(|e| e.dataflows.output_dataflows().count());

                println!("Writing results...");
                serde_json::to_writer(BufWriter::new(File::create(output).unwrap()), &semantics).unwrap();
            },
            Verb::Dump {
                hide_complete,
                hide_failed,
                sort_by,
                json,
                show_unprocessed,
            } => {
                let (_, original_encodings) = self.load_synthesis_and_encodings();
                let artifacts = self.load_artifacts().unwrap();

                let mut seen = GrowingBitmap::new();
                let mut encodings = artifacts
                    .iter()
                    .map(|artifact| {
                        let encoding = original_encodings[artifact.encoding_index].clone();
                        let encoding = merge_semantics_into_encoding(encoding, artifact.computations.clone());
                        let num_synthesized = encoding
                            .dataflows
                            .output_dataflows()
                            .filter(|output| output.computation.is_some())
                            .count();
                        let complete = encoding
                            .dataflows
                            .output_dataflows()
                            .all(|output| output.computation.is_some());
                        let partial = encoding
                            .dataflows
                            .output_dataflows()
                            .any(|output| output.computation.is_some());

                        seen.set(artifact.encoding_index);

                        (encoding, artifact.ms_taken, num_synthesized, complete, partial)
                    })
                    .collect::<Vec<_>>();

                if *show_unprocessed {
                    for (index, encoding) in original_encodings.iter().enumerate() {
                        if !seen[index] {
                            encodings.push((encoding.clone(), 0, 0, false, false))
                        }
                    }
                }

                // encodings.retain(|&(_, num_synthesized, _, _)| num_synthesized > 0);
                if *hide_complete {
                    encodings.retain(|&(_, _, _, complete, _)| !complete);
                }

                if *hide_failed {
                    encodings.retain(|&(_, _, _, _, partial)| partial);
                }

                match sort_by {
                    Some(SortBy::Duration) => encodings.sort_by_key(|(_, ms_taken, ..)| *ms_taken),
                    None => encodings.sort_by_key(|(encoding, _, num_synthesized, ..)| {
                        encoding.dataflows.output_dataflows().count() - *num_synthesized
                    }),
                }

                for (encoding, ms_taken, num_synthesized, complete, _) in encodings.into_iter() {
                    if complete {
                        println!("Complete:");
                    } else {
                        println!("Partial({num_synthesized}):");
                    }

                    println!("    in {}s", ms_taken / 1000);

                    println!("{encoding}");

                    if *json {
                        println!("{}", serde_json::to_string(&encoding).unwrap());
                    }

                    println!();
                }
            },
        }
    }

    fn artifacts_to_semantics(
        artifacts: Vec<SynthesisArtifact<SynthesizedComputation>>, encodings: &[Encoding<A, SynthesizedComputation>],
        include_unprocessed: bool,
    ) -> Vec<Encoding<A, SynthesizedComputation>> {
        let mut seen = GrowingBitmap::new();
        let mut semantics = HashMap::<usize, Encoding<A, SynthesizedComputation>>::new();

        for artifact in artifacts.into_iter() {
            let encoding = encodings[artifact.encoding_index].clone();
            seen.set(artifact.encoding_index);
            let mut encoding = merge_semantics_into_encoding(encoding, artifact.computations);
            encoding.write_ordering = artifact.write_ordering;

            if let Some(prev) = semantics.get(&artifact.encoding_index) {
                let prev_computation_count = prev.dataflows.output_dataflows().filter(|f| f.computation.is_some()).count();
                let new_computation_count = encoding
                    .dataflows
                    .output_dataflows()
                    .filter(|f| f.computation.is_some())
                    .count();
                if prev_computation_count < new_computation_count {
                    semantics.insert(artifact.encoding_index, encoding);
                }
            } else {
                semantics.insert(artifact.encoding_index, encoding);
            }
        }

        let mut semantics = semantics.into_values().collect::<Vec<_>>();

        if include_unprocessed {
            for (index, encoding) in encodings.iter().enumerate() {
                if !seen[index] {
                    semantics.push(encoding.clone());
                }
            }
        }

        semantics
    }

    fn print_status<S>(
        encodings: &[Encoding<A, ()>], artifacts: &[SynthesisArtifact<SynthesizedComputation>], synthesis: &Synthesis<S>,
    ) {
        let mut encodings_processed = GrowingBitmap::new_all_zeros(encodings.len());
        let mut encodings_complete = GrowingBitmap::new_all_zeros(encodings.len());
        let mut encodings_partial = GrowingBitmap::new_all_zeros(encodings.len());
        for artifact in artifacts.iter() {
            if artifact.computations.iter().all(|c| c.computation.is_some()) {
                encodings_complete.set(artifact.encoding_index);
            } else if artifact.computations.iter().any(|c| c.computation.is_some()) {
                encodings_partial.set(artifact.encoding_index);
            }

            encodings_processed.set(artifact.encoding_index);
        }

        let num_timed_out = artifacts.iter().filter(|a| a.ms_taken >= 90_000).count();

        let num_encodings = encodings.len();
        let num_artifacts = artifacts.len();
        let num_processed = encodings_processed.count_ones();
        let seconds_running = synthesis.runtime_ms / 1000;
        let hours_running = seconds_running as f64 / 3600.0;
        let artifacts_per_hour = num_artifacts as f64 / hours_running;
        println!(
            "Processed {num_processed} / {num_encodings} encodings in {hours_running:.1}h; {num_artifacts} artifacts ({artifacts_per_hour:.1}/hr)"
        );
        println!("Timeouts: {num_timed_out}");

        let num_failed = encodings_partial.count_zeros();
        let num_partial = encodings_partial.count_ones();
        let num_complete = encodings_complete.count_ones();
        println!(
            "{num_partial} encodings are partially complete, {num_complete} encodings are complete, {num_failed} encodings failed completely"
        );
        let percentage_complete = num_complete as f64 * 100.0 / encodings.len() as f64;
        println!(
            "Encodings with complete computations: {percentage_complete:.2}% ({num_complete} / {})",
            encodings.len()
        );
        let success_rate = num_complete as f64 * 100.0 / num_processed as f64;
        println!("Success rate: {success_rate:.2}%");

        for goal in [50.0, 60.0, 70.0, 75.0, 80.0, 85.0, 86.0, 87.0, 88.0, 89.0, 90.0, 95.0, 99.0] {
            if success_rate < goal {
                let num_needed = Self::compute_success_rate_goal(success_rate, goal, num_processed);

                if num_needed < (encodings.len() - artifacts.len()) as u64 {
                    println!("  (to get a {goal:.2}% success rate, the next {num_needed} encodings must be complete)");
                } else {
                    println!("  (it is not possible to reach a {goal:.2}% success rate)");
                    break
                }
            }
        }

        let remaining = (num_encodings - num_processed) as f64 / artifacts_per_hour;
        let percent = num_processed as f64 * 100.0 / num_encodings as f64;
        println!("Progress: {percent:.1}% - {remaining:.1}h remaining");
    }

    fn compute_success_rate_goal(success_rate: f64, goal: f64, num_artifacts: usize) -> u64 {
        // success_rate * num_artifacts + x = goal * (num_artifacts + x)
        // success_rate * num_artifacts + x = goal * num_artifacts + goal * x
        // success_rate * num_artifacts - goal * num_artifacts = (goal - 1) * x
        // (success_rate - goal) * num_artifacts / (goal - 1) = x

        let num_artifacts = num_artifacts as f64;
        let x = (success_rate - goal) / 100.0 * num_artifacts / (goal / 100.0 - 1.0);

        x as u64
    }

    fn load_artifacts(&self) -> Result<Vec<SynthesisArtifact<SynthesizedComputation>>, Box<dyn Error>> {
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
}
