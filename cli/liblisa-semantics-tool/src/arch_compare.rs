use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::num::ParseIntError;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use itertools::Itertools;
use liblisa::arch::undef::{UndefProvider, UndefinedOutputs};
use liblisa::arch::x64::undef::IntelUndefWithXed;
use liblisa::arch::x64::X64Arch;
use liblisa::arch::Arch;
use liblisa::compare::{ComparisonMatrix, ComparisonResult, EncodingGroup, Rows};
use liblisa::encoding::indexed::IndexedEncodings;
use liblisa::encoding::{Encoding, EncodingWithFilters};
use liblisa::instr::{InstructionFilter, WithFilters};
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::semantics::Computation;
use liblisa::smt::z3::ThreadLocalZ3;
use liblisa::smt::{CacheHitCounter, CachedSolverProvider, FileCache, MemoryCache, SharedCache, SolverProvider};
use rand::seq::SliceRandom;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use crate::progress::{progress_data, Progress, ProgressUsize};

#[derive(Clone, Debug)]
pub(crate) struct ArchIndexGroup {
    ids: Vec<usize>,
}

impl FromStr for ArchIndexGroup {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut ids = Vec::new();
        for num in s.split(',') {
            ids.push(num.parse::<usize>()?);
        }

        Ok(ArchIndexGroup {
            ids,
        })
    }
}

#[derive(Clone, Debug, clap::Parser)]
/// Compares semantics of different architectures.
/// The comparison consists of multiple steps:
///
/// - Extract overlapping encodings using `compare-overlapping`.
/// - Split groups using `split-exact`.
/// - Compare groups using `compare`.
/// - View the results using `print-table` or `details`.
pub(crate) struct ArchCompareContainer {
    #[clap(subcommand)]
    pub inner: ArchCompare,
}

#[derive(Clone, Debug, clap::Parser)]
pub(crate) enum ArchCompare {
    /// Computes overlapping groups of encodings.
    ComputeOverlapping {
        #[clap(long)]
        /// The paths of the JSON files containing synthesized semantics.
        encodings: Vec<PathBuf>,

        #[clap(long)]
        /// The path to which the exactly overlapping groups will be written.
        output: PathBuf,

        #[clap(long)]
        /// An optional instruction filter.
        /// Only encodings which are (partially) covered by the filter are included in the result.
        /// When not specified, all encodings are included.
        filter: Option<InstructionFilter>,
    },
    /// Splits the overlapping groups of encodings into groups where each encoding covers the exact same instruction space.
    SplitExact {
        /// The output of `compute-overlapping`.
        data: PathBuf,

        #[clap(long)]
        /// A path to which the exactly split groups will be written.
        output: PathBuf,
    },
    /// Compares the exactly split groups.
    Compare {
        /// The output of `split-exact`.
        data: PathBuf,

        #[clap(long)]
        /// The path of a file that can be used as solver cache.
        /// For example, `/tmp/solver-cache.bin`.
        solver_cache: PathBuf,

        #[clap(long)]
        /// The path to which comparison results will be written.
        output: PathBuf,
    },
    /// Re-checks the non-equivalent groups again and updates the file in-place.
    /// This is only useful if the implementation of comparison changed.
    UpdateCompared {
        /// The path to the output of `compare`.
        data: PathBuf,
    },
    /// Prints the comparison results as a table.
    PrintTable {
        /// The path to the output of `compare`.
        data: PathBuf,

        #[clap(long)]
        /// When enabled, prints extra information about the table rows.
        debug: bool,

        #[clap(long)]
        /// When enabled, counts the outputs that aren't fully defined.
        count_undef: bool,
    },
    /// Prints all individual encodings in the comparison results.
    Details {
        /// The path to the output of `compare`.
        data: PathBuf,

        #[clap(long = "group", value_parser = ArchIndexGroup::from_str)]
        /// Filters by equivalence groups. For example: --groups 0 --groups 1,2 --groups 3,4
        groups: Vec<ArchIndexGroup>,

        #[clap(long = "group-index")]
        /// Filters by group indices.
        group_indices: Vec<usize>,

        #[clap(long)]
        /// When enabled, extra information is printed.
        verbose: bool,

        #[clap(long)]
        /// Re-runs the comparison for each printed group.
        with_comparison: bool,

        #[clap(long)]
        /// Filters by instruction filter.
        filter: Option<InstructionFilter>,

        #[clap(long)]
        /// Prints all encodings, even when equivalent.
        all_encodings: bool,

        #[clap(long)]
        /// Only prints differences when the encodings do not have undefined outputs.
        differences_without_undef: bool,

        #[clap(long)]
        /// Only prints encodings that have undefined outputs.
        undef_only: bool,
    },
    /// Exports the comparison results to a portable JSON file.
    Export {
        /// The path to the output of `compare`.
        data: PathBuf,

        #[clap(long)]
        /// The path of the JSON file to which the output will be written.
        output: PathBuf,

        #[clap(long)]
        /// Human-readable names of the architectures.
        /// The number of names specified here must match the number of JSON files initially provided to `compute-overlapping`.
        arch_names: Vec<String>,
    },
}

fn load_from_disk<A: Arch>(paths: &[PathBuf]) -> Vec<Vec<Encoding<A, SynthesizedComputation>>> {
    paths
        .par_iter()
        .map(|path| {
            let encodings: Vec<Encoding<A, SynthesizedComputation>> =
                serde_json::from_reader(BufReader::new(File::open(path).unwrap())).unwrap();

            encodings
        })
        .collect::<Vec<_>>()
}

fn build_filters<A: Arch, C: Computation + Send>(
    encodings_per_arch: Vec<Vec<Encoding<A, C>>>, paths: &[PathBuf],
) -> Vec<Vec<EncodingWithFilters<A, C>>> {
    encodings_per_arch.into_iter().enumerate().map(|(index, encodings)| {
        Progress::run(progress_data! {
            P<'a> {
                index: usize = index,
                paths: &'a [PathBuf] = paths,
                num_to_prepare: usize = encodings.len(),
                num_prepared: AtomicUsize = AtomicUsize::new(0),
            }, |f, p| write!(f, "Preparing {:?}: {} / {} encodings", p.paths[p.index], p.num_prepared.load(Ordering::Relaxed), p.num_to_prepare)
        }, |progress| {
            let encodings_with_filters = encodings.into_par_iter()
                .map(|e| {
                    let ef = EncodingWithFilters::new(e);
                    let mut filters = ef.filters.clone();
                    filters.sort();
                    progress.num_prepared.fetch_add(1, Ordering::Relaxed);

                    (ef, filters)
                })
                .collect::<Vec<_>>();

            let mut map = HashMap::new();
            for (encoding, filters) in encodings_with_filters.into_iter() {
                let _prev = map.insert(filters, encoding);
                // TODO: Assert no encodings with identical filters (= identical bitpatterns (= 2 encodings that describe the exact same instructions))
                // assert!(prev.is_none(), "Duplicate encoding in input file {index}: {} // {}", prev.as_ref().unwrap(), {
                //     let mut filters = prev.as_ref().unwrap().filters();
                //     filters.sort();    
                //     map.get(&filters).unwrap()
                // });
            }

            map.into_values().collect()
        })
    }).collect::<Vec<_>>()
}

const WRITE_BUF_SIZE: usize = 1024 * 1024; // 1 MiB

#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct GroupedEncodings<A: Arch, C: Computation> {
    groups: Vec<EncodingGroup>,
    encodings: IndexedEncodings<A, C>,
}

#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct GroupedEncodingsWithFilter<A: Arch, C: Computation> {
    groups: Vec<(EncodingGroup, InstructionFilter)>,
    encodings: IndexedEncodings<A, C>,
}

#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct ComparedEncodingGroups<A: Arch, C: Computation> {
    groups: Vec<(EncodingGroup, InstructionFilter, ComparisonMatrix)>,
    encodings: IndexedEncodings<A, C>,
}

fn encoding_outputs_are_fully_defined<A: Arch, C: Computation>(
    encodings: &IndexedEncodings<A, C>, group: &EncodingGroup, restrict: &InstructionFilter, undef: &impl UndefProvider<A>,
) -> bool {
    if group.encodings_per_arch.iter().flatten().any(|id| {
        encodings[id]
            .encoding
            .dataflows
            .output_dataflows()
            .any(|flow| flow.computation.is_none())
    }) {
        return false
    }

    let mut encodings = group
        .encodings_per_arch
        .iter()
        .flatten()
        .flat_map(|id| encodings[id].encoding.restrict_to(restrict).ok());
    let mut rng = rand::thread_rng();
    let any_undefined = encodings.any(|e| {
        let part_values = e.parts.iter().map(|_| None).collect::<Vec<_>>();
        let r = e.random_instrs(&part_values, &mut rng).take(1000).any(|instr| {
            UndefinedOutputs::of(instr.bytes(), undef)
                .map(|ud| !ud.is_empty())
                .unwrap_or(false)
        });

        r
    });

    !any_undefined
}

pub trait UndefForArch: Arch {
    fn get_provider() -> impl UndefProvider<Self>;
}

impl UndefForArch for X64Arch {
    fn get_provider() -> impl UndefProvider<Self> {
        IntelUndefWithXed
    }
}

impl ArchCompare {
    pub fn run<A: Arch + UndefForArch>(self) {
        let undef = A::get_provider();
        match self {
            ArchCompare::ComputeOverlapping {
                encodings,
                output,
                filter,
            } => {
                eprintln!("Loading...");
                eprintln!("Reading data from disk...");
                let encodings_per_arch = load_from_disk(&encodings);
                println!();

                eprintln!("Building filters...");
                let arches = build_filters(encodings_per_arch, &encodings);

                let arches = if let Some(filter) = filter {
                    arches
                        .into_iter()
                        .map(|v| {
                            v.into_iter()
                                .filter(|e| e.filters().iter().any(|f| f.overlaps(&filter)))
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                } else {
                    arches
                };

                let (encodings, arches) = {
                    let mut encodings = IndexedEncodings::default();
                    let arches = arches
                        .into_iter()
                        .map(|e| e.into_iter().map(|e| encodings.add(e)).collect::<Vec<_>>())
                        .collect::<Vec<_>>();
                    (encodings, arches)
                };

                eprintln!("Grouping by maximum overlap...");
                let encoding_groups = EncodingGroup::compute_from_arches(&encodings, arches);

                let num_single = encoding_groups
                    .iter()
                    .filter(|g| g.encodings_per_arch.iter().all(|e| e.len() <= 1))
                    .count();
                eprintln!("Groups with at most 1 encoding per architecture: {num_single}");

                eprintln!("Writing {output:?}...");

                bincode::serialize_into::<_, GroupedEncodings<A, SynthesizedComputation>>(
                    BufWriter::with_capacity(WRITE_BUF_SIZE, File::create(output).unwrap()),
                    &GroupedEncodings {
                        groups: encoding_groups,
                        encodings,
                    },
                )
                .unwrap();
            },
            ArchCompare::SplitExact {
                data,
                output,
            } => {
                let GroupedEncodings {
                    groups: encoding_groups,
                    encodings,
                } = bincode::deserialize_from::<_, GroupedEncodings<A, SynthesizedComputation>>(BufReader::new(
                    File::open(data).unwrap(),
                ))
                .unwrap();

                eprintln!("Computing all distinct encodings...");

                let num_groups = encoding_groups.len();
                let encoding_groups = {
                    let mut encoding_groups = encoding_groups;
                    // Try to ensure the 'difficult' groups end up in different processing slices.
                    encoding_groups.shuffle(&mut rand::thread_rng());

                    let start = Instant::now();
                    let split_filters = Progress::run(
                        progress_data! {
                            P {
                                num_processed: ProgressUsize = 0,
                                total: usize = encoding_groups.len(),
                            }, |f, P { num_processed, total }| write!(f, "Computing splitting filters: {num_processed:?} / {total} groups processed")
                        },
                        |progress| {
                            encoding_groups
                                .par_iter()
                                // By setting a low max_len we're adding some overhead, but reduce the chance two difficult groups end up in the same processing slice
                                .with_max_len(1)
                                .flat_map(|group| {
                                    progress.num_processed.increment();
                                    group.split_exact(&encodings)
                                })
                                .collect::<Vec<_>>()
                        },
                    );
                    eprintln!("Computing split filters took {}s", start.elapsed().as_millis() / 1000);
                    split_filters
                };

                eprintln!("Split {num_groups} into {} exact groups", encoding_groups.len());
                eprintln!("Writing {output:?}...");
                bincode::serialize_into::<_, GroupedEncodingsWithFilter<A, SynthesizedComputation>>(
                    BufWriter::with_capacity(WRITE_BUF_SIZE, File::create(output).unwrap()),
                    &GroupedEncodingsWithFilter {
                        groups: encoding_groups,
                        encodings,
                    },
                )
                .unwrap();
            },
            ArchCompare::Compare {
                data,
                output,
                solver_cache,
            } => {
                let GroupedEncodingsWithFilter {
                    groups: encoding_groups,
                    encodings,
                } = bincode::deserialize_from::<_, GroupedEncodingsWithFilter<A, SynthesizedComputation>>(BufReader::new(
                    File::open(data).unwrap(),
                ))
                .unwrap();

                let solver_cache = FileCache::new(&solver_cache);
                let solver_cache = CacheHitCounter::new(solver_cache);
                let solver_cache = SharedCache::new(solver_cache);
                let solver = CachedSolverProvider::new(&solver_cache, ThreadLocalZ3::new(Duration::from_secs(900)));

                let results = run_comparisons(&solver, encoding_groups, &encodings);

                println!("Writing results...");
                bincode::serialize_into::<_, ComparedEncodingGroups<A, SynthesizedComputation>>(
                    BufWriter::with_capacity(WRITE_BUF_SIZE, File::create(output).unwrap()),
                    &ComparedEncodingGroups {
                        groups: results,
                        encodings,
                    },
                )
                .unwrap();
            },
            ArchCompare::UpdateCompared {
                data,
            } => {
                let ComparedEncodingGroups {
                    groups: encoding_groups,
                    encodings,
                } = bincode::deserialize_from::<_, ComparedEncodingGroups<A, SynthesizedComputation>>(BufReader::new(
                    File::open(&data).unwrap(),
                ))
                .unwrap();

                let (groups_to_compare, groups_to_skip) = encoding_groups.into_iter().partition::<Vec<_>, _>(|(_, _, matrix)| {
                    matrix
                        .iter_all()
                        .any(|item| item != ComparisonResult::Equal && item != ComparisonResult::BothMissing)
                });
                let groups_to_compare = groups_to_compare
                    .into_iter()
                    .map(|(group, filter, _)| (group, filter))
                    .collect::<Vec<_>>();

                let solver_cache = SharedCache::new(MemoryCache::new());
                let solver = CachedSolverProvider::new(&solver_cache, ThreadLocalZ3::new(Duration::from_secs(900)));

                let mut results = run_comparisons(&solver, groups_to_compare, &encodings);
                results.extend(groups_to_skip);

                println!("Writing results...");
                bincode::serialize_into::<_, ComparedEncodingGroups<A, SynthesizedComputation>>(
                    BufWriter::with_capacity(WRITE_BUF_SIZE, File::create(data).unwrap()),
                    &ComparedEncodingGroups {
                        groups: results,
                        encodings,
                    },
                )
                .unwrap();
            },
            ArchCompare::PrintTable {
                data,
                debug,
                count_undef,
            } => {
                let ComparedEncodingGroups {
                    groups,
                    encodings,
                } = bincode::deserialize_from::<_, ComparedEncodingGroups<A, SynthesizedComputation>>(BufReader::new(
                    File::open(data).unwrap(),
                ))
                .unwrap();
                let num_arches = groups[0].0.encodings_per_arch.len();
                let (groups, partials) = groups
                    .into_iter()
                    .partition(|(group, ..)| group.all_encodings_have_computations(&encodings));
                let rows = Rows::build(groups);

                eprintln!();
                println!();

                let mut seen = HashSet::new();
                for (index, row) in rows.into_iter().enumerate() {
                    let key = row.key();
                    let num_groups = *row.min_encoding_counts().iter().filter(|&&n| n != 0).min().unwrap_or(&0);
                    let groups = row.groups();
                    let groupname = format!("Group {index}");

                    let num_with_undef = if count_undef {
                        groups
                            .iter()
                            .filter(|(group, restrict, _)| {
                                !encoding_outputs_are_fully_defined(&encodings, group, restrict, &undef)
                            })
                            .map(|(group, ..)| group.encodings_per_arch.clone())
                            .reduce(|mut a, b| {
                                for (a, b) in a.iter_mut().zip(b.into_iter()) {
                                    a.extend(b);
                                }

                                a
                            })
                            .unwrap_or_else(Vec::new)
                            .iter()
                            .map(|v| v.iter().collect::<HashSet<_>>().len())
                            .min()
                            .unwrap_or(0)
                    } else {
                        0
                    };

                    let (sets, _missing) = key.extract_sets(num_arches);
                    let sets_text = (0..num_arches)
                        .map(|a| sets.iter().position(|s| s.contains(&a)))
                        .map(|n| match n {
                            Some(n) => format!("\\Impl{}$", ["X", "Y", "Z", "W", "V"][n]),
                            None => String::from("-"),
                        })
                        .join(" & ");
                    if !seen.insert(sets.clone()) {
                        println!("% NOTE: We saw this group configuration before...");
                    }

                    print!("{groupname:10} & \\num{{{num_groups:>5}}} & {sets_text}");
                    if count_undef {
                        print!(" & {num_with_undef:>8}");
                    }
                    println!(" \\\\");

                    if debug {
                        println!("     - Row configuration: 0x{:X}", key.repr());
                        println!(
                            "     - Matrixes: {:?}",
                            groups.iter().map(|(_, _, matrix)| matrix).unique().format(", ")
                        );
                    }
                }

                let num_partial_encodings = (0..num_arches)
                    .map(|index| {
                        partials
                            .iter()
                            .flat_map(|(group, ..)| group.encodings_per_arch[index].iter())
                            .unique()
                            .count()
                    })
                    .filter(|&n| n != 0)
                    .min()
                    .unwrap_or(0);

                println!("Synthesis failed & {num_partial_encodings} & - & - \\\\");
            },
            ArchCompare::Details {
                data,
                groups,
                group_indices,
                verbose,
                with_comparison,
                filter,
                all_encodings,
                differences_without_undef,
                undef_only,
            } => {
                let selector = groups
                    .into_iter()
                    .map(|g| {
                        let mut v = g.ids;
                        v.sort();
                        v
                    })
                    .sorted()
                    .collect::<Vec<_>>();

                let ComparedEncodingGroups {
                    groups,
                    encodings,
                } = bincode::deserialize_from::<_, ComparedEncodingGroups<A, SynthesizedComputation>>(BufReader::new(
                    File::open(data).unwrap(),
                ))
                .unwrap();
                let num_arches = groups[0].0.encodings_per_arch.len();
                let (groups, _partials) = groups
                    .into_iter()
                    .partition(|(group, ..)| group.all_encodings_have_computations(&encodings));
                let rows = Rows::build(groups);

                let solver_cache = SharedCache::new(MemoryCache::new());
                let solver = CachedSolverProvider::new(&solver_cache, ThreadLocalZ3::new(Duration::from_secs(900)));

                let mut num_printed = 0;

                if let Some(filter) = &filter {
                    println!("Only printing results overlapping with {filter:?}");
                }

                for (row_index, row) in rows.into_iter().enumerate() {
                    let groups = row.groups();
                    let key = row.key();
                    if !group_indices.is_empty() && !group_indices.contains(&row_index) {
                        continue
                    }

                    let (sets, _) = key.extract_sets(num_arches);
                    if selector.is_empty() || sets == selector {
                        println!("Sets: {sets:?}");
                        for (group_index, (group, restrict, original_matrix)) in groups.iter().enumerate() {
                            if let Some(filter) = &filter {
                                if !group
                                    .encodings_per_arch
                                    .iter()
                                    .flatten()
                                    .any(|id| encodings[id].encoding.bitpattern_as_filter().overlaps(filter))
                                {
                                    continue
                                }
                            }

                            if differences_without_undef
                                && !encoding_outputs_are_fully_defined(&encodings, group, restrict, &undef)
                            {
                                continue
                            }

                            if undef_only && encoding_outputs_are_fully_defined(&encodings, group, restrict, &undef) {
                                continue
                            }

                            if group.has_encodings_overlapping_filter(&encodings, restrict) {
                                num_printed += 1;
                                for (arch_index, (ids, implementation_index)) in group
                                    .encodings_per_arch
                                    .iter()
                                    .zip(key.implementation_indices(num_arches))
                                    .enumerate()
                                {
                                    for (encoding_index, id) in ids.iter().enumerate() {
                                        print!(
                                            "EncodingGroup #{group_index}, architecture #{arch_index}, encoding #{encoding_index}: "
                                        );
                                        match implementation_index {
                                            Some(implementation_index) if implementation_index == arch_index || all_encodings => {
                                                let encoding = encodings[id].encoding.restrict_to(restrict).unwrap();

                                                println!("{encoding}");

                                                if verbose {
                                                    println!("{:?}", encodings[id]);
                                                    println!("{:?}", encodings[id].filters);
                                                }
                                            },
                                            Some(implementation_index) => {
                                                println!("see architecture #{implementation_index:?}")
                                            },
                                            None => println!("-"),
                                        }
                                    }
                                }

                                if with_comparison {
                                    let matrix = group.compare(&encodings, restrict, &solver);

                                    println!("Comparison matrix: {matrix:?}");
                                    println!("Stored comparison matrix: {original_matrix:?}");
                                }
                            }
                        }
                    }
                }

                println!("Printed {num_printed} groups");
            },
            ArchCompare::Export {
                data,
                output,
                arch_names,
            } => {
                let ComparedEncodingGroups {
                    groups,
                    encodings,
                } = bincode::deserialize_from::<_, ComparedEncodingGroups<A, SynthesizedComputation>>(BufReader::new(
                    File::open(data).unwrap(),
                ))
                .unwrap();
                let num_arches = groups[0].0.encodings_per_arch.len();
                assert_eq!(arch_names.len(), num_arches);

                let rows = Rows::build(groups);

                println!("Building summary...");
                let summary = rows.export_summary(arch_names, encodings);

                println!("Writing results...");
                serde_json::to_writer(BufWriter::new(File::create(output).unwrap()), &summary).unwrap();
            },
        }
    }
}

fn run_comparisons<A: Arch>(
    solver: &impl SolverProvider, encoding_groups: Vec<(EncodingGroup, InstructionFilter)>,
    encodings: &IndexedEncodings<A, SynthesizedComputation>,
) -> Vec<(EncodingGroup, InstructionFilter, ComparisonMatrix)> {
    let encoding_groups = {
        let mut encoding_groups = encoding_groups;
        encoding_groups.shuffle(&mut rand::thread_rng());
        encoding_groups
    };

    Progress::run(
        progress_data! {
            P {
                total_groups: usize = encoding_groups.len(),
                num_compared: AtomicUsize = AtomicUsize::new(0),
                num_equivalent: AtomicUsize = AtomicUsize::new(0),
                start: Instant = Instant::now(),
            }, |f, P { start, total_groups, num_compared, num_equivalent }| {
                let num_compared = num_compared.load(Ordering::Relaxed);
                let elapsed = start.elapsed();
                let duration_per_group = elapsed.checked_div(num_compared.try_into().unwrap()).unwrap_or(Duration::ZERO);
                let remaining = duration_per_group * (total_groups - num_compared).try_into().unwrap();
                write!(f, "Checking equivalence: {:3.1}% - {num_compared} / {total_groups} groups - {}m remaining - {num_equivalent:?} / {total_groups} equivalent", num_compared as f64 * 100.0 / *total_groups as f64, remaining.as_secs() / 60)
            }
        },
        |progress| {
            encoding_groups
                .into_par_iter()
                .with_max_len(1)
                .map(|(group, filter)| {
                    let comparison_matrix = group.compare(encodings, &filter, solver);
                    progress.num_compared.fetch_add(1, Ordering::Relaxed);

                    if comparison_matrix
                        .iter_all()
                        .all(|r| r == ComparisonResult::Equal || r == ComparisonResult::BothMissing)
                    {
                        progress.num_equivalent.fetch_add(1, Ordering::Relaxed);
                    }

                    (group, filter, comparison_matrix)
                })
                .collect::<Vec<_>>()
        },
    )
}
