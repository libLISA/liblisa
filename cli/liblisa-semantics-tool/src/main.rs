use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use arch_compare::ArchCompareContainer;
use clap::Parser;
use itertools::Itertools;
use liblisa::arch::x64::X64Arch;
use liblisa::arch::Arch;
use liblisa::encoding::Encoding;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::Instruction;
use log::trace;
use merge::Merge;
use schemars::{schema_for, JsonSchema};

// TODO: Expand this into a tool that can search through encodings based on a query.
// TODO: query: overlapping ouputs?
// TODO: query: can write to RAX?
// TODO: query: writes to rip but it's not `rip + instruction_length`?

pub mod arch_compare;
pub mod merge;
pub mod progress;
pub mod server;

#[derive(Clone, Debug, clap::Parser)]
enum Verb {
    /// Queries semantics stored in a JSON file.
    Get {
        /// The path to the raw semantics.
        encodings: PathBuf,

        /// The operation to perform.
        #[clap(subcommand)]
        property: Property,
    },
    /// Prints the JSON schema of the raw encodings.
    Schema,
    ArchCompare(#[clap(subcommand)] ArchCompareContainer),
    Merge(Merge),
    Server(#[clap(subcommand)] server::Server),
}

#[derive(Clone, Debug, clap::Parser)]
enum Property {
    /// Prints general statistics.
    Stats,

    /// Prints the encodings with unobservable outputs.
    UnobservableOutputs,

    /// Prints the encodings with overlapping outputs.
    OverlappingOutputs,

    /// Prints the encodings with >128-bit outputs.
    BigOutputs,

    /// Prints the encodings without synthesized semantics.
    FailedSynthesis,

    /// Prints the bitpatterns of all encodings.
    Bitpatterns,

    /// Prints all encodings. (NOTE: This will print millions of lines of text)
    FullEncodings {
        #[clap(long, default_value = "0")]
        min_access_count: usize,
    },

    /// Prints all encodings that match `instr`.
    /// This will generally only be a single encoding.
    Encoding {
        /// The instruction that should be matched by the encoding.
        instr: Instruction,
    },
}

#[derive(Copy, Clone, Debug, Default, clap::ValueEnum)]
enum Architecture {
    #[default]
    X64,
}

#[derive(Clone, Debug, clap::Parser)]
struct Args {
    #[clap(long, default_value = "x64")]
    arch: Architecture,

    #[clap(subcommand)]
    verb: Verb,
}

pub fn main() {
    env_logger::init();

    let args = Args::parse();
    trace!("Args: {args:#?}");

    match args.arch {
        Architecture::X64 => run::<X64Arch>(args),
    }
}

fn run<A: Arch + JsonSchema + arch_compare::UndefForArch>(args: Args)
where
    <A as Arch>::Reg: JsonSchema,
{
    match args.verb {
        Verb::Get {
            encodings,
            property,
        } => {
            eprintln!("Loading {:?}...", encodings);
            let encodings: Vec<Encoding<A, SynthesizedComputation>> =
                serde_json::from_reader(BufReader::new(File::open(&encodings).unwrap())).unwrap();

            eprintln!("Loaded {} encodings", encodings.len());
            match property {
                Property::Stats => {
                    println!("Encodings: {}", encodings.len());
                    println!(
                        "Synthesized: {}",
                        encodings.iter().filter(|e| e.all_outputs_have_computations()).count()
                    );
                },
                Property::UnobservableOutputs => {
                    for encoding in encodings.iter() {
                        if encoding.dataflows.outputs.iter().any(|o| o.unobservable_external_inputs) {
                            println!("Encoding with unobservable inputs: {encoding}");
                        }
                    }
                },
                Property::OverlappingOutputs => {
                    let mut candidate_encodings = encodings
                        .iter()
                        .flat_map(|e| {
                            let num = e.overlapping_outputs().map(|(_, v)| v.len()).max();
                            num.map(|num| (e, num))
                        })
                        .collect::<Vec<_>>();
                    candidate_encodings.sort_by_key(|&(_, num)| num);

                    println!("{} encodings with overlapping outputs", candidate_encodings.len());

                    for (encoding, num_overlapping) in candidate_encodings.iter() {
                        println!("Encoding ({num_overlapping} overlapping): {encoding}");
                    }
                },
                Property::BigOutputs => {
                    let candidate_encodings = encodings
                        .iter()
                        .filter(|e| {
                            e.dataflows.output_dataflows().any(|o| {
                                o.target().size().num_bytes() > 16
                                    || o.inputs()
                                        .iter()
                                        .any(|i| i.size().map(|s| s.num_bytes() > 16).unwrap_or(false))
                            })
                        })
                        .collect::<Vec<_>>();

                    println!("{} encodings with overlapping outputs", candidate_encodings.len());

                    for encoding in candidate_encodings.iter() {
                        println!("Encoding: {encoding}");
                    }
                },
                Property::FailedSynthesis => {
                    let candidate_encodings = encodings
                        .iter()
                        .filter(|e| !e.all_outputs_have_computations())
                        .collect::<Vec<_>>();

                    println!("{} encodings with failed synthesis", candidate_encodings.len());

                    for encoding in candidate_encodings.iter() {
                        println!("Encoding: {encoding}");
                    }
                },
                Property::Encoding {
                    instr,
                } => {
                    for e in encodings.iter() {
                        if e.bitpattern_as_filter().matches(&instr) && e.filters().iter().any(|f| f.matches(&instr)) {
                            println!("{e}");
                        }
                    }
                },
                Property::FullEncodings {
                    min_access_count,
                } => {
                    let mut num_printed = 0;
                    for e in encodings.iter() {
                        if e.dataflows.addresses.len() > min_access_count {
                            num_printed += 1;
                            println!("{e}");
                        }
                    }

                    let num_ignored = encodings.len() - num_printed;
                    if num_ignored != 0 {
                        eprintln!("Printed {num_printed} encodings. Ignored {num_ignored} encodings that did not match filters");
                    }
                },
                Property::Bitpatterns => {
                    let mut num_bits = 0u128;
                    for e in encodings.iter() {
                        println!(
                            "{}",
                            e.bits
                                .iter()
                                .rev()
                                .chunks(8)
                                .into_iter()
                                .map(|byte| byte.into_iter().map(|s| format!("{s:?}")).join(""))
                                .join(" ")
                        );

                        num_bits += e.bits.len() as u128;
                    }

                    println!("Printed {num_bits} bits across {} encodings", encodings.len());
                },
            }
        },
        Verb::Schema => {
            let schema = schema_for!(Vec<Encoding<A, SynthesizedComputation>>);
            println!("{}", serde_json::to_string_pretty(&schema).unwrap());
        },
        Verb::ArchCompare(v) => v.inner.run::<A>(),
        Verb::Merge(v) => v.run::<A>(),
        Verb::Server(v) => v.run::<A>(),
    }
}
