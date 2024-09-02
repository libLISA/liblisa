use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use itertools::Itertools;
use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{AddrTermCalculation, AddrTermSize, Dataflows, Dest, Size, Source};
use liblisa::encoding::Encoding;
use liblisa::instr::{FilterMap, Instruction};
use liblisa::semantics::default::codegen::codegen_computation;
use liblisa::semantics::default::codegen::sexpr::{SExpr, SExprCodeGen};
use liblisa::semantics::default::computation::SynthesizedComputation;
use log::info;
use serde::{Deserialize, Serialize};

/// Allows you to query semantics via stdin/stdout.
///
/// The semantics server *instantiates* semantics: it fills the correct registers, flags and immediate values from parts in the encoding.
#[derive(Clone, Debug, clap::Parser)]
pub struct Server {
    /// The path of the JSON file that contains the encodings.
    encodings: PathBuf,

    #[clap(long = "debug")]
    /// When enabled, human-readable semantics are printed to stderr.
    ///
    /// The JSON schema is also printed.
    debug: bool,

    #[clap(long = "cache")]
    /// An optional path for a cache.
    /// If the path does not exist, the lookup table is generated normally and then written to this file.
    /// If the path exists, the lookup table is read directly the file.
    /// This significantly speeds up startup time.
    ///
    /// The cache is not portable between different versions of the semantics server.
    /// No verification is performed on the cache.
    /// You must ensure that you use a different file when using a different set of encodings.
    cache: Option<PathBuf>,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct TermRepr<A: Arch> {
    value: SourceRepr<A>,
    interpret_as: AddrTermSize,
    shift_right: u8,
    multiply_by: u8,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct AccessRepr<A: Arch> {
    byte_size: u64,
    sum_of: Vec<TermRepr<A>>,
    offset: i64,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct OutputRepr<A: Arch> {
    write_target: DestRepr<A>,
    inputs: Vec<SourceRepr<A>>,
    computation: SExpr,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct Repr<A: Arch> {
    memory: Vec<AccessRepr<A>>,
    write_targets: Vec<OutputRepr<A>>,
}

impl<A: Arch> TermRepr<A> {
    fn from_term(term: AddrTermCalculation, input: SourceRepr<A>) -> TermRepr<A> {
        TermRepr {
            value: input,
            interpret_as: term.size,
            shift_right: term.shift.right(),
            multiply_by: term.shift.mult(),
        }
    }
}

impl<A: Arch> Display for TermRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} >> {}) * {}", self.value, self.shift_right, self.multiply_by)
    }
}

#[derive(Copy, Clone, Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
enum DestRepr<A: Arch> {
    Reg { reg: A::Reg, size: Size },
    Mem { index: usize, size: Size },
}

impl<A: Arch> From<Dest<A>> for DestRepr<A> {
    fn from(value: Dest<A>) -> Self {
        match value {
            Dest::Reg(reg, size) => DestRepr::Reg {
                reg,
                size,
            },
            Dest::Mem(index, size) => DestRepr::Mem {
                index,
                size,
            },
        }
    }
}

impl<A: Arch> From<DestRepr<A>> for Dest<A> {
    fn from(value: DestRepr<A>) -> Self {
        match value {
            DestRepr::Reg {
                reg,
                size,
            } => Dest::Reg(reg, size),
            DestRepr::Mem {
                index,
                size,
            } => Dest::Mem(index, size),
        }
    }
}

impl<A: Arch> Debug for DestRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&Dest::<A>::from(*self), f)
    }
}

impl<A: Arch> Display for DestRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&Dest::<A>::from(*self), f)
    }
}

#[derive(Copy, Clone, Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
enum SourceRepr<A: Arch> {
    Dest(DestRepr<A>),
    Imm { index: usize },
    Const { value: u64, num_bits: usize },
}

impl<A: Arch> From<Source<A>> for SourceRepr<A> {
    fn from(value: Source<A>) -> Self {
        match value {
            Source::Dest(dest) => SourceRepr::Dest(dest.into()),
            Source::Imm(index) => SourceRepr::Imm {
                index,
            },
            Source::Const {
                value,
                num_bits,
            } => SourceRepr::Const {
                value,
                num_bits,
            },
        }
    }
}

impl<A: Arch> From<SourceRepr<A>> for Source<A> {
    fn from(value: SourceRepr<A>) -> Self {
        match value {
            SourceRepr::Dest(dest) => Source::Dest(dest.into()),
            SourceRepr::Imm {
                index,
            } => Source::Imm(index),
            SourceRepr::Const {
                value,
                num_bits,
            } => Source::Const {
                value,
                num_bits,
            },
        }
    }
}

impl<A: Arch> Debug for SourceRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&Source::<A>::from(*self), f)
    }
}

impl<A: Arch> Display for SourceRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&Source::<A>::from(*self), f)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "", deserialize = ""))]
struct Data<A: Arch> {
    encodings: Vec<Encoding<A, SynthesizedComputation>>,
    map: FilterMap<usize>,
}

fn build_filter_map<A: Arch>(encodings: &Path) -> Data<A> {
    eprintln!("Reading...");
    let encodings: Vec<Encoding<A, SynthesizedComputation>> =
        serde_json::from_reader(BufReader::new(File::open(encodings).unwrap())).unwrap();

    eprintln!("Building lookup table...");

    let mut map = FilterMap::new();
    for (index, e) in encodings.iter().enumerate() {
        for filter in e.filters() {
            map.add(filter, index);
        }
    }

    Data {
        encodings,
        map,
    }
}

impl Server {
    pub fn run<A: Arch + schemars::JsonSchema>(&self)
    where
        A::Reg: schemars::JsonSchema,
    {
        if self.debug {
            let schema = schemars::schema_for!(Repr<A>);
            eprintln!("Schema: {}", serde_json::to_string_pretty(&schema).unwrap());
        }

        let start = Instant::now();
        let map: Data<A> = if let Some(cache) = &self.cache {
            match File::open(cache) {
                Ok(file) => {
                    eprintln!("Loading cache from {cache:?}");
                    bincode::deserialize_from(BufReader::new(file)).unwrap()
                },
                Err(e) => {
                    eprintln!("Error reading {cache:?}: {e}");

                    let map = build_filter_map(&self.encodings);

                    eprintln!("Writing cache to {cache:?}");
                    bincode::serialize_into(BufWriter::new(File::create(cache).unwrap()), &map).unwrap();
                    map
                },
            }
        } else {
            build_filter_map(&self.encodings)
        };

        eprintln!("That took {}ms", start.elapsed().as_millis());
        eprintln!("Ready!");

        let stdin = std::io::stdin();
        let mut buf = String::new();

        while stdin.read_line(&mut buf).is_ok() {
            let instr = Instruction::from_str(&buf).unwrap();

            let result = map.map.filters(&instr).map(|&index| &map.encodings[index]);
            if let Some(e) = result {
                info!("Matched encoding: {e}");
            }

            let result = result.map(|encoding: &Encoding<_, _>| {
                let parts = encoding.extract_parts(&instr);
                encoding.instantiate(&parts).unwrap()
            });
            let result = result.and_then(|dataflow: Dataflows<_, _>| {
                if dataflow.output_dataflows().any(|o| o.computation.is_none()) {
                    None
                } else {
                    Some(Repr {
                        memory: dataflow
                            .addresses
                            .iter()
                            .map(|access| AccessRepr {
                                byte_size: access.size.end,
                                sum_of: access
                                    .inputs
                                    .iter()
                                    .zip(access.calculation.terms.iter())
                                    .flat_map(|(&input, term)| {
                                        [TermRepr::from_term(term.primary, input.into())].into_iter().chain(
                                            [term.second_use.map(|term| TermRepr::from_term(term, input.into()))]
                                                .into_iter()
                                                .flatten(),
                                        )
                                    })
                                    .collect(),
                                offset: access.calculation.offset,
                            })
                            .collect(),
                        write_targets: dataflow
                            .outputs
                            .iter()
                            .map(|output| {
                                let mut g = SExprCodeGen::new();
                                let computation = output.computation.as_ref().unwrap();
                                let computation = codegen_computation(&mut g, computation);

                                OutputRepr {
                                    write_target: output.target.into(),
                                    inputs: output.inputs.iter().cloned().map_into().collect(),
                                    computation,
                                }
                            })
                            .collect(),
                    })
                }
            });

            println!("{}", serde_json::to_string(&result).unwrap());
            if self.debug {
                if let Some(r) = result {
                    for (index, item) in r.memory.iter().enumerate() {
                        eprintln!("  Addr[{index}] = {} + 0x{:X}", item.sum_of.iter().join(" + "), item.offset);
                    }

                    for item in r.write_targets.iter() {
                        eprintln!(
                            "  {:?} := {} with inputs {:?}",
                            item.write_target, item.computation, item.inputs
                        );
                    }
                }
            }

            buf.clear();
        }
    }
}
