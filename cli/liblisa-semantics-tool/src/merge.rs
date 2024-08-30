use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::PathBuf;
use std::time::Duration;

use liblisa::arch::Arch;
use liblisa::encoding::bitpattern::{Bit, ImmBitOrder, MappingOrBitOrder, PartMapping};
use liblisa::encoding::mcs::split_encodings_into_overlapping_groups;
use liblisa::encoding::{merge_encodings_semantically, Encoding, EncodingWithFilters, IntegrityError};
use liblisa::instr::InstructionFilter;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::smt::z3::ThreadLocalZ3;
use liblisa::smt::{CachedSolverProvider, MemoryCache, SharedCache};

#[derive(Clone, Debug, clap::Parser)]
/// Merges encodings that (partially) overlap and whose semantics are equivalent.
pub struct Merge {
    /// The path of the JSON file that contains the encodings.
    encodings: PathBuf,

    #[clap(long)]
    /// The path of the target file to which the merged encodings will be written.
    /// When not specified, results are discarded.
    output: Option<PathBuf>,

    #[clap(long)]
    /// An optional instruction filter.
    /// Only encodings that (partially) overlap with the filter are processed.
    /// When not specified, all encodings are processed.
    filter: Option<InstructionFilter>,
}

impl Merge {
    pub fn run<A: Arch>(self) {
        // We already do some merging in the post-processing after enumeration, but we can be much more aggressive here.
        // Semantics have already been synthesized, so we don't need to worry about what structure can be most useful for synthesis.
        // So we can just merge as much as possible.

        println!("Loading {:?}...", self.encodings);

        let encodings: Vec<Encoding<A, SynthesizedComputation>> =
            serde_json::from_reader(BufReader::new(File::open(&self.encodings).unwrap())).unwrap();

        let mut failed = false;
        let encodings = encodings.iter()
            .filter(|e| if let Some(filter) = &self.filter {
                e.bitpattern_as_filter().overlaps(filter)
            } else {
                true
            })
            .cloned()
            .map(|mut encoding| {
                encoding.fix();

                match encoding.integrity_check() {
                    Ok(_) => (),
                    Err(e) => {
                        let fixed = match e {
                            IntegrityError::MappingDoesNotMatchPartSize { part_index, .. } => {
                                println!("Trying to fix encoding with incorrect mapping size in part {part_index}: {encoding}\n\n{encoding:?}");
                                let part = &mut encoding.parts[part_index];
                                match &mut part.mapping {
                                    PartMapping::Imm { mapping: Some(MappingOrBitOrder::BitOrder(bit_order)), .. } if bit_order.len() > part.size => {
                                        let mut indices_to_remove = Vec::new();
                                        let bit_indices = encoding.bits.iter()
                                            .enumerate()
                                            .filter(|&(_, &bit)| bit == Bit::Part(part_index))
                                            .map(|(index, _)| index)
                                            .collect::<Vec<_>>();
                                        let mut n = 0;
                                        for (index, bit_order) in bit_order.iter().enumerate() {
                                            // TODO: This uses x86-specific knowledge to fix a few errors in some encodings.
                                            // TODO: This should never happen on new runs that generate correct encodings, so remove this at some point in the future.

                                            if let Some(bit_index) = bit_indices.get(n) {
                                                let expected = bit_index % 8;
                                                let actual = match bit_order {
                                                    ImmBitOrder::Positive(n) | ImmBitOrder::Negative(n) => n % 8,
                                                };

                                                if expected != actual {
                                                    indices_to_remove.push(index);
                                                } else {
                                                    n += 1;
                                                }
                                            } else {
                                                indices_to_remove.push(index);
                                            }
                                        }

                                        println!("Applying fix: remove indices {indices_to_remove:?} from {bit_order:?}");
                                        if bit_order.len() - indices_to_remove.len() == part.size {
                                            for index in indices_to_remove.into_iter().rev() {
                                                bit_order.remove(index);
                                            }

                                            true
                                        } else {
                                            false
                                        }
                                    },
                                    _ => false,
                                }
                            },
                            _ => false,
                        };

                        if !fixed {
                            failed = true;
                            println!("Encoding failed integrity check: {e}: {encoding}\n\n{encoding:?}")
                        }
                    },
                }

                encoding
            })
            .collect::<Vec<_>>();

        if failed {
            panic!("One or more encodings failed integrity checks");
        }

        let num_encodings = encodings.len();

        let encodings_with_filters = encodings.into_iter().map(EncodingWithFilters::new).collect::<Vec<_>>();

        // println!("{} encodings", encodings_with_filters.len());
        // for encoding in encodings_with_filters.iter() {
        //     println!("Encoding: {}", encoding.encoding);
        // }

        let overlapping_groups = split_encodings_into_overlapping_groups(encodings_with_filters);

        let num_unit_groups = overlapping_groups.iter().filter(|g| g.len() == 1).count();

        println!("{num_unit_groups} / {num_encodings} encodings don't overlap");

        let solver_cache = SharedCache::new(MemoryCache::new());

        let solver = ThreadLocalZ3::new(Duration::from_secs(90));
        let solver = CachedSolverProvider::new(&solver_cache, solver);

        let new_encodings = merge_encodings_semantically(overlapping_groups, &solver);

        if let Some(output) = self.output {
            let new_encodings = new_encodings.into_iter().map(|e| e.encoding).collect::<Vec<_>>();
            println!("Writing results...");
            serde_json::to_writer(BufWriter::new(File::create(output).unwrap()), &new_encodings).unwrap();
        }
    }
}
