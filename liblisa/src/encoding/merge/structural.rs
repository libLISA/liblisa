use std::collections::HashSet;
use std::fmt::Debug;
use std::sync::atomic::{AtomicUsize, Ordering};

use log::{debug, info};
use rayon::prelude::*;

use crate::arch::Arch;
use crate::compare::{encoding_addresses_equal, encoding_dataflows_structurally_equal, PartIndexMapping};
use crate::encoding::bitpattern::{MappingOrBitOrder, Part, PartMapping};
use crate::encoding::Encoding;
use crate::semantics::Computation;
use crate::utils::bitmask_u64;

fn is_merge_candidate<A: Arch, C: Clone + Debug + PartialEq>(a: &Encoding<A, C>, b: &Encoding<A, C>) -> bool {
    // TODO: Allow bits to differ
    if a.bits != b.bits {
        return false
    }

    for (part_a, part_b) in a.parts.iter().zip(b.parts.iter()) {
        match (&part_a.mapping, &part_b.mapping) {
            (
                PartMapping::Imm {
                    mapping: mapping_a, ..
                },
                PartMapping::Imm {
                    mapping: mapping_b, ..
                },
            ) => match (mapping_a, mapping_b) {
                (None, None) => (),
                (Some(MappingOrBitOrder::Mapping(a)), Some(MappingOrBitOrder::Mapping(b))) => {
                    if a != b {
                        return false
                    }
                },
                (Some(MappingOrBitOrder::BitOrder(bitorder_a)), Some(MappingOrBitOrder::BitOrder(bitorder_b))) => {
                    if bitorder_a != bitorder_b {
                        return false
                    }
                },
                _ => return false,
            },

            (
                PartMapping::MemoryComputation {
                    mapping: mapping_a,
                    memory_indexes: memory_indexes_a,
                },
                PartMapping::MemoryComputation {
                    mapping: mapping_b,
                    memory_indexes: memory_indexes_b,
                },
            ) if memory_indexes_a == memory_indexes_b => {
                for (lhs, rhs) in mapping_a.iter().zip(mapping_b.iter()) {
                    if lhs.and_then(|lhs| rhs.map(|rhs| lhs != rhs)).unwrap_or(false) {
                        return false
                    }
                }
            },

            (
                PartMapping::Register {
                    mapping: mapping_a, ..
                },
                PartMapping::Register {
                    mapping: mapping_b, ..
                },
            ) => {
                for (lhs, rhs) in mapping_a.iter().zip(mapping_b.iter()) {
                    if lhs.and_then(|lhs| rhs.map(|rhs| lhs != rhs)).unwrap_or(false) {
                        return false
                    }
                }
            },

            _ => return false,
        }
    }

    let mapping = PartIndexMapping::of(a, b).unwrap();
    if !encoding_addresses_equal(&mapping, &Default::default(), a, b) {
        return false
    }

    if !encoding_dataflows_structurally_equal(&mapping, a, b) {
        return false
    }

    if a.dataflows.addresses.memory != b.dataflows.addresses.memory {
        return false
    }

    if a.dataflows.outputs.len() != b.dataflows.outputs.len() {
        return false
    }

    true
}

fn try_merge<A: Arch, C: Computation>(encoding: &Encoding<A, C>, candidates: &[&Encoding<A, C>]) -> Option<Encoding<A, C>> {
    let merged_encoding = Encoding {
        parts: encoding
            .parts
            .iter()
            .enumerate()
            .map(|(part_index, part)| Part {
                size: part.size,
                value: part.value,
                mapping: match &part.mapping {
                    PartMapping::MemoryComputation {
                        mapping,
                        memory_indexes,
                    } => PartMapping::MemoryComputation {
                        memory_indexes: memory_indexes.clone(),
                        mapping: mapping
                            .iter()
                            .enumerate()
                            .map(|(index, &reg)| {
                                reg.or_else(|| {
                                    candidates
                                        .iter()
                                        .flat_map(|e| {
                                            if let PartMapping::MemoryComputation {
                                                mapping: other_mapping, ..
                                            } = &e.parts[part_index].mapping
                                            {
                                                other_mapping[index]
                                            } else {
                                                unreachable!()
                                            }
                                        })
                                        .next()
                                })
                            })
                            .collect(),
                    },
                    PartMapping::Register {
                        mapping,
                        locations,
                    } => PartMapping::Register {
                        locations: locations.clone(),
                        mapping: mapping
                            .iter()
                            .enumerate()
                            .map(|(index, &reg)| {
                                reg.or_else(|| {
                                    candidates
                                        .iter()
                                        .flat_map(|e| {
                                            if let PartMapping::Register {
                                                mapping: other_mapping, ..
                                            } = &e.parts[part_index].mapping
                                            {
                                                other_mapping[index]
                                            } else {
                                                unreachable!()
                                            }
                                        })
                                        .next()
                                })
                            })
                            .collect(),
                    },
                    other => other.clone(),
                },
            })
            .collect(),
        ..encoding.clone()
    };

    let main_filters = encoding.filters();
    let merged_filters = merged_encoding.filters();
    let candidate_filters = candidates
        .iter()
        .map(|encoding| (encoding, encoding.filters()))
        .collect::<Vec<_>>();

    let relevant_parts = encoding
        .parts
        .iter()
        .enumerate()
        .filter(|(_index, part)| match &part.mapping {
            PartMapping::Imm {
                ..
            } => false,
            PartMapping::MemoryComputation {
                ..
            } => true,
            PartMapping::Register {
                ..
            } => true,
        })
        .collect::<Vec<_>>();

    let part_sizes = encoding
        .parts
        .iter()
        .enumerate()
        .map(|(index, part)| {
            if relevant_parts.iter().any(|&(n, _)| n == index) {
                Some(part.size)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    let num_bits = relevant_parts.iter().map(|(_, part)| part.size).sum::<usize>();

    for c in 0..1u64 << num_bits {
        let mut k = c;
        let parts = part_sizes
            .iter()
            .map(|size| {
                size.map(|n| {
                    let result = k & bitmask_u64(n as u32);
                    k >>= n;
                    result
                })
                .unwrap_or(0)
            })
            .collect::<Vec<_>>();

        let instr = encoding.unchecked_instr(&parts);
        if !main_filters.iter().any(|f| f.matches(&instr)) {
            if let Some((other_index, (..))) = candidate_filters
                .iter()
                .enumerate()
                .find(|(_, (_, filters))| filters.iter().any(|f| f.matches(&instr)))
            {
                debug!("{instr:X} is covered by encoding {other_index}");
            } else if merged_filters.iter().any(|f| f.matches(&instr)) {
                info!("{instr:X} is not covered");
                return None
            }
        }
    }

    Some(merged_encoding)
}

/// Performs a conservative merging of a collection of [`crate::encoding::Encoding`]s.
///
/// Encodings are merged if they have the same bitpattern and are structurally similar.
pub fn merge_encodings_structurally<A: Arch, C: Eq + std::hash::Hash + Computation + Send + Sync>(
    encodings: Vec<Encoding<A, C>>,
) -> Vec<Encoding<A, C>> {
    info!("Merging {} encodings", encodings.len());

    let num_candidates = AtomicUsize::new(0);
    let num_merged = AtomicUsize::new(0);

    let num_checked = AtomicUsize::new(0);

    let encodings_with_candidates = encodings
        .par_iter()
        .enumerate()
        .map(|(a_index, a)| {
            let n = num_checked.fetch_add(1, Ordering::Relaxed);
            if n % 10_000 == 0 {
                info!("Finding merge candidates: {n}/{}", encodings.len());
            }

            (
                a_index,
                a,
                encodings
                    .iter()
                    .enumerate()
                    .filter(|&(b_index, b)| a_index != b_index && is_merge_candidate(a, b))
                    .map(|(_, b)| b)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    let new_encodings = encodings_with_candidates
        .into_par_iter()
        .map(|(a_index, a, candidates)| {
            if !candidates.is_empty() {
                num_candidates.fetch_add(candidates.len(), Ordering::Relaxed);
                debug!("Merge candidates for #{a_index}:");
                debug!("{a}");

                for candidate in candidates.iter() {
                    debug!("Candidate: {candidate}");
                }

                if let Some(new_encoding) = try_merge(a, &candidates) {
                    debug!("Merged encoding: {new_encoding}");
                    num_merged.fetch_add(1, Ordering::Relaxed);

                    new_encoding
                } else {
                    a.clone()
                }
            } else {
                a.clone()
            }
        })
        .collect::<HashSet<_>>();

    info!("Merge candidates: {num_candidates:?}");
    info!("Encodings merged: {num_merged:?}");

    info!("{} unique encodings", new_encodings.len());

    new_encodings.into_iter().collect()
}
