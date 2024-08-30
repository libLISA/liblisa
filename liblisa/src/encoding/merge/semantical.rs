use std::collections::HashSet;

use log::trace;

use crate::arch::Arch;
use crate::compare::{
    encoding_addresses_equal, encodings_semantically_equal, AddressComparisonOptions, ComputationEquivalence,
    EncodingComparisonOptions, Mapping, PartIndexMapping,
};
use crate::encoding::bitpattern::{Bit, Part, PartMapping};
use crate::encoding::dataflows::{Dataflows, MemoryAccess, MemoryAccesses};
use crate::encoding::{Encoding, EncodingWithFilters};
use crate::instr::WithFilters;
use crate::semantics::default::computation::{AsComputationRef, SynthesizedComputation};
use crate::semantics::Computation;
use crate::smt::SolverProvider;
use crate::utils::Symmetric2DMatrix;

fn encoding_is_excluded<A: Arch, C: Computation + PartialEq>(a: &Encoding<A, C>) -> bool {
    for part in a.parts.iter() {
        match &part.mapping {
            PartMapping::Imm {
                ..
            } => (),
            PartMapping::MemoryComputation {
                ..
            } => (),
            PartMapping::Register {
                mapping, ..
            } => {
                let num_filled = mapping.iter().flatten().count();
                let distinct = mapping.iter().copied().flatten().collect::<HashSet<_>>();

                // If more than 20% of options is non-distinct
                if distinct.len() < (num_filled * 4) / 5 {
                    return true
                }
            },
        }
    }

    // if a.dataflows.outputs.iter().any(|flow| flow.computation.is_none()) {
    //     return true
    // }

    false
}

fn is_merge_candidate<A: Arch, C: Computation + AsComputationRef + PartialEq>(
    a: &Encoding<A, C>, b: &Encoding<A, C>, solver: &impl SolverProvider,
) -> bool {
    if encoding_is_excluded(a) || encoding_is_excluded(b) {
        return false
    }

    if !a.write_ordering.is_empty() || !b.write_ordering.is_empty() {
        return false
    }

    if a.bits.len() != b.bits.len() {
        println!("Not the same number of bits");
        return false
    }

    for (bit_a, bit_b) in a.bits.iter().zip(b.bits.iter()) {
        match (bit_a, bit_b) {
            (Bit::Part(_), Bit::Part(_))
            | (Bit::Part(_), Bit::Fixed(_))
            | (Bit::Part(_), Bit::DontCare)
            | (Bit::Fixed(_), Bit::Part(_))
            | (Bit::DontCare, Bit::DontCare) => (),
            (Bit::Fixed(val_a), Bit::Fixed(val_b)) => {
                if val_a != val_b {
                    return false
                }
            },
            (Bit::Fixed(_), Bit::DontCare) | (Bit::DontCare, Bit::Part(_)) | (Bit::DontCare, Bit::Fixed(_)) => return false,
        }
    }

    trace!("Checking merge: {a} vs {b}");

    let mapping = match Mapping::of(
        a.bits.iter().copied().map(|bit| (bit, true)),
        b.bits.iter().copied().map(|bit| (bit, true)),
    ) {
        Some(mapping) if mapping.all_indices_mapped() => mapping,
        _ => return false,
    };

    trace!("Part mapping: {mapping:?}");

    if a.dataflows.addresses.len() != b.dataflows.addresses.len() {
        println!("Different number of memory accesses");
        return false
    }

    if a.dataflows.outputs.len() != b.dataflows.outputs.len() {
        return false
    }

    if a.parts.len() != b.parts.len() {
        println!("Different number of parts");
        return false
    }

    let parts_match = a
        .parts
        .iter()
        .enumerate()
        .map(|(a_index, a)| (a, &b.parts[mapping.a_to_b(a_index)]))
        .all(|(a, b)| match (&a.mapping, &b.mapping) {
            (
                PartMapping::Imm {
                    mapping: mapping_a, ..
                },
                PartMapping::Imm {
                    mapping: mapping_b, ..
                },
            ) => a.size == b.size && mapping_a == mapping_b,
            (
                PartMapping::MemoryComputation {
                    ..
                },
                PartMapping::MemoryComputation {
                    ..
                },
            ) => true,
            (
                PartMapping::Register {
                    ..
                },
                PartMapping::Register {
                    ..
                },
            ) => true,
            _ => false,
        });

    if !parts_match {
        println!("Parts don't match");
        return false
    }

    let imm_part_bits_identical = a.bits.iter().zip(b.bits.iter()).all(|(&bit_a, &bit_b)| match (bit_a, bit_b) {
        (Bit::Part(n), _) if a.is_bit_imm(bit_a) => Some(bit_b) == mapping.try_a_to_b(n).map(Bit::Part),
        (_, Bit::Part(n)) if b.is_bit_imm(bit_b) => Some(bit_a) == mapping.try_b_to_a(n).map(Bit::Part),
        _ => true,
    });
    if !imm_part_bits_identical {
        return false
    }

    let imm_bits_match = a.bits.iter().zip(b.bits.iter()).all(|(&a_bit, &b_bit)| {
        let a_is_imm = a.is_bit_imm(a_bit);
        let b_is_imm = b.is_bit_imm(b_bit);

        (a_is_imm && b_is_imm) || (!a_is_imm && !b_is_imm)
    });

    if !imm_bits_match {
        return false
    }

    let parts_overlap = a.bits.iter().zip(b.bits.iter()).any(|(&a, &b)| match (a, b) {
        (Bit::Part(n_a), Bit::Part(n_b)) => n_a != mapping.b_to_a(n_b),
        _ => false,
    });

    if parts_overlap {
        return false
    }

    let reg_bits_to_check = a
        .bits
        .iter()
        .zip(b.bits.iter())
        .enumerate()
        .filter(|(_, (&bit_a, &bit_b))| {
            matches!(bit_a, Bit::Part(n) if matches!(a.parts[n].mapping, PartMapping::Register { .. }))
                && matches!(bit_b, Bit::Part(_))
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();

    if reg_bits_to_check.len() >= 20 {
        return false
    }

    let base_instr = {
        let mut instr = *a.instr();

        for (index, (&a, &b)) in a.bits.iter().zip(b.bits.iter()).enumerate() {
            match (a, b) {
                (Bit::Fixed(bit), _) => instr.set_nth_bit_from_right(index, bit),
                (_, Bit::Fixed(bit)) => instr.set_nth_bit_from_right(index, bit),
                _ => (),
            }
        }

        instr
    };

    for k in 0..(1u64 << reg_bits_to_check.len()) {
        let instr = {
            let mut instr = base_instr;
            for (index, &bit_index) in reg_bits_to_check.iter().enumerate() {
                instr.set_nth_bit_from_right(bit_index, (k >> index) as u8 & 1);
            }

            instr
        };

        let parts_a = a.extract_parts(&instr);
        let parts_b = b.extract_parts(&instr);
        let parts = a.parts.iter().enumerate().map(|(index_a, part_a)| {
            let index_b = mapping.a_to_b(index_a);
            ((index_a, part_a), (index_b, &b.parts[index_b]))
        });
        for ((index_a, part_a), (index_b, part_b)) in parts {
            if let (
                PartMapping::Register {
                    mapping: mapping_a, ..
                },
                PartMapping::Register {
                    mapping: mapping_b, ..
                },
            ) = (&part_a.mapping, &part_b.mapping)
            {
                if let (Some(a), Some(b)) = (mapping_a[parts_a[index_a] as usize], mapping_b[parts_b[index_b] as usize]) {
                    if a != b {
                        return false
                    }
                }
            }
        }
    }

    let mapping_for_equivalence = match PartIndexMapping::of(a, b) {
        Some(mapping) => mapping,
        _ => return false,
    };

    let options = AddressComparisonOptions {
        allow_size_differences: true,
        ..Default::default()
    };

    if !encoding_addresses_equal(&mapping_for_equivalence, &options, a, b) {
        return false
    }

    let options = EncodingComparisonOptions::default();
    let equivalence =
        solver.with_solver(|mut context| ComputationEquivalence::of(&mapping_for_equivalence, &options, a, b, &mut context));
    if equivalence != ComputationEquivalence::Equal {
        println!("Equivalence is false!");
        return false
    }

    true
}

fn merge<A: Arch, C: Computation>(a: &EncodingWithFilters<A, C>, b: &EncodingWithFilters<A, C>) -> Encoding<A, C> {
    let a_filters = &a.filters;
    let b_filters = &b.filters;
    let a = &a.encoding;
    let b = &b.encoding;

    let mapping = Mapping::of(
        a.bits.iter().copied().map(|bit| (bit, true)),
        b.bits.iter().copied().map(|bit| (bit, true)),
    )
    .expect("can_merge should have checked this");

    let merged_bits = a
        .bits
        .iter()
        .copied()
        .zip(b.bits.iter().copied())
        .map(|(a, b)| match (a, b) {
            (Bit::Part(n_a), Bit::Part(n_b)) => {
                assert_eq!(n_b, mapping.a_to_b(n_a));
                Bit::Part(n_a)
            },
            (Bit::Part(n), Bit::Fixed(_)) | (Bit::Part(n), Bit::DontCare) | (Bit::Fixed(_), Bit::Part(n)) => Bit::Part(n),
            (Bit::Fixed(val_a), Bit::Fixed(val_b)) => {
                assert_eq!(val_a, val_b);
                Bit::Fixed(val_a)
            },
            (Bit::Fixed(_), Bit::DontCare) => todo!(),
            (Bit::DontCare, Bit::Part(_)) => todo!(),
            (Bit::DontCare, Bit::Fixed(_)) => todo!(),
            (Bit::DontCare, Bit::DontCare) => Bit::DontCare,
        })
        .collect::<Vec<_>>();

    assert_eq!(a.parts.len(), b.parts.len());

    // TODO: Allow merges when parts don't match: build register parts and memory computation parts by exhaustively enumerating options, instead of looking at the current parts.

    Encoding {
        parts: a
            .parts
            .iter()
            .enumerate()
            .map(|(a_part_index, a_part)| {
                let b_part_index = mapping.a_to_b(a_part_index);
                let b_part = &b.parts[b_part_index];
                let bit_indices = merged_bits
                    .iter()
                    .enumerate()
                    .filter(|&(_, &b)| b == Bit::Part(a_part_index))
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>();
                Part {
                    size: bit_indices.len(),
                    value: 0,
                    mapping: match &a_part.mapping {
                        PartMapping::MemoryComputation {
                            mapping,
                            memory_indexes,
                        } => PartMapping::MemoryComputation {
                            memory_indexes: memory_indexes.clone(),
                            mapping: (0..(1u64 << bit_indices.len()))
                                .map(|k| {
                                    let mut instr_a = *a.instr();
                                    let mut instr_b = *b.instr();
                                    for (index, bit_index) in bit_indices.iter().copied().enumerate() {
                                        let bit = (k >> index) as u8 & 1;
                                        instr_a.set_nth_bit_from_right(bit_index, bit);
                                        instr_b.set_nth_bit_from_right(bit_index, bit);
                                    }

                                    let mapping_from_a = if a_filters.iter().any(|f| f.matches(&instr_a)) {
                                        let parts = a.extract_parts(&instr_a);
                                        mapping[parts[a_part_index] as usize]
                                    } else {
                                        None
                                    };

                                    mapping_from_a.or_else(|| {
                                        if b_filters.iter().any(|f| f.matches(&instr_b)) {
                                            let parts = b.extract_parts(&instr_b);
                                            match &b_part.mapping {
                                                PartMapping::MemoryComputation {
                                                    mapping, ..
                                                } => mapping[parts[b_part_index] as usize],
                                                _ => unreachable!(),
                                            }
                                        } else {
                                            None
                                        }
                                    })
                                })
                                .collect(),
                        },
                        PartMapping::Register {
                            mapping,
                            locations,
                        } => PartMapping::Register {
                            locations: locations.clone(),
                            mapping: (0..(1u64 << bit_indices.len()))
                                .map(|k| {
                                    let mut instr_a = *a.instr();
                                    let mut instr_b = *b.instr();
                                    for (index, bit_index) in bit_indices.iter().copied().enumerate() {
                                        let bit = (k >> index) as u8 & 1;
                                        instr_a.set_nth_bit_from_right(bit_index, bit);
                                        instr_b.set_nth_bit_from_right(bit_index, bit);
                                    }

                                    let mapping_from_a = if a_filters.iter().any(|f| f.matches(&instr_a)) {
                                        let parts = a.extract_parts(&instr_a);
                                        mapping[parts[a_part_index] as usize]
                                    } else {
                                        None
                                    };

                                    mapping_from_a.or_else(|| {
                                        if b_filters.iter().any(|f| f.matches(&instr_b)) {
                                            let parts = b.extract_parts(&instr_b);
                                            match &b.parts[b_part_index].mapping {
                                                PartMapping::Register {
                                                    mapping, ..
                                                } => mapping[parts[b_part_index] as usize],
                                                _ => unreachable!(),
                                            }
                                        } else {
                                            None
                                        }
                                    })
                                })
                                .collect(),
                        },
                        other => other.clone(),
                    },
                }
            })
            .collect(),
        bits: merged_bits,
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                memory: a
                    .dataflows
                    .addresses
                    .iter()
                    .zip(b.dataflows.addresses.iter())
                    .map(|(a, b)| MemoryAccess {
                        size: a.size.start.min(b.size.start)..a.size.end.min(b.size.end),
                        ..a.clone()
                    })
                    .collect(),
                ..a.dataflows.addresses.clone()
            },
            ..a.dataflows.clone()
        },
        // write_ordering,
        ..a.clone()
    }
    .canonicalize()
}

/// Performs an eager merging of a collection of [`crate::encoding::Encoding`]s.
///
/// Encodings are merged if they overlap and their semantics are equivalent.
/// An SMT solver is used to determine if the semantics are equivalent.
pub fn merge_encodings_semantically<A: Arch>(
    overlapping_groups: Vec<Vec<EncodingWithFilters<A, SynthesizedComputation>>>, solver: &impl SolverProvider,
) -> Vec<EncodingWithFilters<A, SynthesizedComputation>> {
    let mut num_merged = 0;
    let mut num_covering_removed = 0;
    let mut num_candidates = 0;
    let num_groups = overlapping_groups.len();
    let mut new_encodings = Vec::new();
    for (index, group) in overlapping_groups.into_iter().enumerate() {
        println!("Processing group {index} / {num_groups}");

        if group.len() > 1 {
            num_candidates += group.len();
            for (index, candidate) in group.iter().enumerate() {
                println!("Candidate #{index}: {}", candidate.encoding);
            }

            let mut compared = Symmetric2DMatrix::new();
            let mut group = group.into_iter().enumerate().collect::<Vec<_>>();
            let mut next_id = group.len();

            'outer: loop {
                for (index_a, (id_a, candidate_a)) in group.iter().enumerate() {
                    for (index_b, (id_b, candidate_b)) in group.iter().enumerate().skip(index_a + 1) {
                        // Make sure we perform each comparison only once
                        if compared.set(*id_a, *id_b) {
                            // println!("Comparing {index_a} & {index_b}");
                            if is_merge_candidate(&candidate_a.encoding, &candidate_b.encoding, solver) {
                                num_merged += 1;
                                println!("Merging {index_a} & {index_b}");
                                println!("{}", candidate_a.encoding);
                                println!("{}", candidate_b.encoding);

                                let new_encoding = EncodingWithFilters::new(merge(candidate_a, candidate_b));
                                println!("New encoding: {}", new_encoding.encoding);

                                match new_encoding.encoding.integrity_check() {
                                    Ok(_) => (),
                                    Err(e) => panic!(
                                        "Encoding does not match integrity check after merging: {e}; {0}; {0:?}",
                                        new_encoding.encoding
                                    ),
                                }

                                group.remove(index_a.max(index_b));
                                group.remove(index_a.min(index_b));
                                group.push((next_id, new_encoding));
                                next_id += 1;

                                continue 'outer
                            }

                            let bf_a = candidate_a.encoding.bitpattern_as_filter();
                            let bf_b = candidate_b.encoding.bitpattern_as_filter();
                            if let Some(((smaller_index, smaller), bigger)) = if bf_a.covers(&bf_b) {
                                Some(((index_b, candidate_b), candidate_a))
                            } else if bf_b.covers(&bf_a) {
                                Some(((index_a, candidate_a), candidate_b))
                            } else {
                                None
                            } {
                                let covering = smaller
                                    .filters
                                    .iter()
                                    .all(|filter| filter.find_uncovered_instr(bigger.filters().to_vec()).is_none());
                                if covering {
                                    let can_remove = smaller.filters.iter().all(|filter| {
                                        if let (Ok(lhs), Ok(rhs)) = (smaller.encoding.restrict_to(filter), bigger.encoding.restrict_to(filter)) {
                                            let equivalence = solver.with_solver(|mut context| {
                                                encodings_semantically_equal(&Default::default(), &lhs, &rhs, &mut context)
                                            });

                                            if !equivalence.equal || equivalence.timeout {
                                                println!("Encodings are covering, but semantics differ: {lhs}\\n{rhs}\\n\\nOriginals: {}\\n{}\\n", smaller.encoding, bigger.encoding);
                                                false
                                            } else {
                                                true
                                            }
                                        } else {
                                            false
                                        }
                                    });

                                    if can_remove {
                                        println!(
                                            "Removing covering candidate: Smaller {}; Bigger {}",
                                            smaller.encoding, bigger.encoding
                                        );
                                        group.remove(smaller_index);
                                        num_covering_removed += 1;
                                        continue 'outer
                                    }
                                }
                            }
                        }
                    }
                }

                break
            }

            // TODO: Detect if we have any encodings that completely cover other encodings, and if so: 1. Make sure they are equivalent, 2. remove the smallest one.
            // TODO: See for example the one Nico showed in the last PI meeting

            new_encodings.extend(group.into_iter().map(|(_, x)| x));
        } else {
            new_encodings.extend(group);
        }
    }

    println!("Merge candidates: {num_candidates}");
    println!("Encodings merged: {num_merged}");
    println!("Encodings removed (because of another equivalent covering encoding): {num_covering_removed}");

    println!("{} unique encodings", new_encodings.len());
    new_encodings
}
