//! Methods for splitting encodings into overlapping groups and finding mimimum covering subsets of encodings.

use std::collections::HashMap;
use std::hash::Hash;
use std::iter::repeat;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use itertools::Itertools;
use log::{debug, info, trace};
use rand::seq::SliceRandom;
use rayon::prelude::*;

use crate::arch::Arch;
use crate::encoding::bitpattern::Bit;
use crate::encoding::{Encoding, EncodingWithFilters};
use crate::instr::{MinimumCoveringFilterSet, WithFilters};
use crate::semantics::Computation;
use crate::utils::bitmap::GrowingBitmap;
use crate::utils::Symmetric2DMatrix;

fn filter_mask_from_bits(bits: &[Bit]) -> u32 {
    bits.iter()
        .rev()
        .chain(repeat(&Bit::Fixed(0)))
        .take(32)
        .enumerate()
        .fold(0u32, |acc, (index, bit)| {
            acc | (match bit {
                Bit::Fixed(_) => 1,
                _ => 0,
            } << (31 - index))
        })
}

fn instruction_start_from_bits(bits: &[Bit]) -> u32 {
    bits.iter()
        .rev()
        .chain(repeat(&Bit::Fixed(0)))
        .take(32)
        .enumerate()
        .fold(0u32, |acc, (index, bit)| {
            acc | (match bit {
                Bit::Fixed(v) => *v as u32,
                _ => 0,
            } << (31 - index))
        })
}

/// A set of encodings in a [`Split`] that don't overlap with the other [`SplitEntry`]s in the [`Split`].
pub struct SplitEntry<A: Arch, C: Computation> {
    /// A unique key representing this entry.
    pub key: u32,

    /// The set of encoding that don't overlap with the other [`SplitEntry`]s in the [`Split`].
    pub encodings: Vec<EncodingWithFilters<A, C>>,
}

/// Sets of encodings that do not overlap with any of the other sets.
pub struct Split<A: Arch, C: Computation> {
    /// The mask used.
    pub mask: u32,

    /// Groups of encodings that don't overlap with any of the other groups.
    pub groups: Vec<SplitEntry<A, C>>,
}

impl<A: Arch, C: Computation> Split<A, C> {
    /// Splits the encodings by bits that are fixed in all encodings.
    pub fn by_fixed_bits(encodings: Vec<EncodingWithFilters<A, C>>) -> Split<A, C> {
        let mask = encodings
            .iter()
            .map(|encoding| filter_mask_from_bits(&encoding.encoding.bits))
            .fold(u32::MAX, |a, b| a & b);

        debug!("Mask: {:08X}", mask);

        let mut result = HashMap::new();
        for encoding in encodings {
            let entry = mask & instruction_start_from_bits(&encoding.encoding.bits);
            result.entry(entry).or_insert(Vec::new()).push(encoding);
        }

        Split {
            mask,
            groups: result
                .into_iter()
                .map(|(key, value)| SplitEntry {
                    key,
                    encodings: value,
                })
                .collect(),
        }
    }
}

fn split_into_overlapping_groups<A: Arch, C: Computation + Send>(
    encodings: Vec<Vec<EncodingWithFilters<A, C>>>,
) -> Vec<Vec<EncodingWithFilters<A, C>>> {
    encodings
        // .into_par_iter()
        // .with_max_len(1)
        .into_iter()
        .flat_map(|encodings| if encodings.len() <= 1 {
            vec![ encodings ]
        } else {
            assert!(encodings.iter().all(|e| e.encoding.instr().byte_len() == encodings[0].encoding.instr().byte_len()));
            debug!("Considering group of {} encodings: {}", encodings.len(), encodings.iter().map(|e| format!("{:X}", e.encoding.instr())).format(", "));

            // Pre-compute the symmetric overlapping matrix so we can skip over 50% of the InstructionFilter::overlaps calls.
            let overlapping = {
                let mut overlapping = Symmetric2DMatrix::new();
                for (index_a, a) in encodings.iter().enumerate() {
                    // Always overlapping with self
                    overlapping.set(index_a, index_a);

                    for (index_b, b) in encodings.iter().enumerate().skip(index_a + 1) {
                        if a.filters.iter().any(|fa| b.filters.iter().any(|fb| fa.overlaps(fb))) {
                            overlapping.set(index_a, index_b);
                        }
                    }
                }

                overlapping
            };

            let mut group_masks = Vec::new();
            let mut remaining = GrowingBitmap::new_all_ones(encodings.len());
            while let Some(index) = remaining.first_bit_set() {
                trace!("Remaining: {remaining:?}");
                let mut mask = GrowingBitmap::new_all_zeros(encodings.len());
                let mut frontier = vec![ index ];

                trace!("Mask: {mask:?}");
                trace!("Frontier: {frontier:?}");

                while let Some(index) = frontier.pop() {
                    trace!("Popped {index}");
                    trace!("Mask: {mask:?}");
                    trace!("Frontier: {frontier:?}");
                    trace!("Entries to set: {}", overlapping.iter_row_indices(index).format(", "));

                    for item in overlapping.iter_row_indices(index) {
                        if mask.set(item) {
                            frontier.push(item);
                        }
                    }
                }

                debug!("Created new group mask {mask:?}, {} encodings remaining", remaining.count_ones());
                remaining.clear_from(&mask);
                group_masks.push(mask);
            }

            let mut groups = vec![ Vec::new(); group_masks.len() ];
            for (index, e) in encodings.into_iter().enumerate() {
                let group_index = group_masks.iter()
                    .position(|mask| mask[index])
                    .expect("All encodings should have been assigned a group, because the while loop above continues until `remaining` is empty");

                groups[group_index].push(e);
            }

            debug!("Created {} groups", groups.len());

            groups
        }).collect()
}

/// Splits all encodings into the smallest groups of encodings that overlap with eachother, but not with any other group.
pub fn split_encodings_into_overlapping_groups<A: Arch, C: Computation + Send>(
    mut encodings: Vec<EncodingWithFilters<A, C>>,
) -> Vec<Vec<EncodingWithFilters<A, C>>> {
    encodings.sort_by_key(|e| e.encoding.instr().byte_len());
    let mut encoding_groups = encodings
        .into_iter()
        .group_by(|e| e.encoding.instr().byte_len())
        .into_iter()
        .map(|(_, group)| group.collect())
        .collect::<Vec<Vec<_>>>();

    for _ in 0..25 {
        encoding_groups = encoding_groups
            .into_iter()
            .flat_map(|group| Split::by_fixed_bits(group).groups.into_iter().map(|g| g.encodings))
            .collect::<Vec<_>>();
        info!(
            "Split encodings in {} groups: {:?}",
            encoding_groups.len(),
            encoding_groups.iter().map(|g| g.len()).collect::<Vec<_>>()
        );
    }

    info!(
        "Groups: {}",
        encoding_groups
            .iter()
            .map(|g| g.iter().map(|e| format!("{:X}", e.encoding.instr())).format(", "))
            .format(" || ")
    );

    info!("Splitting into overlapping groups...");
    let mut encoding_groups = split_into_overlapping_groups(encoding_groups);
    encoding_groups.shuffle(&mut rand::thread_rng());

    info!("Created {} groups of overlapping encodings", encoding_groups.len());
    info!("Max group size: {}", encoding_groups.iter().map(|g| g.len()).max().unwrap());
    info!("Groups: {:?}", encoding_groups.iter().map(|g| g.len()).collect::<Vec<_>>());
    encoding_groups
}

/// Computes a minimum covering set of encodings.
pub fn filter_overlapping_encodings<A: Arch, C: Computation + Eq + std::hash::Hash + PartialEq + Send + Sync>(
    encodings: Vec<Encoding<A, C>>,
) -> Vec<Encoding<A, C>> {
    info!("Encodings remaining: {}", encodings.len());

    info!("Finding minimal covering set for the remaining {} encodings", encodings.len());

    info!("Generating filters...");

    let encodings = encodings.into_par_iter();
    let encodings = encodings.map(|e| EncodingWithFilters::new(e)).collect::<Vec<_>>();

    info!("Pre-splitting by fixed instruction bits");

    let encoding_groups = split_encodings_into_overlapping_groups(encodings);
    let num_groups = encoding_groups.len();

    info!(
        "Determining minimal covering set of encodings for {} groups...",
        encoding_groups.len()
    );

    let num_chosen = AtomicUsize::new(0);

    let mut chosen_encodings = if log::log_enabled!(log::Level::Info) {
        encoding_groups
            .into_iter()
            .enumerate()
            .map(|(index, group)| choose_encodings(index, num_groups, group, &num_chosen))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>()
    } else {
        encoding_groups
            .into_par_iter()
            .with_min_len(1)
            .with_max_len(5)
            .enumerate()
            .map(|(index, group)| choose_encodings(index, num_groups, group, &num_chosen))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>()
    };

    info!("{} chosen encodings", chosen_encodings.len());
    chosen_encodings.sort_by_key(|e| *e.instr());

    chosen_encodings
}

fn choose_encodings<A: Arch, C: Computation + Eq + Hash + PartialEq + Send + Sync>(
    index: usize, num_groups: usize, mut group: Vec<EncodingWithFilters<A, C>>, num_chosen: &AtomicUsize,
) -> Vec<Encoding<A, C>> {
    let start = Instant::now();
    info!(
        "Group {index} / {num_groups} ({} encodings): {:?}",
        group.len(),
        group
            .iter()
            .map(|e| format!("{:X}", *e.encoding.dataflows.instr()))
            .collect::<Vec<_>>()
    );
    for (index, coverage) in group.iter().enumerate() {
        debug!("Encoding #{}", index);
        debug!("Filters: {:?}", coverage.filters);
        debug!("{}", coverage.encoding);
    }

    let pre_chosen_indices = group
        .iter()
        .enumerate()
        .filter(|&(group_index, encoding)| {
            let other_filters = group
                .iter()
                .enumerate()
                .filter(|&(other_index, _)| other_index != group_index)
                .flat_map(|(_, item)| item.filters.iter().cloned())
                .collect::<Vec<_>>();

            encoding
                .filters
                .iter()
                .any(|filter| filter.find_uncovered_instr(other_filters.clone()).is_some())
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    info!("Pre-chosen encoding indices: {pre_chosen_indices:?}");
    let pre_chosen = pre_chosen_indices
        .into_iter()
        .rev()
        .map(|index| group.remove(index))
        .collect::<Vec<_>>();

    info!(
        "Determining minimal covering set of {} encodings ({} pre-chosen)...",
        group.len(),
        pre_chosen.len()
    );
    let mut chosen = if group.is_empty() {
        Vec::new()
    } else {
        let mut mcfs = MinimumCoveringFilterSet::new(group.clone(), &pre_chosen);
        debug!("Running mcfs...");
        mcfs.run()
    };

    chosen.extend(pre_chosen);

    for item in chosen.iter() {
        debug!("Chosen: {}", item.encoding);
    }

    info!("Group {index} took {}ms", start.elapsed().as_millis());
    let num_chosen = num_chosen.fetch_add(chosen.len(), Ordering::Relaxed);
    info!("Total encodings chosen: {num_chosen}");

    let filters = chosen.iter().flat_map(|item| item.filters.iter()).collect::<Vec<_>>();
    for e in group.iter() {
        for instr in e
            .encoding
            .random_instrs(&vec![None; e.encoding.parts.len()], &mut rand::thread_rng())
            .take(100_000)
        {
            assert!(
                filters.iter().any(|f| f.matches(&instr)),
                "Instruction {instr:?} not covered by chosen encodings, from: {:?}",
                group.iter().map(|item| item.filters()).collect::<Vec<_>>()
            );
        }
    }

    chosen.into_iter().map(|item| item.encoding).collect::<Vec<_>>()
}

/// Check the integrity of all encodings, and apply automatic fixes if possible.
pub fn verify_and_fix<A: Arch>(encodings: &mut Vec<Encoding<A, ()>>, remove: bool) {
    info!("Verifying and fixing encodings...");
    for i in (0..encodings.len()).rev() {
        let encoding = &mut encodings[i];
        trace!("Trying to fix: {}", encoding);
        if !encoding.fix() {
            panic!("WARNING: Unable to fix: {encoding}");
        }

        trace!("Fixed: {}", encoding);
        match encoding.integrity_check() {
            Ok(_) => (),
            Err(e) => {
                if remove {
                    println!("WARNING: Removing encoding with failed integrity check: {e}: {encoding}");
                    encodings.remove(i);
                } else {
                    panic!("Integrity check failed: {e}: {encoding}")
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::filter_mask_from_bits;
    use crate::encoding::bitpattern::Bit;

    #[test]
    pub fn test_filter_mask_from_bits() {
        let mask = filter_mask_from_bits(&[
            Bit::Part(0),
            Bit::Fixed(1),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::DontCare,
            Bit::Fixed(1),
            Bit::Fixed(1),
        ]);
        assert_eq!(mask, 0xc2ff_ffff, "{mask:08X} doesn't match c2ff_ffff");
    }
}
