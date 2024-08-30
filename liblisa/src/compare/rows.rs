use std::collections::{HashMap, HashSet};

use super::group::{ComparisonMatrix, EncodingGroup};
use super::summary::{ArchComparisonSummary, ArchId, ArchInfo, SharedEncodingGroup, SharedEncodings};
use crate::arch::Arch;
use crate::compare::group::ComparisonResult;
use crate::encoding::indexed::IndexedEncodings;
use crate::instr::InstructionFilter;
use crate::semantics::Computation;

/// The key for a row in an architecture comparison table.
/// All encodings that have the same RowKey should be grouped into the same row.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RowKey(u64);

impl RowKey {
    /// Creates a new RowKey.
    ///
    /// The `exists` iterator should yield `num_arches` bools that determine whether the instructions exist for that architecture.
    ///
    /// The `check_equal` function should return true if the semantics for the two architectures (passed as indices) are equal.
    /// `check_equal` should return false if the instructions do not exist on one of the two architectures, but true if they do not exist on both architectures.
    pub fn new_from_iter(
        num_arches: usize, exists: impl Iterator<Item = bool>, mut check_equal: impl FnMut(usize, usize) -> bool,
    ) -> RowKey {
        let mut result = 0;

        for (index, exists) in exists.enumerate() {
            if exists {
                result |= 1 << index;
            }
        }

        for x in 0..num_arches {
            for y in x + 1..num_arches {
                if check_equal(x, y) {
                    let base_index = Self::index(num_arches, x, y);
                    result |= 1 << base_index;
                }
            }
        }

        RowKey(result)
    }

    fn index(num_arches: usize, x: usize, y: usize) -> usize {
        // y=0 maps nothing
        // y=1 maps x=0                     (((0 + 1) * 0) / 2 = 0)
        // y=2 maps x=0, x=1                (((1 + 1) * 1) / 2 = 1)
        // y=3 maps x=0, x=1, x=2           (((3 + 1) * 3) / 2 = 3)
        // y=4 maps x=0, x=1, x=2, x=3      (((4 + 1) * 4) / 2 = 6)
        (((y - 1) + 1) * (y - 1)) / 2 + x + num_arches
    }

    fn get(&self, num_arches: usize, x: usize, y: usize) -> bool {
        let (x, y) = (x.min(y), x.max(y));
        let base_index = Self::index(num_arches, x, y);

        (self.0 >> base_index) & 1 != 0
    }

    /// An `u64` representation of the `RowKey`.
    pub fn repr(&self) -> u64 {
        self.0
    }

    /// Returns an iterator that yields the smallest architecture index that has equivalent semantics, for each architecture.
    pub fn implementation_indices(&self, num_arches: usize) -> impl Iterator<Item = Option<usize>> + '_ {
        (0..num_arches).map(move |index| {
            if (self.0 >> index) & 1 != 0 {
                Some(
                    (0..index)
                        .find(|&smaller_index| self.get(num_arches, index, smaller_index))
                        .unwrap_or(index),
                )
            } else {
                None
            }
        })
    }

    /// Extracts sets of equivalent semantics.
    /// Returns `(equivalent_sets, missing)`, where `equivalent_sets` is a `Vec` containing one or more sets of architectures with equivalent semantics, and `missing` is a set of architectures on which the instructions described by this RowKey do not exist.
    pub fn extract_sets(&self, num_arches: usize) -> (Vec<Vec<usize>>, Vec<usize>) {
        let mut m = HashMap::new();
        let mut missing = Vec::new();
        for (index, implementation) in self.implementation_indices(num_arches).enumerate() {
            if let Some(implementation) = implementation {
                m.entry(implementation).or_insert_with(Vec::new).push(index);
            } else {
                missing.push(index);
            }
        }
        let mut v = m.into_values().collect::<Vec<_>>();
        v.sort();
        (v, missing)
    }
}

/// A row in the architecture comparison table.
#[derive(Clone, Debug)]
pub struct Row {
    key: RowKey,
    groups: Vec<(EncodingGroup, InstructionFilter, ComparisonMatrix)>,
    min_encodings: Vec<usize>,
}

impl Row {
    /// Returns the [`RowKey`] for the row.
    pub fn key(&self) -> RowKey {
        self.key
    }

    /// Returns all groups beloning to this row.
    pub fn groups(&self) -> &[(EncodingGroup, InstructionFilter, ComparisonMatrix)] {
        &self.groups
    }

    /// Returns the smallest number of encodings in this group for each architecture.
    pub fn min_encoding_counts(&self) -> &[usize] {
        &self.min_encodings
    }

    /// Consumes self and returns all groups beloning to this row.
    pub fn into_groups(self) -> impl Iterator<Item = (EncodingGroup, InstructionFilter, ComparisonMatrix)> {
        self.groups.into_iter()
    }
}

/// A collection of rows.
#[derive(Clone, Debug)]
pub struct Rows(Vec<Row>);

impl Rows {
    /// Builds [`Rows`] from a list of groups.
    pub fn build(groups: Vec<(EncodingGroup, InstructionFilter, ComparisonMatrix)>) -> Rows {
        let num_arches = groups[0].0.encodings_per_arch.len();
        let mut rows = HashMap::new();
        for (group, filter, matrix) in groups.into_iter() {
            let key = RowKey::new_from_iter(
                num_arches,
                (0..group.encodings_per_arch.len()).map(|index| matrix[(index, index)] != ComparisonResult::BothMissing),
                |index_a, index_b| {
                    index_a == index_b || {
                        use ComparisonResult::*;
                        match matrix[(index_a, index_b)] {
                            Equal => true,
                            NotEqual | OneWithoutSemantics => false,
                            // Reasoning: something exists on one side, but doesn't exist on the other side.
                            // So assuming perfect analysis, that indicates a missing instruction.
                            // However, in practice it happens because analysis missed an instruction.
                            LhsMissing | RhsMissing => false,
                            // Reasoning: we're effectively comparing an empty set with an empty set;
                            // So for all 0 instructions, both sides have the same semantics.
                            BothMissing => true,
                            // Reasoning: if neither side has semantics, let's just consider them not equal.
                            // If we had semantics they might have been equal, but we don't know that with the info we have.
                            BothWithoutSemantics => false,
                            Unknown => false, // TODO
                            // Reasoning: the encodings on one side are inconsistent (or at least they look that way to us).
                            // We have no idea if the encodings are actually equal, so let's just treat them as if they weren't.
                            Confusing => false,
                        }
                    }
                },
            );

            rows.entry(key).or_insert(Vec::new()).push((group, filter, matrix));
        }

        let mut rows = rows
            .into_iter()
            .map(|(row, groups)| {
                let mut min_encodings = vec![HashSet::new(); num_arches];

                for (group, ..) in groups.iter() {
                    for (ids, set) in group.encodings_per_arch.iter().zip(min_encodings.iter_mut()) {
                        set.extend(ids.iter().copied());
                    }
                }

                Row {
                    key: row,
                    groups,
                    min_encodings: min_encodings.iter().map(|set| set.len()).collect::<Vec<_>>(),
                }
            })
            .collect::<Vec<_>>();
        rows.sort_by_key(|row| {
            let num = row.min_encodings.iter().copied().filter(|&n| n != 0).min().unwrap_or(0);
            (
                usize::MAX - num,
                row.key.implementation_indices(num_arches).collect::<Vec<_>>(),
            )
        });

        Rows(rows)
    }

    /// Iterates over all rows.
    pub fn iter(&self) -> impl Iterator<Item = &Row> {
        self.0.iter()
    }

    /// Exports the rows to a summary format suitable for serialization.
    pub fn export_summary<A: Arch, C: Computation>(
        self, arch_names: Vec<String>, encodings: IndexedEncodings<A, C>,
    ) -> ArchComparisonSummary<A, C> {
        let num_arches = arch_names.len();
        ArchComparisonSummary {
            architectures: arch_names
                .into_iter()
                .map(|name| ArchInfo {
                    name,
                })
                .collect(),
            encodings: self
                .into_iter()
                .flat_map(|row| {
                    let (sets, _) = row.key().extract_sets(num_arches);
                    let groups = row.into_groups();

                    groups.into_iter().map(move |(group, filter, _)| SharedEncodingGroup {
                        filter: filter.clone(),
                        encodings: sets
                            .iter()
                            .map(|set| SharedEncodings {
                                architectures: set.iter().map(|&id| ArchId(id)).collect(),
                                encodings: set
                                    .iter()
                                    .map(|&index| &group.encodings_per_arch[index])
                                    .min_by_key(|ids| ids.len())
                                    .unwrap()
                                    .clone(),
                            })
                            .collect(),
                    })
                })
                .collect(),
            index: encodings,
        }
    }
}

impl IntoIterator for Rows {
    type Item = Row;
    type IntoIter = std::vec::IntoIter<Row>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
