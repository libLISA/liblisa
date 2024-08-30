use std::collections::{HashMap, HashSet};
use std::iter::repeat;
use std::ops::{Index, IndexMut};
use std::sync::atomic::{AtomicBool, Ordering};

use itertools::Itertools;
use log::{debug, trace};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use super::split::compute_split_filters;
use super::EncodingComparisonOptions;
use crate::arch::Arch;
use crate::encoding::indexed::{EncodingId, IndexedEncodings};
use crate::encoding::EncodingWithFilters;
use crate::instr::{ByteFilter, InstructionFilter, WithFilters};
use crate::semantics::default::computation::SynthesizedComputation;
use crate::semantics::Computation;
use crate::smt::SolverProvider;
use crate::utils::bitmap::GrowingBitmap;
use crate::utils::Symmetric2DMatrix;

/// The result of a pairwise comparison between two encodings.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum ComparisonResult {
    /// The encoding are equal.
    Equal,

    /// The encodings are different.
    NotEqual,

    /// The left-hand side is missing.
    LhsMissing,

    /// The right-hand side is missing.
    RhsMissing,

    /// Both sides are missing
    BothMissing,

    /// One side does not have semantics (but does have at least one encoding)
    OneWithoutSemantics,

    /// Both sides do not have semantics (but do have encodings)
    BothWithoutSemantics,

    /// Equivalence has not been determined
    Unknown,

    /// Overlapping encodings on one side have conflicting semantics
    Confusing,
}

impl ComparisonResult {
    fn invert(&self) -> ComparisonResult {
        use ComparisonResult::*;
        match self {
            LhsMissing => RhsMissing,
            RhsMissing => LhsMissing,
            rest => *rest,
        }
    }
}

/// A matrix of pairwise comparisons between all architectures.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ComparisonMatrix(Vec<Vec<ComparisonResult>>);

impl From<Vec<Vec<ComparisonResult>>> for ComparisonMatrix {
    fn from(value: Vec<Vec<ComparisonResult>>) -> Self {
        assert!(value.iter().all(|v| v.len() == value.len()), "vectors must have equal sizes");

        Self(value)
    }
}

impl ComparisonMatrix {
    /// Creates a matrix with all fields set to `Unknown`.
    pub fn new(size: usize) -> Self {
        Self(vec![vec![ComparisonResult::Unknown; size]; size])
    }

    fn find_all_equal(&self, index: usize) -> Vec<usize> {
        let mut frontier = vec![index];
        let mut seen = GrowingBitmap::new();

        while let Some(index) = frontier.pop() {
            for (index, &c) in self.0[index].iter().enumerate() {
                if c == ComparisonResult::Equal && seen.set(index) {
                    frontier.push(index);
                }
            }
        }

        seen.iter_one_indices().collect()
    }

    /// Iterates over the entire matrix.
    pub fn iter_all(&self) -> impl Iterator<Item = ComparisonResult> + '_ {
        self.0.iter().flatten().copied()
    }

    /// Propagates the ComparisonResult in `(index_a, index_b)` to the rest of the matrix.
    ///
    /// For example, if A is equal to B and B is equal to C, this method ensures that A is also set equal to C.
    pub fn propagate_result(&mut self, index_a: usize, index_b: usize) {
        match self[(index_a, index_b)] {
            // - if a == b && b == c, then a == c
            ComparisonResult::Equal => {
                let a_indices = self.find_all_equal(index_a);
                let b_indices = self.find_all_equal(index_b);

                for &a_index in a_indices.iter() {
                    for &b_index in b_indices.iter() {
                        self[(a_index, b_index)] = ComparisonResult::Equal;
                        self[(b_index, a_index)] = ComparisonResult::Equal;
                    }
                }
            },
            // - if a != b && b == c, then a != c
            ComparisonResult::NotEqual => {
                let a_indices = self.find_all_equal(index_a);
                let b_indices = self.find_all_equal(index_b);

                for &a_index in a_indices.iter() {
                    for &b_index in b_indices.iter() {
                        self[(a_index, b_index)] = ComparisonResult::NotEqual;
                        self[(b_index, a_index)] = ComparisonResult::NotEqual;
                    }
                }
            },
            _ => (),
        }
    }
}

impl Index<(usize, usize)> for ComparisonMatrix {
    type Output = ComparisonResult;

    fn index(&self, (x, y): (usize, usize)) -> &Self::Output {
        &self.0[x][y]
    }
}

impl IndexMut<(usize, usize)> for ComparisonMatrix {
    fn index_mut(&mut self, (x, y): (usize, usize)) -> &mut Self::Output {
        &mut self.0[x][y]
    }
}

/// For each architecture, a group of overlapping encodings.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncodingGroup {
    /// The encodings per architecture.
    pub encodings_per_arch: Vec<Vec<EncodingId>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct FilterId(usize);

struct ArchData {
    encodings: Vec<(EncodingId, Vec<FilterId>)>,
    unprocessed: GrowingBitmap,
}

struct FilterLookupEntry {
    filter: InstructionFilter,
    related_ids: HashSet<FilterId>,
}

impl EncodingGroup {
    /// Computes a set of [`EncodingGroup`]s that cover all encodings provided in `arches`.
    pub fn compute_from_arches<A: Arch, C: Computation + Send + Sync>(
        encodings: &IndexedEncodings<A, C>, arches: Vec<Vec<EncodingId>>,
    ) -> Vec<EncodingGroup> {
        let arches_by_instr_len = {
            let mut arches_by_instr_len = vec![vec![Vec::new(); arches.len()]; 16];
            for (arch_index, ids) in arches.into_iter().enumerate() {
                for id in ids.into_iter() {
                    let len = encodings[id].encoding.bits.len() / 8;
                    arches_by_instr_len[len][arch_index].push(id);
                }
            }

            arches_by_instr_len
        };

        let items = arches_by_instr_len
            .into_par_iter()
            .with_max_len(1)
            .map(|arches| {
                let mut id_map = HashMap::new();
                let mut filter_lookup = Vec::new();

                // Assign IDs to all filters
                let arches = arches
                    .into_iter()
                    .map(|ids| ArchData {
                        unprocessed: GrowingBitmap::new_all_ones(ids.len()),
                        encodings: ids
                            .into_iter()
                            .map(|id| {
                                let filter_ids = encodings[id]
                                    .filters
                                    .iter()
                                    .map(|filter| {
                                        if let Some(id) = id_map.get(filter) {
                                            *id
                                        } else {
                                            let id = FilterId(filter_lookup.len());
                                            let prev = id_map.insert(filter.clone(), id);
                                            assert!(prev.is_none());
                                            filter_lookup.push(FilterLookupEntry {
                                                filter: filter.clone(),
                                                related_ids: HashSet::new(),
                                            });

                                            id
                                        }
                                    })
                                    .collect::<Vec<_>>();

                                for id in filter_ids.iter() {
                                    filter_lookup[id.0].related_ids.extend(filter_ids.iter().copied());
                                }

                                (id, filter_ids)
                            })
                            .collect::<Vec<_>>(),
                    })
                    .collect::<Vec<_>>();

                let filter_overlap = {
                    let index_groups = {
                        let mut groups = vec![Vec::new(); 16];
                        for (index, lookup_entry) in filter_lookup.iter().enumerate() {
                            groups[lookup_entry.filter.byte_len()].push(index);
                        }

                        groups.into_iter().filter(|g| !g.is_empty()).collect::<Vec<_>>()
                    };

                    let mut filter_overlap = Symmetric2DMatrix::new();
                    // Now, we compute the overlap between all filters
                    for indices in index_groups.iter() {
                        for (offset_a, &index_a) in indices.iter().enumerate() {
                            // n += 1;
                            for &index_b in indices.iter().skip(offset_a) {
                                let a = &filter_lookup[index_a].filter;
                                let b = &filter_lookup[index_b].filter;
                                if a.overlaps(b) {
                                    filter_overlap.set(index_a, index_b);
                                }
                            }
                        }
                    }

                    filter_overlap
                };

                (arches, filter_overlap, filter_lookup)
            })
            .collect::<Vec<_>>();

        items
            .into_par_iter()
            .with_max_len(1)
            .flat_map(|(mut arches, filter_overlap, filter_lookup)| {
                let mut groups = Vec::new();

                while let Some((arch_index, encoding_index)) = arches
                    .iter()
                    .enumerate()
                    .flat_map(|(index, data)| data.unprocessed.first_bit_set().map(|encoding_index| (index, encoding_index)))
                    .next()
                {
                    let arch = &arches[arch_index];
                    let (_, encoding_filter_ids) = &arch.encodings[encoding_index];

                    let mut filter_ids_matched = GrowingBitmap::new();
                    let mut filter_ids_to_process = encoding_filter_ids.clone();

                    while let Some(filter_id) = filter_ids_to_process.pop() {
                        filter_ids_to_process.extend(
                            filter_overlap
                                .iter_row_indices(filter_id.0)
                                .flat_map(|index| filter_lookup[index].related_ids.iter().copied())
                                .filter(|filter_id| filter_ids_matched.set(filter_id.0)),
                        );
                    }

                    let group = EncodingGroup {
                        encodings_per_arch: arches
                            .iter_mut()
                            .map(|arch| {
                                arch.encodings
                                    .iter()
                                    .enumerate()
                                    .filter(|(_, (_, filter_ids))| filter_ids.iter().any(|id| filter_ids_matched.get(id.0)))
                                    .map(|(index, &(e, _))| {
                                        arch.unprocessed.reset(index);

                                        e
                                    })
                                    .collect()
                            })
                            .collect(),
                    };
                    groups.push(group);
                }

                groups
            })
            .collect::<Vec<_>>()
    }

    /// The total number of encodings in the group, accross all architectures.
    pub fn num_encodings(&self) -> usize {
        self.encodings_per_arch.iter().map(|e| e.len()).sum()
    }

    /// Checks whether the bitpatterns for the encodings are equivalent between all groups.
    pub fn all_identical_bitpatterns<A: Arch, C: Computation>(&self, encodings: &IndexedEncodings<A, C>) -> bool {
        let mut first = None;
        for ids in self.encodings_per_arch.iter() {
            if ids.len() > 1 {
                return false
            }

            if let Some(id) = ids.first() {
                if let Some(first) = first.as_ref() {
                    if encodings[id].encoding.bits != *first {
                        return false
                    }
                } else {
                    first = Some(encodings[id].encoding.bits.clone());
                }
            }
        }

        true
    }

    /// Returns the byte length of the instructions in this group.
    pub fn byte_len<A: Arch, C: Computation>(&self, encodings: &IndexedEncodings<A, C>) -> usize {
        let id = self.encodings_per_arch.iter().flatten().next().unwrap();

        encodings[id].encoding.instr().byte_len()
    }

    /// Filters the encodings by `filter` and only returns encodings for which match `filter` at least partially.
    pub fn only_matching<A: Arch, C: Computation>(
        &self, encodings: &IndexedEncodings<A, C>, filter: &InstructionFilter,
    ) -> EncodingGroup {
        EncodingGroup {
            encodings_per_arch: self
                .encodings_per_arch
                .iter()
                .map(|ids| {
                    ids.iter()
                        .copied()
                        .filter(|&id| encodings[id].filters.iter().any(|f| f.overlaps(filter)))
                        .collect()
                })
                .collect(),
        }
    }

    /// Compares the encodings in the groups and builds a [`ComparisonMatrix`] with the comparison results.
    pub fn compare<A: Arch>(
        &self, encodings: &IndexedEncodings<A, SynthesizedComputation>, filter: &InstructionFilter, solver: &impl SolverProvider,
    ) -> ComparisonMatrix {
        let encoding_set = self
            .encodings_per_arch
            .iter()
            .map(|ids| {
                ids.iter()
                    .flat_map(|id| encodings[id].encoding.restrict_to(filter).ok())
                    .unique()
                    .map(EncodingWithFilters::new)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        Self::build_comparison_matrix(solver, encoding_set)
    }

    fn build_comparison_matrix<A: Arch>(
        solver: &impl SolverProvider, encoding_set: Vec<Vec<EncodingWithFilters<A, SynthesizedComputation>>>,
    ) -> ComparisonMatrix {
        let mut comparison_matrix = ComparisonMatrix::new(encoding_set.len());
        for (index, set) in encoding_set.iter().enumerate() {
            trace!("Architecture #{index} contains {} encodings", set.len());
            comparison_matrix[(index, index)] = if set.is_empty() {
                ComparisonResult::BothMissing
            } else {
                ComparisonResult::Equal
            };
        }

        trace!("Intermediate resulting comparison matrix: {comparison_matrix:?}");

        let confusing = encoding_set
            .iter()
            .map(|set| Self::is_confusing(solver, set))
            .collect::<Vec<_>>();

        for (index_a, a) in encoding_set.iter().enumerate() {
            for (index_b, b) in encoding_set.iter().enumerate().skip(index_a + 1) {
                if comparison_matrix[(index_a, index_b)] == ComparisonResult::Unknown {
                    trace!("Comparing architecture #{index_a} vs #{index_b}");
                    let result = if confusing[index_a] || confusing[index_b] {
                        ComparisonResult::Confusing
                    } else if a == b && !a.is_empty() && a.iter().all(|e| e.encoding.all_outputs_have_computations()) {
                        ComparisonResult::Equal
                    } else {
                        Self::compare_semantics(solver, a, b)
                    };

                    trace!("Result: {result:?}");

                    comparison_matrix[(index_a, index_b)] = result;
                    comparison_matrix[(index_b, index_a)] = result.invert();

                    comparison_matrix.propagate_result(index_a, index_b);

                    trace!("Propagated: {comparison_matrix:?}");
                }
            }
        }

        trace!("Comparison matrix: {comparison_matrix:?}");

        comparison_matrix
    }

    fn is_confusing<A: Arch>(solver: &impl SolverProvider, a: &[EncodingWithFilters<A, SynthesizedComputation>]) -> bool {
        #[cfg(not(debug_assertions))]
        let w = a.par_windows(2);
        #[cfg(debug_assertions)]
        let mut w = a.windows(2);

        w.any(|items| {
            let first = &items[0];
            let second = &items[1];

            // If we have some encodings with missing semantics, we'll allow them to be treated as equal.
            // Since all encodings are from the same architecture, we can be a little less strict and assume that encodings are equal unless proven otherwise.
            let mut options = OPTIONS.clone();
            options.treat_missing_as_equal = true;
            let result = solver.with_solver(|mut solver| {
                super::encodings_semantically_equal(&options, &first.encoding, &second.encoding, &mut solver)
            });

            let confusing = !result.equal || result.timeout;

            if confusing {
                let overlapping = first
                    .encoding
                    .bitpattern_as_filter()
                    .intersect(&second.encoding.bitpattern_as_filter());
                debug!(
                    "Confused between {} and {}",
                    first.encoding.restrict_to(&overlapping).unwrap(),
                    second.encoding.restrict_to(&overlapping).unwrap()
                );
            }

            confusing
        })
    }

    fn compare_semantics<A: Arch>(
        solver: &impl SolverProvider, a: &[EncodingWithFilters<A, SynthesizedComputation>],
        b: &[EncodingWithFilters<A, SynthesizedComputation>],
    ) -> ComparisonResult {
        match (a.len(), b.len()) {
            (0, 0) => ComparisonResult::BothMissing,
            (0, _) => ComparisonResult::LhsMissing,
            (_, 0) => ComparisonResult::RhsMissing,
            _ => {
                // We assume we've already ruled out confusingness

                let mut equal = true;
                let lhs_missing_semantics = a.iter().any(|a| !a.encoding.all_outputs_have_computations());
                let rhs_missing_semantics = b.iter().any(|b| !b.encoding.all_outputs_have_computations());

                // TODO: This might compare the same area multiple times...
                // TODO: We already know that all encodings in a or b are equal. So we only need to compare each part of the instruction space once.
                let comparisons = a
                    .iter()
                    .flat_map(|a| b.iter().map(move |b| (a, b)))
                    .filter(|(a, b)| a.encoding.bitpattern_as_filter().overlaps(&b.encoding.bitpattern_as_filter()))
                    .collect::<Vec<_>>();
                let abort = AtomicBool::new(false);
                #[cfg(not(debug_assertions))]
                let iter = comparisons.par_iter().with_max_len(16);
                #[cfg(debug_assertions)]
                let iter = comparisons.iter();
                let results = iter
                    .flat_map(|(a, b)| {
                        if abort.load(Ordering::Relaxed) {
                            None
                        } else {
                            let result = solver.with_solver(|mut solver| {
                                super::encodings_semantically_equal(OPTIONS, &a.encoding, &b.encoding, &mut solver)
                            });
                            if result.timeout || !result.equal {
                                abort.store(true, Ordering::Relaxed);
                            }

                            trace!("Result from encodings_semantically_equal: {result:?}");

                            Some(result)
                        }
                    })
                    .collect::<Vec<_>>();
                for result in results {
                    if result.timeout {
                        return ComparisonResult::Unknown
                    }

                    equal &= result.equal;
                    if !result.equal {
                        break
                    }
                }

                if equal {
                    if lhs_missing_semantics && rhs_missing_semantics {
                        ComparisonResult::BothWithoutSemantics
                    } else if lhs_missing_semantics || rhs_missing_semantics {
                        ComparisonResult::OneWithoutSemantics
                    } else {
                        ComparisonResult::Equal
                    }
                } else {
                    ComparisonResult::NotEqual
                }
            },
        }
    }

    /// Splits the group into exact, non-overlapping, subgroups.
    pub fn split_exact<A: Arch, C: Computation>(
        &self, encodings: &IndexedEncodings<A, C>,
    ) -> Vec<(EncodingGroup, InstructionFilter)> {
        let filters = self
            .encodings_per_arch
            .iter()
            .filter(|es| !es.is_empty())
            .map(|es| {
                es.iter()
                    .flat_map(|id| encodings[id].filters.iter())
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let filter_overlap = ensure_filter_overlap(&filters);

        let non_overlapping_filters = if !filter_overlap {
            let group_filters = self
                .encodings_per_arch
                .iter()
                .map(|es| {
                    es.iter()
                        .flat_map(|id| encodings[id].filters().iter())
                        .cloned()
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            compute_split_filters(group_filters).unique().collect::<Vec<_>>()
        } else {
            vec![InstructionFilter::new(
                repeat(ByteFilter::new(0, 0)).take(filters.iter().flatten().next().unwrap().byte_len()),
            )]
        };

        let result = non_overlapping_filters;

        result
            .into_iter()
            .map(|filter| {
                let new_group = self.only_matching(encodings, &filter);
                (new_group, filter)
            })
            .collect::<Vec<_>>()
    }

    /// Checks whether any encodings overlap the filter `restrict`.
    pub fn has_encodings_overlapping_filter<A: Arch>(
        &self, encodings: &IndexedEncodings<A, SynthesizedComputation>, restrict: &InstructionFilter,
    ) -> bool {
        self.encodings_per_arch
            .iter()
            .flatten()
            .all(|id| encodings[id].encoding.restrict_to(restrict).is_ok())
    }

    /// Checks whether all encodings for all architectures have successfully synthesized computations.
    pub fn all_encodings_have_computations<A: Arch, C: Computation>(&self, encodings: &IndexedEncodings<A, C>) -> bool {
        self.encodings_per_arch
            .iter()
            .flatten()
            .all(|id| encodings[id].encoding.all_outputs_have_computations())
    }
}

fn ensure_filter_overlap(sets: &[Vec<InstructionFilter>]) -> bool {
    for window in sets.windows(2) {
        if let [lhs, rhs] = window {
            for item in lhs.iter() {
                if let Some(instr) = item.find_uncovered_instr(rhs.to_vec()) {
                    trace!("Found {instr:?}, which is not (fully) covered by {rhs:?}");
                    return false
                }
            }

            for item in rhs.iter() {
                if let Some(instr) = item.find_uncovered_instr(lhs.to_vec()) {
                    trace!("Found {instr:?}, which is not (fully) covered by {lhs:?}");
                    return false
                }
            }
        } else {
            unreachable!("This should never happen, because sets.windows(2) always returns slices of length 2");
        }
    }

    true
}

const OPTIONS: &EncodingComparisonOptions = &{
    let mut o = EncodingComparisonOptions::new();
    o.addresses.allow_size_differences = true;
    o.addresses.allow_alignment_differences = true;
    o
};

#[cfg(test)]
mod tests {
    use super::{ComparisonMatrix, ComparisonResult};

    #[test]
    pub fn test_propagate_result() {
        use ComparisonResult::*;
        let mut comparison_matrix = ComparisonMatrix::from(vec![
            vec![Equal, Equal, Equal, Equal, Equal],
            vec![Equal, Equal, Unknown, Unknown, Unknown],
            vec![Equal, Unknown, Equal, Unknown, Unknown],
            vec![Equal, Unknown, Unknown, Equal, Unknown],
            vec![Equal, Unknown, Unknown, Unknown, Equal],
        ]);

        comparison_matrix.propagate_result(0, 1);

        assert_eq!(
            comparison_matrix,
            ComparisonMatrix::from(vec![
                vec![Equal, Equal, Equal, Equal, Equal,],
                vec![Equal, Equal, Equal, Equal, Equal,],
                vec![Equal, Equal, Equal, Equal, Equal,],
                vec![Equal, Equal, Equal, Equal, Equal,],
                vec![Equal, Equal, Equal, Equal, Equal,],
            ])
        );

        let mut comparison_matrix = ComparisonMatrix::from(vec![
            vec![Equal, NotEqual, Equal, Equal, Equal],
            vec![NotEqual, Equal, Unknown, Unknown, Unknown],
            vec![Equal, Unknown, Equal, Unknown, Unknown],
            vec![Equal, Unknown, Unknown, Equal, Unknown],
            vec![Equal, Unknown, Unknown, Unknown, Equal],
        ]);

        comparison_matrix.propagate_result(0, 1);

        assert_eq!(
            comparison_matrix,
            ComparisonMatrix::from(vec![
                vec![Equal, NotEqual, Equal, Equal, Equal,],
                vec![NotEqual, Equal, NotEqual, NotEqual, NotEqual,],
                vec![Equal, NotEqual, Equal, Unknown, Unknown,],
                vec![Equal, NotEqual, Unknown, Equal, Unknown,],
                vec![Equal, NotEqual, Unknown, Unknown, Equal,],
            ])
        );
    }
}
