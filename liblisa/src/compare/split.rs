use std::collections::HashSet;
use std::fmt::Debug;

use itertools::Itertools;
use log::{debug, info, trace};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::instr::{ByteFilter, FilterBit, InstructionFilter};
use crate::utils::minisat::{SatSolver, Term};
use crate::utils::EitherIter;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct EfficientFilter {
    mask: u128,
    value: u128,
    len: u8,
}

impl Debug for EfficientFilter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.as_instruction_filter(), f)
    }
}

impl EfficientFilter {
    pub fn new(filter: InstructionFilter) -> Self {
        Self {
            mask: filter.mask_as_u128(),
            value: filter.value_as_u128(),
            len: filter.len() as u8,
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    pub fn bit_len(&self) -> usize {
        self.len() * 8
    }

    pub fn as_instruction_filter(&self) -> InstructionFilter {
        InstructionFilter::new(
            (0..self.len())
                .rev()
                .map(|index| index * 8)
                .map(|n| ByteFilter::new((self.mask >> n) as u8, (self.value >> n) as u8)),
        )
    }

    pub fn overlaps(&self, other: &EfficientFilter) -> bool {
        let intersect_mask = self.mask & other.mask;
        self.value & intersect_mask == other.value & intersect_mask
    }

    pub fn covers(&self, other: &EfficientFilter) -> bool {
        // We don't need to check the length because it is assumed that EfficientFilter::covers is only called when the lengths are equal
        self.value & self.mask == other.value & self.mask && other.mask & self.mask == self.mask
    }

    pub fn set_nth_bit_from_right(&mut self, index: usize, bit: FilterBit) {
        match bit.as_u8() {
            Some(n) => {
                self.mask |= 1 << index;
                self.value &= !(1 << index);
                self.value |= (n as u128) << index;
            },
            None => {
                self.mask &= !(1 << index);
                self.value &= !(1 << index);
            },
        }
    }

    pub fn get_nth_bit_from_right(&self, index: usize) -> FilterBit {
        let mask = (self.mask >> index) & 1 != 0;
        let value = (self.value >> index) & 1 != 0;

        match (mask, value) {
            (false, _) => FilterBit::Wildcard,
            (true, false) => FilterBit::Is0,
            (true, true) => FilterBit::Is1,
        }
    }

    pub fn mask_indices_from_right(&self) -> impl Iterator<Item = usize> + '_ {
        let mut bitmap = (!self.mask) & !(u128::MAX << (self.bit_len()));
        (0..bitmap.count_ones()).map(move |_| {
            let candidate_index = bitmap.trailing_zeros() as usize;
            bitmap &= !(1 << candidate_index);
            candidate_index
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FilterGroup {
    filters: Vec<EfficientFilter>,
}

impl FilterGroup {
    pub fn new(filters: Vec<InstructionFilter>) -> Self {
        if !filters.is_empty() {
            assert!(filters.iter().all(|f| f.bit_len() == filters[0].bit_len()));
        }

        FilterGroup {
            filters: filters.into_iter().map(EfficientFilter::new).collect(),
        }
    }

    pub fn filters(&self) -> impl Iterator<Item = InstructionFilter> + '_ {
        self.filters.iter().map(|x| x.as_instruction_filter())
    }

    pub fn is_empty(&self) -> bool {
        self.filters.is_empty()
    }

    pub fn sub(&self, other: &FilterGroup) -> FilterGroup {
        fn sub_internal(
            current: &EfficientFilter, filters: &[EfficientFilter], result: &mut HashSet<EfficientFilter>,
            _explored: &mut HashSet<EfficientFilter>,
        ) {
            let indices = current.mask_indices_from_right().collect::<Vec<_>>();
            let mut solver = SatSolver::new(indices.len());
            for filter in filters.iter() {
                solver.and_not_conjunction(indices.iter().enumerate().flat_map(|(term_index, &bit_index)| {
                    match filter.get_nth_bit_from_right(bit_index) {
                        FilterBit::Is0 => Some(Term::ff(term_index as u8)),
                        FilterBit::Is1 => Some(Term::tt(term_index as u8)),
                        FilterBit::Wildcard => None,
                    }
                }));
            }

            solver.solve_with::<Option<()>>(|solution| {
                let mut filter = *current;
                for (&bit_index, &val) in indices.iter().zip(solution.iter()) {
                    match val {
                        Some(false) => filter.set_nth_bit_from_right(bit_index, FilterBit::Is0),
                        Some(true) => filter.set_nth_bit_from_right(bit_index, FilterBit::Is1),
                        None => (),
                    }
                }

                result.insert(filter);

                None
            });
        }

        if self.filters.is_empty() {
            return FilterGroup {
                filters: Vec::new(),
            }
        } else if other.filters.is_empty() {
            return self.clone()
        }

        assert_eq!(self.filters[0].bit_len(), other.filters[0].bit_len());

        let mut explored = HashSet::new();
        let mut result = HashSet::new();
        for filter in self.filters.iter() {
            let overlapping = other
                .filters
                .iter()
                .cloned()
                .filter(|other| filter.overlaps(other))
                .collect::<Vec<_>>();
            if !overlapping.iter().any(|other| other.covers(filter)) {
                sub_internal(filter, &overlapping, &mut result, &mut explored)
            }
        }

        FilterGroup {
            filters: result.into_iter().collect(),
        }
    }
}

/// Splits the encoding group into multiple groups, such that each group
/// contains encodings that cover the exact same space.
/// This function is one-to-many. That is, it will generate many smaller groups that each cover a small subset.
pub fn compute_split_filters(mut item: Vec<Vec<InstructionFilter>>) -> impl Iterator<Item = InstructionFilter> {
    // Happy path: consider filters shared by all 5 architectures first, don't process them below
    let shared_filters = {
        let mut v = Vec::new();

        let (first, rest) = item.split_first_mut().unwrap();
        first.retain(|filter| {
            if rest.iter().all(|v| v.contains(filter)) {
                for list in rest.iter_mut() {
                    list.remove(list.iter().position(|p| p == filter).unwrap());
                }

                v.push(filter.clone());

                false
            } else {
                true
            }
        });

        v
    };

    let mut num_removed = 0;
    for filters in item.iter_mut() {
        'outer: loop {
            for (filter_index, filter) in filters.iter().enumerate() {
                if filters.iter().enumerate().any(|(n, f)| n != filter_index && f.covers(filter)) {
                    filters.remove(filter_index);
                    num_removed += 1;
                    continue 'outer;
                }
            }

            break
        }
    }

    info!("Removed {num_removed} unneeded filters");

    info!(
        "Need to check {} filters ({} * {} eliminated)",
        item.iter().map(|v| v.len()).sum::<usize>(),
        shared_filters.len(),
        item.len()
    );
    let mut groups = vec![item];

    for _ in 0..10 {
        groups = groups
            .into_iter()
            .enumerate()
            .flat_map(|(group_index, group)| {
                let num_filters = group.iter().map(|v| v.len()).sum::<usize>();
                if num_filters > 500 {
                    trace!("Filters for group {group_index}: {group:#?}");
                    trace!("Filter count: {num_filters}");

                    EitherIter::Left(split_groups(group).into_iter())
                } else {
                    EitherIter::Right([group].into_iter())
                }
            })
            .collect::<Vec<_>>();
    }

    info!("{} groups", groups.len());

    groups
        .into_iter()
        .flat_map(compute_split_filters_internal)
        .chain(shared_filters)
}

fn split_groups(item: Vec<Vec<InstructionFilter>>) -> [Vec<Vec<InstructionFilter>>; 2] {
    let num_bits = item.iter().flatten().next().unwrap().bit_len();
    let bit_to_split = (0..num_bits)
        .max_by_key(|&bit_index| {
            let [num_zero, num_one, num_shared] = item
                .iter()
                .flatten()
                .map(|filter| match filter.nth_bit_from_left(bit_index) {
                    FilterBit::Is0 => [1, 0, 0],
                    FilterBit::Is1 => [0, 1, 0],
                    FilterBit::Wildcard => [0, 0, 1],
                })
                .reduce(|[a, b, c], [x, y, z]| [a + x, b + y, c + z])
                .unwrap();

            debug!("Bit{bit_index}: ({num_shared} shared) {num_zero} zero : {num_one} one");
            let score = num_one.min(num_zero) * 100 - num_shared;
            debug!("Score = {score:5}");

            score
        })
        .unwrap();

    info!("Splitting on bit {bit_to_split}");

    [(FilterBit::Is0, FilterBit::Is1), (FilterBit::Is0, FilterBit::Is1)].map(|(set_to, exclude)| {
        item.iter()
            .map(|v| {
                v.iter()
                    .filter(|filter| filter.nth_bit_from_left(bit_to_split) != exclude)
                    .map(|filter| {
                        let mut filter = filter.clone();
                        filter.set_nth_bit_from_left(bit_to_split, set_to);
                        filter
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    })
}

fn compute_split_filters_internal(item: Vec<Vec<InstructionFilter>>) -> impl Iterator<Item = InstructionFilter> {
    // matrix_x_without_y[X][Y] are the filters in X but not in Y.
    let matrix_x_without_y = item
        .par_iter()
        .with_max_len(1)
        .map(|a| {
            item.par_iter()
                .with_max_len(1)
                .map(|b| {
                    info!(" - {}x{}: {a:?} x {b:?}", a.len(), b.len());

                    let x = FilterGroup::new(a.clone());
                    let y = FilterGroup::new(b.clone());
                    // println!("{} filters - {} filters", x.filters.len(), y.filters.len());
                    let x_without_y = x.sub(&y);

                    if !x_without_y.is_empty() {
                        info!("{a:?} - {b:?} = {:?}", x_without_y.filters().format(", "));
                    }

                    // println!("{} filters - {} filters = {} filters",  x.filters.len(), y.filters.len(), x_without_y.filters.len());

                    x_without_y.filters().collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // println!("Computing configurations...");

    (1..(1u64 << item.len()))
        .into_par_iter()
        .flat_map(move |config| {
            let (included_indices, excluded_indices): (Vec<_>, _) = item
                .iter()
                .enumerate()
                .map(|(index, _)| index)
                .partition(|index| config & (1 << index) != 0);
            let base_filters = included_indices
                .iter()
                .map(|&index| &item[index])
                .min_by_key(|v| v.len())
                .unwrap()
                .clone();
            let base = FilterGroup::new(base_filters);

            info!("Computing filters for configuration {included_indices:?} - {excluded_indices:?}");
            let matrix_x_without_y = &matrix_x_without_y;
            // We want to compute the filters commonly present in `included_indices`, but not in `excluded_indices`.
            // To do this we need to exclude all filters in `excluded_indices`,
            // as well as any filters not shared between two items in `included_indices`.
            let excluded_filters = excluded_indices
                .iter()
                .flat_map(|&index| item[index].iter())
                .chain(
                    included_indices
                        .iter()
                        .flat_map(|&a| included_indices.iter().flat_map(move |&b| matrix_x_without_y[a][b].iter())),
                )
                .unique()
                .cloned()
                .collect::<Vec<_>>();
            let g2 = FilterGroup::new(excluded_filters);
            let shared = base.sub(&g2);

            shared.filters().collect::<Vec<_>>()
        })
        .collect::<HashSet<_>>()
        .into_iter()
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use test_log::test;

    use super::EfficientFilter;
    use crate::compare::split::FilterGroup;
    use crate::instr::{FilterBit, InstructionFilter};

    #[test]
    pub fn efficient_filter_set_bit() {
        let filter = InstructionFilter::parse("01000011 00001111 01000101 01010100 __000000 _____100");

        for index in 0..filter.bit_len() {
            for bit in [FilterBit::Is0, FilterBit::Is1, FilterBit::Wildcard] {
                let mut f = filter.clone();
                let mut ef = EfficientFilter::new(f.clone());
                f.set_nth_bit_from_right(index, bit);
                ef.set_nth_bit_from_right(index, bit);

                assert_eq!(f, ef.as_instruction_filter());
            }
        }
    }

    #[test]
    pub fn sub_is_minimal() {
        let a = vec![InstructionFilter::parse("0110__10")];
        let b = vec![InstructionFilter::parse("0110__0_"), InstructionFilter::parse("0110101_")];

        let a = FilterGroup::new(a);
        let b = FilterGroup::new(b);

        let result = a.sub(&b);

        assert_eq!(
            result.filters().sorted().collect::<Vec<_>>(),
            vec![InstructionFilter::parse("0110_110"), InstructionFilter::parse("01100_10"),]
        )
    }
}
