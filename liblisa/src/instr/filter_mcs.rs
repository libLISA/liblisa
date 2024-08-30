use std::collections::HashSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use fxhash::FxHashSet;
use itertools::Itertools;
use log::{debug, info, trace};
use rayon::prelude::*;

use super::WithFilters;
use crate::instr::{Instruction, InstructionFilter};
use crate::utils::bitmap::GrowingBitmap;
use crate::utils::MinimumCoveringSet;

pub struct MinimumCoveringFilterSet<T: WithFilters> {
    items: Vec<T>,
    group_maps: Vec<GrowingBitmap>,
}

impl<T: WithFilters + Clone + Send + Sync> MinimumCoveringFilterSet<T> {
    fn find_intersections3(
        depth: usize, current: &InstructionFilter, seen: &mut FxHashSet<InstructionFilter>,
        item_filters: &[Vec<InstructionFilter>], pre_chosen_filters: &[InstructionFilter],
        mut exclusion_filters: Vec<InstructionFilter>, result: &mut HashSet<Instruction>,
    ) {
        #[cfg(debug_assertions)]
        if depth > 0 && !seen.insert(current.clone()) {
            panic!("Already checked {current:?}");
        }

        if seen.len() % 50000 == 0 && !seen.is_empty() {
            debug!("Checked {} filters, generated {} instructions", seen.len(), result.len());
        }

        trace!("Checking {current:?} with {} overlapping filters", item_filters.len());
        for (index, filters) in item_filters.iter().enumerate() {
            for filter in filters.iter() {
                debug_assert_eq!(current.byte_len(), filter.byte_len());
                debug_assert!(current.covers(filter));

                if depth < 2 {
                    debug!("Depth {depth}: Checked {}/{} overlaps", index, item_filters.len());
                }

                let intersection = current.intersect(filter);
                trace!("Intersection: {intersection:?}");

                if intersection == *current {
                    if let Some(instr) = intersection.find_uncovered_instr(pre_chosen_filters.to_vec()) {
                        trace!("Skipping intersection that doesn't reduce scope: {instr:?}");
                        result.insert(instr);
                    }

                    continue
                }

                let mut s = FxHashSet::default();
                let overlapping_filters = item_filters[index + 1..]
                    .iter()
                    .map(|f| {
                        let mut v = f
                            .iter()
                            .filter(|f| intersection.overlaps(f))
                            .map(|f| intersection.intersect(f))
                            .unique()
                            .collect::<Vec<_>>();
                        v.sort();
                        v
                    })
                    .filter(|f| !f.is_empty())
                    .filter(|f| s.insert(f.clone()))
                    .filter(|f| f.iter().any(|f| f.find_uncovered_instr(exclusion_filters.clone()).is_some()))
                    .filter(|f| f.iter().all(|f| f != &intersection))
                    .unique()
                    .collect::<Vec<_>>();

                if !overlapping_filters.is_empty() {
                    trace!(
                        "Recursing with {} filters (down from {})",
                        overlapping_filters.len(),
                        item_filters.len()
                    );
                    if intersection.find_uncovered_instr(exclusion_filters.clone()).is_some() {
                        Self::find_intersections3(
                            depth + 1,
                            &intersection,
                            seen,
                            &overlapping_filters,
                            pre_chosen_filters,
                            exclusion_filters.clone(),
                            result,
                        );
                    }
                }

                let r = overlapping_filters
                    .into_iter()
                    .flatten()
                    .chain(exclusion_filters.iter().cloned())
                    .collect::<Vec<_>>();
                if let Some(instr) = intersection.find_uncovered_instr(r) {
                    trace!("Found instruction: {instr:?} for {intersection:?} - {exclusion_filters:?}");
                    result.insert(instr);
                }

                exclusion_filters.push(intersection);
            }
        }
    }

    pub fn new(items: Vec<T>, pre_chosen: &[T]) -> Self {
        // TODO: Add exclusion of already-chosen items
        // Determine which items we need to take. If an item is fully covered by another item, we can drop it.
        let mut take = GrowingBitmap::new();
        for (index, item) in items.iter().enumerate() {
            if !take[index] {
                if let Some(covering_index) = items.iter().enumerate().position(|(other_index, other_item)| {
                    index != other_index
                        && item
                            .filters()
                            .iter()
                            .all(|filter| other_item.filters().iter().any(|other_filter| other_filter.covers(filter)))
                }) {
                    take.set(covering_index);
                } else {
                    take.set(index);
                }
            }
        }
        debug!("Items taken: {take:?}");
        let items = items
            .iter()
            .enumerate()
            .filter(|&(index, _)| take[index])
            .map(|(_, e)| e.clone())
            .collect::<Vec<_>>();

        let pre_chosen_filters = pre_chosen
            .iter()
            .flat_map(|item| item.filters().iter())
            .cloned()
            .collect::<Vec<_>>();

        let start = Instant::now();

        let covering_instrs = {
            info!("Computing instructions...");
            let mut results = HashSet::new();

            let item_filters = items
                .iter()
                .map(|e| {
                    let mut v = e.filters().to_vec();
                    v.sort();
                    v
                })
                .unique()
                // TODO: Filter out filters/encodings that are completely covered by the pre_chosen_filters
                .collect::<Vec<_>>();

            info!(
                "Computing instructions that can prove full filter coverage for {} filters in {} items: {item_filters:?}",
                item_filters.len(),
                items.len()
            );
            debug!("Pre-chosen: {:?}", pre_chosen.iter().map(|t| t.filters()).format(", "));

            let find_intersections =
                |(matching, overlapping_references, exclusion_filters): (&InstructionFilter, Vec<Vec<_>>, Vec<_>)| {
                    let mut set = HashSet::new();

                    Self::find_intersections3(
                        0,
                        matching,
                        &mut Default::default(),
                        &overlapping_references,
                        &pre_chosen_filters,
                        exclusion_filters,
                        &mut set,
                    );
                    set
                };

            let mut intersections_to_find = Vec::new();
            let mut exclusion_filters: HashSet<InstructionFilter> = HashSet::new();

            exclusion_filters.extend(pre_chosen_filters.iter().cloned());

            for (index_a, filters) in item_filters.iter().enumerate() {
                debug!("Checking item {index_a}/{}: {filters:?}", item_filters.len());
                for matching in filters.iter() {
                    if !exclusion_filters.contains(matching) {
                        if matching
                            .find_uncovered_instr(exclusion_filters.iter().cloned().collect())
                            .is_none()
                        {
                            debug!("Skipping {matching:?}, because is covered by exclusion_filters: {exclusion_filters:?}");
                            // If we will not be able to find any instructions within `matching`, we can skip it.
                            continue
                        }

                        let overlapping = item_filters
                            .iter()
                            .enumerate()
                            .filter(|&(index_b, filters)| index_a != index_b && filters.iter().any(|f| f.overlaps(matching)))
                            .map(|(_, filters)| filters.iter().filter(|f| f.overlaps(matching)).collect::<Vec<_>>())
                            .collect::<Vec<_>>();

                        debug!("Overlapping for {matching:?}: {overlapping:?}");
                        let overlapping_references = overlapping
                            .iter()
                            .map(|f| {
                                let mut v = f.iter().map(|f| matching.intersect(f)).unique().collect::<Vec<_>>();
                                v.sort();
                                v
                            })
                            .unique()
                            .collect::<Vec<_>>();
                        let exclusions = exclusion_filters
                            .iter()
                            .filter(|f| f.overlaps(matching))
                            .map(|f| matching.intersect(f))
                            .unique()
                            .collect::<Vec<_>>();

                        let r = overlapping_references
                            .iter()
                            .flatten()
                            .cloned()
                            .chain(exclusion_filters.iter().cloned())
                            .collect::<Vec<_>>();
                        if let Some(instr) = matching.find_uncovered_instr(r) {
                            trace!(
                                "Found unique instruction for {matching:?}: {instr:?} for {matching:?} - <exclusion filters + seen filters>"
                            );
                            results.insert(instr);
                        } else {
                            if log::log_enabled!(log::Level::Debug) {
                                results.extend(find_intersections((matching, overlapping_references, exclusions)));
                            } else {
                                intersections_to_find.push((matching, overlapping_references, exclusions));
                            }

                            // TODO: Can we do this?
                            exclusion_filters.insert(matching.clone());
                        }
                    }
                }
            }

            if !log::log_enabled!(log::Level::Debug) {
                let num_done = AtomicUsize::new(0);
                let total = intersections_to_find.len();
                results.extend(
                    intersections_to_find
                        .into_par_iter()
                        .with_max_len(1)
                        .map(|item| {
                            let result = find_intersections(item);
                            info!(
                                "Finding intersections: {}/{}",
                                num_done.fetch_add(1, Ordering::Relaxed),
                                total
                            );
                            result
                        })
                        .collect::<Vec<_>>()
                        .into_iter()
                        .flatten(),
                );
            } else {
                assert!(intersections_to_find.is_empty());
            }

            info!("Filtering {} instructions...", results.len());
            let mut results = results.into_iter().collect::<Vec<_>>();

            for instr in results.iter() {
                assert!(
                    !pre_chosen_filters.iter().any(|f| f.matches(instr)),
                    "Added {instr:?} even though it is already matched by a pre-chosen item"
                );
            }

            info!("Sorting {} instructions...", results.len());
            results.sort_by_cached_key(|instr| item_filters.iter().flatten().filter(|f| f.matches(instr)).count());

            results
        };

        // Sanity check on the instructions we found: each filter should be covered by at least one instruction
        for item in items.iter() {
            if item
                .filters()
                .iter()
                .any(|f| f.find_uncovered_instr(pre_chosen_filters.clone()).is_some())
            {
                assert!(
                    covering_instrs
                        .iter()
                        .any(|instr| item.filters().iter().any(|f| f.matches(instr))),
                    "{:?} not covered by any instr; filters: \n{:#?}\npre_chosen:\n{:#?}",
                    item.filters(),
                    items.iter().map(|t| t.filters()).collect::<Vec<_>>(),
                    pre_chosen.iter().map(|t| t.filters()).collect::<Vec<_>>()
                );
            }
        }

        info!(
            "Found {} instructions in {}ms",
            covering_instrs.len(),
            start.elapsed().as_millis()
        );
        trace!("Covering instructions: {covering_instrs:#?}");

        let start = Instant::now();
        let group_maps = {
            info!(
                "Creating coverage maps: {} items * {} instrs",
                items.len(),
                covering_instrs.len()
            );
            let num_instrs_processed = AtomicUsize::new(0);

            // group_maps_t[y][x] = encoding X covers instruction Y.
            let group_maps_t = covering_instrs
                .iter()
                .map(|instr| {
                    let n = num_instrs_processed.fetch_add(1, Ordering::Relaxed);
                    if n % 10_000 == 0 {
                        info!("Processed: {n} / {} instrs in coverage map", covering_instrs.len());
                    }

                    items
                        .iter()
                        .map(|items| items.filters().iter().any(|filter| filter.matches(instr)))
                        .collect::<GrowingBitmap>()
                })
                .collect::<HashSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();

            info!("Transposing coverage map of {} rows...", group_maps_t.len());
            trace!("Transposed coverage map: {group_maps_t:#?}");

            let group_maps = (0..items.len())
                .map(|y| group_maps_t.iter().map(|map| map[y]).collect::<GrowingBitmap>())
                .collect::<Vec<_>>();

            trace!("Normal coverage map: {group_maps:#?}");

            group_maps
        };

        info!("That took {}ms", start.elapsed().as_millis());
        info!("Final covering map: {group_maps:#?}");

        Self {
            items,
            group_maps,
        }
    }

    #[must_use]
    fn find_minimum_covering_group_indexes(&mut self) -> Vec<usize> {
        let num_map_bits = self.group_maps[0].len();
        let num_choices = self.group_maps.len();

        assert!(num_choices <= u16::MAX as usize);

        // A conjunction of disjunctions
        let decisions = {
            let mut v = (0..num_map_bits)
                .map(|index| {
                    self.group_maps
                        .iter()
                        .enumerate()
                        .filter(|(_, m)| m[index])
                        .map(|(index, _)| index)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            v.sort();
            v.dedup();

            v
        };

        info!("Finding MCS of {decisions:?}");

        MinimumCoveringSet::of(decisions, num_choices).into_vec()
    }

    pub fn run(&mut self) -> Vec<T> {
        info!("Running BFS...");

        let mut result = self.find_minimum_covering_group_indexes();
        result.sort();

        result.into_iter().map(|index| self.items[index].clone()).collect()
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::{MinimumCoveringFilterSet, WithFilters};
    use crate::instr::{Instruction, InstructionFilter};

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Filters(Vec<InstructionFilter>);

    impl WithFilters for Filters {
        fn filters(&self) -> &[InstructionFilter] {
            &self.0
        }
    }

    #[test]
    pub fn return_correct_items_with_prechosen_filters() {
        let filters = vec![
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 1___0000 11110010 00___100 ____0__0"),
                InstructionFilter::parse("11000100 ___00010 1___0000 11110010 00___100 ___0___0"),
                InstructionFilter::parse("11000100 ___00010 1___0000 11110010 00___100 __1____0"),
                InstructionFilter::parse("11000100 _0_00010 1___0000 11110010 00___100 _______0"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ____0__0"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ____00__"),
                InstructionFilter::parse("11000100 __100010 1____000 11110010 00___100 ____0_1_"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ___0___0"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ___0_0__"),
                InstructionFilter::parse("11000100 __100010 1____000 11110010 00___100 ___0__1_"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 __0____0"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 __0__0__"),
                InstructionFilter::parse("11000100 __100010 1____000 11110010 00___100 __0___1_"),
                InstructionFilter::parse("11000100 _1_00010 1____000 11110010 00___100 _______0"),
                InstructionFilter::parse("11000100 _1_00010 1____000 11110010 00___100 _____0__"),
                InstructionFilter::parse("11000100 _1100010 1____000 11110010 00___100 ______1_"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ____0__0"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ____00__"),
                InstructionFilter::parse("11000100 __100010 1____000 11110010 00___100 ____0_1_"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ___0___0"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 ___0_0__"),
                InstructionFilter::parse("11000100 __100010 1____000 11110010 00___100 ___0__1_"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 __0____0"),
                InstructionFilter::parse("11000100 ___00010 1____000 11110010 00___100 __0__0__"),
                InstructionFilter::parse("11000100 __100010 1____000 11110010 00___100 __0___1_"),
                InstructionFilter::parse("11000100 _1_00010 1____000 11110010 00___100 _______0"),
                InstructionFilter::parse("11000100 _1_00010 1____000 11110010 00___100 _____0__"),
                InstructionFilter::parse("11000100 _1100010 1____000 11110010 00___100 ______1_"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 1___0000 11110010 00___100 ____0__0"),
                InstructionFilter::parse("11000100 ___00010 1___0000 11110010 00___100 ___0___0"),
                InstructionFilter::parse("11000100 ___00010 1___0000 11110010 00___100 __1____0"),
                InstructionFilter::parse("11000100 _0_00010 1___0000 11110010 00___100 _______0"),
            ]),
            Filters(vec![InstructionFilter::parse(
                "11000100 ___00010 1____000 11110010 00___100 ______1_",
            )]),
            Filters(vec![InstructionFilter::parse(
                "11000100 ___00010 1____000 11110010 00___100 ______1_",
            )]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 1__01000 11110010 00___100 ____1_00"),
                InstructionFilter::parse("11000100 ___00010 1__01000 11110010 00___100 ____11_0"),
                InstructionFilter::parse("11000100 __000010 1__01000 11110010 00___100 ____1__0"),
                InstructionFilter::parse("11000100 ___00010 1_1_1000 11110010 00___100 ____1_00"),
                InstructionFilter::parse("11000100 ___00010 1_1_1000 11110010 00___100 ____11_0"),
                InstructionFilter::parse("11000100 __000010 1_1_1000 11110010 00___100 ____1__0"),
                InstructionFilter::parse("11000100 ___00010 11__1000 11110010 00___100 ____1_00"),
                InstructionFilter::parse("11000100 ___00010 11__1000 11110010 00___100 ____11_0"),
                InstructionFilter::parse("11000100 __000010 11__1000 11110010 00___100 ____1__0"),
            ]),
            Filters(vec![InstructionFilter::parse(
                "11000100 ___00010 1__01000 11110010 00___100 ____1_00",
            )]),
            Filters(vec![
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 ____1__0"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 ____1_1_"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 ____10__"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 ___0___0"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 ___0__1_"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 ___0_0__"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 __1____0"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 __1___1_"),
                InstructionFilter::parse("11000100 __100010 10___000 11110010 00___100 __1__0__"),
                InstructionFilter::parse("11000100 _1100010 10___000 11110010 00___100 _______0"),
                InstructionFilter::parse("11000100 _1100010 10___000 11110010 00___100 ______1_"),
                InstructionFilter::parse("11000100 _1100010 10___000 11110010 00___100 _____0__"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 __100010 10__1000 11110010 00___100 ____1__0"),
                InstructionFilter::parse("11000100 __100010 10__1000 11110010 00___100 ___1___0"),
                InstructionFilter::parse("11000100 __100010 10__1000 11110010 00___100 __0____0"),
                InstructionFilter::parse("11000100 _1100010 10__1000 11110010 00___100 _______0"),
                InstructionFilter::parse("11000100 __100010 10_1_000 11110010 00___100 ____1__0"),
                InstructionFilter::parse("11000100 __100010 10_1_000 11110010 00___100 ___1___0"),
                InstructionFilter::parse("11000100 __100010 10_1_000 11110010 00___100 __0____0"),
                InstructionFilter::parse("11000100 _1100010 10_1_000 11110010 00___100 _______0"),
                InstructionFilter::parse("11000100 __100010 101__000 11110010 00___100 ____1__0"),
                InstructionFilter::parse("11000100 __100010 101__000 11110010 00___100 ___1___0"),
                InstructionFilter::parse("11000100 __100010 101__000 11110010 00___100 __0____0"),
                InstructionFilter::parse("11000100 _1100010 101__000 11110010 00___100 _______0"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 _1_00010 10___000 11110010 00___100 _______0"),
                InstructionFilter::parse("11000100 _1_00010 10___000 11110010 00___100 _____0__"),
                InstructionFilter::parse("11000100 _1100010 10___000 11110010 00___100 ______1_"),
            ]),
        ];

        let result = MinimumCoveringFilterSet::new(
            filters,
            &[
                Filters(vec![InstructionFilter::parse(
                    "11000100 ___00010 1____000 11110010 00___100 _______0",
                )]),
                Filters(vec![InstructionFilter::parse(
                    "11000100 ___00010 1____000 11110010 00___100 _____0__",
                )]),
            ],
        )
        .run();

        assert!(result.iter().any(|f| {
            f.0.iter()
                .any(|f| f.matches(&Instruction::new(&[0xC4, 0xA2, 0xB0, 0xF2, 0x14, 0xFF])))
        }));
    }

    #[test]
    pub fn choose_minimal_items() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0000____")]),
            Filters(vec![InstructionFilter::parse("00_0____")]),
        ];

        let result = MinimumCoveringFilterSet::new(filters, &[]).run();

        assert_eq!(result, vec![Filters(vec![InstructionFilter::parse("00_0____")])]);
    }

    #[test]
    pub fn prefer_explicit_enumeration_over_wildcards() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0000____")]),
            Filters(vec![InstructionFilter::parse("0001____")]),
            Filters(vec![InstructionFilter::parse("0010____")]),
            Filters(vec![InstructionFilter::parse("0011____")]),
            Filters(vec![InstructionFilter::parse("0100____")]),
            Filters(vec![InstructionFilter::parse("0101____")]),
            Filters(vec![InstructionFilter::parse("0110____")]),
            Filters(vec![InstructionFilter::parse("0111____")]),
            Filters(vec![InstructionFilter::parse("000_____")]),
            Filters(vec![InstructionFilter::parse("000____0")]),
            Filters(vec![InstructionFilter::parse("000____1")]),
            Filters(vec![InstructionFilter::parse("0____000")]),
        ];

        let result = MinimumCoveringFilterSet::new(filters, &[]).run();

        assert_eq!(
            result,
            vec![
                Filters(vec![InstructionFilter::parse("0010____")]),
                Filters(vec![InstructionFilter::parse("0011____")]),
                Filters(vec![InstructionFilter::parse("0100____")]),
                Filters(vec![InstructionFilter::parse("0101____")]),
                Filters(vec![InstructionFilter::parse("0110____")]),
                Filters(vec![InstructionFilter::parse("0111____")]),
                Filters(vec![InstructionFilter::parse("000_____")]),
            ]
        );
    }

    #[test]
    pub fn leave_out_unneeded1() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0111011_ ____0010")]),
            Filters(vec![InstructionFilter::parse("01110110 0_______")]),
            Filters(vec![InstructionFilter::parse("01110110 1_______")]),
            Filters(vec![InstructionFilter::parse("01110111 ________")]),
        ];

        let result = MinimumCoveringFilterSet::new(filters, &[]).run();

        assert_eq!(
            result,
            vec![
                Filters(vec![InstructionFilter::parse("01110110 0_______")]),
                Filters(vec![InstructionFilter::parse("01110110 1_______")]),
                Filters(vec![InstructionFilter::parse("01110111 ________")]),
            ]
        );
    }

    #[test]
    pub fn leave_out_unneeded2() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0111111_ ________")]),
            Filters(vec![InstructionFilter::parse("0111____ 00000000")]), // <== This one is not needed
            Filters(vec![InstructionFilter::parse("0111000_ ________")]),
            Filters(vec![InstructionFilter::parse("0111001_ ________")]),
            Filters(vec![InstructionFilter::parse("0111010_ ________")]),
            Filters(vec![InstructionFilter::parse("01110110 0_______")]),
            Filters(vec![InstructionFilter::parse("0111011_ ____0010")]), // <== This one here is also not needed
            Filters(vec![InstructionFilter::parse("01110110 1_______")]),
            Filters(vec![InstructionFilter::parse("01110111 ________")]),
            Filters(vec![InstructionFilter::parse("0111100_ ________")]),
            Filters(vec![InstructionFilter::parse("0111101_ ________")]),
            Filters(vec![InstructionFilter::parse("0111110_ ________")]),
        ];

        let result = MinimumCoveringFilterSet::new(filters, &[]).run();

        assert_eq!(
            result,
            vec![
                Filters(vec![InstructionFilter::parse("0111111_ ________")]),
                Filters(vec![InstructionFilter::parse("0111000_ ________")]),
                Filters(vec![InstructionFilter::parse("0111001_ ________")]),
                Filters(vec![InstructionFilter::parse("0111010_ ________")]),
                Filters(vec![InstructionFilter::parse("01110110 0_______")]),
                Filters(vec![InstructionFilter::parse("01110110 1_______")]),
                Filters(vec![InstructionFilter::parse("01110111 ________")]),
                Filters(vec![InstructionFilter::parse("0111100_ ________")]),
                Filters(vec![InstructionFilter::parse("0111101_ ________")]),
                Filters(vec![InstructionFilter::parse("0111110_ ________")]),
            ]
        );
    }

    #[test]
    pub fn consider_complex_combinations() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0000____")]),
            Filters(vec![InstructionFilter::parse("0011____")]),
            Filters(vec![InstructionFilter::parse("1100____")]),
            Filters(vec![InstructionFilter::parse("__110___")]),
            Filters(vec![InstructionFilter::parse("110_____")]),
        ];

        let result = MinimumCoveringFilterSet::new(filters, &[]).run();

        assert_eq!(
            result,
            vec![
                Filters(vec![InstructionFilter::parse("0000____")]),
                Filters(vec![InstructionFilter::parse("0011____")]),
                Filters(vec![InstructionFilter::parse("__110___")]),
                Filters(vec![InstructionFilter::parse("110_____")]),
            ]
        );
    }

    #[test]
    pub fn mutex_filter_memory_usage() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 1_______ ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 0011_101 ________ ________ ________ ________ 00000000",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 001_____ ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 01______ ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ ________ 0_______",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ _______1 ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ ______10 ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ _____100 ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ ____1___ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ ___1____ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ __1_____ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ _1______ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ________ 1_______ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ _______1 ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ______1_ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ _____1__ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ____1___ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ ___1____ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ __1_____ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ _1______ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ________ 1_______ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ _______1 ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ______1_ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ _____1__ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ____1___ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ ___1____ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ __1_____ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ _1______ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ________ 1_______ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 _______1 ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ______1_ ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 _____1__ ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ____1___ ________ ________ ________ ________",
            )]),
            Filters(vec![InstructionFilter::parse(
                "10000011 00110101 ___1____ ________ ________ ________ ________",
            )]),
        ];

        let result = MinimumCoveringFilterSet::new(filters, &[]).run();

        assert_eq!(
            result,
            vec![
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 1_______ ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 0011_101 ________ ________ ________ ________ 00000000"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 001_____ ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 01______ ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ ________ 0_______"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ _______1 ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ ______10 ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ _____100 ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ ____1___ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ ___1____ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ __1_____ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ _1______ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ________ 1_______ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ _______1 ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ______1_ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ _____1__ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ____1___ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ ___1____ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ __1_____ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ _1______ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ________ 1_______ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ _______1 ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ______1_ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ _____1__ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ____1___ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ ___1____ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ __1_____ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ _1______ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ________ 1_______ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 _______1 ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ______1_ ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 _____1__ ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ____1___ ________ ________ ________ ________"
                )]),
                Filters(vec![InstructionFilter::parse(
                    "10000011 00110101 ___1____ ________ ________ ________ ________"
                )]),
            ]
        );
    }

    fn assert_covering_set_selected(filters: &[Filters], pre_chosen: &[Filters]) -> Vec<Filters> {
        let result = MinimumCoveringFilterSet::new(filters.to_vec(), pre_chosen).run();

        println!("Picked: {result:?}");

        for filter in filters.iter().flat_map(|f| f.0.iter()) {
            assert!(
                result
                    .iter()
                    .any(|f| f.0.iter().any(|f| f.matches(&filter.smallest_matching_instruction())))
            );
            assert!(
                result
                    .iter()
                    .any(|f| f.0.iter().any(|f| f.matches(&filter.largest_matching_instruction()))),
                "Filters do not match: {:?}",
                filter.largest_matching_instruction()
            );
        }

        result
    }

    #[test]
    fn select_covering_set1() {
        let filters = vec![
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0___1001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0__1_001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0_0__001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 00___001 11110111 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 0___0001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0___0001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0___0001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 0___0001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0__0_001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0__0_001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0__0_001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 0__0_001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 0_0__001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 00___001 11110111 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0___1001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0__1_001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0_0__001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 00___001 11110111 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0___1001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0__1_001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 0_0__001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11___0__"),
                InstructionFilter::parse("11000100 __100010 00___001 11110111 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __100010 0___1001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __100010 0__1_001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 0_0__001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __100010 0_0__001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11_____1"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11____1_"),
                InstructionFilter::parse("11000100 ___00010 00___001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __100010 00___001 11110111 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0___1001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 0___1001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0__1_001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 0__1_001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 0_1__001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 0_1__001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 0_1__001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 0_1__001 11110111 11______"),
                InstructionFilter::parse("11000100 ___00010 01___001 11110111 11_____0"),
                InstructionFilter::parse("11000100 ___00010 01___001 11110111 11____0_"),
                InstructionFilter::parse("11000100 ___00010 01___001 11110111 11___1__"),
                InstructionFilter::parse("11000100 __000010 01___001 11110111 11______"),
            ]),
        ];

        let result = assert_covering_set_selected(&filters, &[]);
        assert!(result.iter().any(|f| {
            f.0.iter()
                .any(|f| f.matches(&Instruction::new(&[0xC4, 0x02, 0x01, 0xF7, 0xFF])))
        }));
    }

    #[test]
    fn select_covering_set2() {
        let filters = vec![
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 1___0101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1__0_101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 1__0_101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1__0_101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 1__0_101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1_0__101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 1_0__101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1_0__101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 1_0__101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 11___101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 11___101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 11___101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 11___101 11001111 11______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 1___0101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1__1_101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 1__1_101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1__1_101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 1__1_101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1_0__101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 1_0__101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1_0__101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 1_0__101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 10___101 11001111 11______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 1___1101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 1___1101 11001111 11____1_ ________"),
                InstructionFilter::parse("11000100 ___00011 1___1101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 1___1101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1__1_101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 1__1_101 11001111 11____1_ ________"),
                InstructionFilter::parse("11000100 ___00011 1__1_101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 1__1_101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1_1__101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 1_1__101 11001111 11____1_ ________"),
                InstructionFilter::parse("11000100 ___00011 1_1__101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 1_1__101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11_____1 ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11____1_ ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __000011 10___101 11001111 11______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1___0101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 1___0101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1__0_101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 1__0_101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1__0_101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 1__0_101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 1_1__101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 1_1__101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 1_1__101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 1_1__101 11001111 11______ ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11_____0 ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11____0_ ________"),
                InstructionFilter::parse("11000100 ___00011 10___101 11001111 11___0__ ________"),
                InstructionFilter::parse("11000100 __100011 10___101 11001111 11______ ________"),
            ]),
        ];

        assert_covering_set_selected(&filters, &[]);
    }

    #[test]
    fn select_covering_set3() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0100_0_0 001000_0 11000000")]),
            Filters(vec![InstructionFilter::parse("0100____ 00100000 11______")]),
            Filters(vec![InstructionFilter::parse("0100____ 00100010 11______")]),
        ];

        assert_covering_set_selected(&filters, &[]);
    }

    #[test]
    fn select_covering_set4() {
        let filters = vec![
            Filters(vec![
                InstructionFilter::parse("___00011 1___0101 11_____0"),
                InstructionFilter::parse("___00011 1___0101 11____0_"),
                InstructionFilter::parse("___00011 1___0101 11___0__"),
                InstructionFilter::parse("__000011 1___0101 11______"),
                InstructionFilter::parse("___00011 1__0_101 11_____0"),
                InstructionFilter::parse("___00011 1__0_101 11____0_"),
                InstructionFilter::parse("___00011 1__0_101 11___0__"),
                InstructionFilter::parse("__000011 1__0_101 11______"),
                InstructionFilter::parse("___00011 1_0__101 11_____0"),
                InstructionFilter::parse("___00011 1_0__101 11____0_"),
                InstructionFilter::parse("___00011 1_0__101 11___0__"),
                InstructionFilter::parse("__000011 1_0__101 11______"),
                InstructionFilter::parse("___00011 11___101 11_____0"),
                InstructionFilter::parse("___00011 11___101 11____0_"),
                InstructionFilter::parse("___00011 11___101 11___0__"),
                InstructionFilter::parse("__000011 11___101 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("___00011 1___0101 11_____1"),
                InstructionFilter::parse("___00011 1___0101 11____0_"),
                InstructionFilter::parse("___00011 1___0101 11___0__"),
                InstructionFilter::parse("__100011 1___0101 11______"),
                InstructionFilter::parse("___00011 1__1_101 11_____1"),
                InstructionFilter::parse("___00011 1__1_101 11____0_"),
                InstructionFilter::parse("___00011 1__1_101 11___0__"),
                InstructionFilter::parse("__100011 1__1_101 11______"),
                InstructionFilter::parse("___00011 1_0__101 11_____1"),
                InstructionFilter::parse("___00011 1_0__101 11____0_"),
                InstructionFilter::parse("___00011 1_0__101 11___0__"),
                InstructionFilter::parse("__100011 1_0__101 11______"),
                InstructionFilter::parse("___00011 10___101 11_____1"),
                InstructionFilter::parse("___00011 10___101 11____0_"),
                InstructionFilter::parse("___00011 10___101 11___0__"),
                InstructionFilter::parse("__100011 10___101 11______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("___00011 1___0101 11_____0"),
                InstructionFilter::parse("___00011 1__0_101 11_____0"),
                InstructionFilter::parse("___00011 1__0_101 11____0_"),
                InstructionFilter::parse("___00011 1__0_101 11___0__"),
                InstructionFilter::parse("__100011 1__0_101 11______"),
                InstructionFilter::parse("___00011 1_1__101 11_____0"),
                InstructionFilter::parse("___00011 1_1__101 11____0_"),
                InstructionFilter::parse("___00011 1_1__101 11___0__"),
                InstructionFilter::parse("__100011 1_1__101 11______"),
                InstructionFilter::parse("___00011 10___101 11_____0"),
            ]),
            Filters(vec![
                InstructionFilter::parse("___00011 1___1101 11_____1"),
                InstructionFilter::parse("___00011 1___1101 11____1_"),
                InstructionFilter::parse("___00011 1___1101 11___0__"),
                InstructionFilter::parse("__000011 1___1101 11______"),
                InstructionFilter::parse("___00011 1__1_101 11_____1"),
                InstructionFilter::parse("___00011 1__1_101 11____1_"),
                InstructionFilter::parse("___00011 1__1_101 11___0__"),
                InstructionFilter::parse("__000011 1__1_101 11______"),
                InstructionFilter::parse("___00011 1_1__101 11_____1"),
                InstructionFilter::parse("___00011 1_1__101 11____1_"),
                InstructionFilter::parse("__000011 1_1__101 11______"),
            ]),
        ];

        let result = assert_covering_set_selected(&filters, &[]);
        assert!(
            result
                .iter()
                .any(|f| f.0.iter().any(|f| f.matches(&Instruction::new(&[0xe3, 0xed, 0xf7]))))
        );
    }

    #[test]
    fn select_covering_set5a() {
        let filters = vec![
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ 0_______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ 0_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0_1__101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ _1______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ 1_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ _0______"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ _0______"),
                InstructionFilter::parse("11000100 ___00011 0__0_101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ _0______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00___0__ _0______"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00___0__ 1_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ _1______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00___0__ 1_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 0___0101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 00___101 01001011 00____1_ 0_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 0___1101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 0__1_101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 0_0__101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ _0______"),
                InstructionFilter::parse("11000100 ___00011 01___101 01001011 00____1_ 1_______"),
            ]),
        ];

        let result = assert_covering_set_selected(&filters, &[]);
        assert!(result.iter().any(|f| {
            f.0.iter()
                .any(|f| f.matches(&Instruction::new(&[0xc4, 0x83, 0x15, 0x4b, 0x26, 0x21])))
        }));
    }

    #[test]
    fn select_covering_set5b() {
        let filters = vec![
            Filters(vec![
                InstructionFilter::parse("0___1101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("0___1101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0___1101 01001011 00____1_ _1______"),
                InstructionFilter::parse("0___1101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("0___1101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("0___1101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0___1101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0___1101 01001011 00___0__ 0_______"),
                InstructionFilter::parse("0__0_101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("0__0_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0__0_101 01001011 00____1_ _1______"),
                InstructionFilter::parse("0__0_101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ 0_______"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ _1______"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ 0_______"),
                InstructionFilter::parse("01___101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("01___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("01___101 01001011 00____1_ _1______"),
                InstructionFilter::parse("01___101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("01___101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("01___101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("01___101 01001011 00___0__ _1______"),
                InstructionFilter::parse("01___101 01001011 00___0__ 0_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0___0101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("0___0101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0___0101 01001011 00____1_ _1______"),
                InstructionFilter::parse("0___0101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("0___0101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("0___0101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0___0101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0___0101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ _1______"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ _1______"),
                InstructionFilter::parse("0_1__101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0_1__101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("01___101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("01___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("01___101 01001011 00____1_ _1______"),
                InstructionFilter::parse("01___101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("01___101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("01___101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("01___101 01001011 00___0__ _1______"),
                InstructionFilter::parse("01___101 01001011 00___0__ 1_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0___0101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("0___0101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0___0101 01001011 00___0__ _0______"),
                InstructionFilter::parse("0___0101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ _0______"),
                InstructionFilter::parse("0__0_101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ _0______"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("00___101 01001011 00___0__ ___0____"),
                InstructionFilter::parse("00___101 01001011 00___0__ __0_____"),
                InstructionFilter::parse("00___101 01001011 00___0__ _0______"),
                InstructionFilter::parse("00___101 01001011 00___0__ 1_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0___1101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("0___1101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("0___1101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0___1101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0__1_101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ _1______"),
                InstructionFilter::parse("0_0__101 01001011 00___0__ 1_______"),
                InstructionFilter::parse("01___101 01001011 00___0__ ___1____"),
                InstructionFilter::parse("01___101 01001011 00___0__ __1_____"),
                InstructionFilter::parse("01___101 01001011 00___0__ _1______"),
                InstructionFilter::parse("01___101 01001011 00___0__ 1_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0___0101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("0___0101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0___0101 01001011 00____1_ _0______"),
                InstructionFilter::parse("0___0101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ _0______"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ _0______"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ 0_______"),
                InstructionFilter::parse("00___101 01001011 00____1_ ___1____"),
                InstructionFilter::parse("00___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("00___101 01001011 00____1_ _0______"),
                InstructionFilter::parse("00___101 01001011 00____1_ 0_______"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0___1101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("0___1101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0___1101 01001011 00____1_ _0______"),
                InstructionFilter::parse("0___1101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ _0______"),
                InstructionFilter::parse("0__1_101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ _0______"),
                InstructionFilter::parse("0_0__101 01001011 00____1_ 1_______"),
                InstructionFilter::parse("01___101 01001011 00____1_ ___0____"),
                InstructionFilter::parse("01___101 01001011 00____1_ __0_____"),
                InstructionFilter::parse("01___101 01001011 00____1_ _0______"),
                InstructionFilter::parse("01___101 01001011 00____1_ 1_______"),
            ]),
        ];

        let result = assert_covering_set_selected(&filters, &[]);
        assert!(
            result
                .iter()
                .any(|f| f.0.iter().any(|f| f.matches(&Instruction::new(&[0x15, 0x4b, 0x26, 0x21]))))
        );
    }

    #[test]
    fn select_covering_set6() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("00001111 010101_0 11000000")]),
            Filters(vec![InstructionFilter::parse("00001111 01010100 11______")]),
            Filters(vec![InstructionFilter::parse("00001111 01010100 11______")]),
            Filters(vec![InstructionFilter::parse("00001111 01010100 11______")]),
            Filters(vec![InstructionFilter::parse("00001111 01010100 11__0__1")]),
            Filters(vec![InstructionFilter::parse("00001111 01010100 11__1__0")]),
            Filters(vec![InstructionFilter::parse("00001111 01010110 11______")]),
            Filters(vec![InstructionFilter::parse("00001111 01010110 11______")]),
            Filters(vec![InstructionFilter::parse("00001111 01010110 11______")]),
            Filters(vec![InstructionFilter::parse("00001111 01010110 11__0__1")]),
            Filters(vec![InstructionFilter::parse("00001111 01010110 11__1__0")]),
        ];

        assert_covering_set_selected(&filters, &[]);
    }

    #[test]
    fn select_covering_set7() {
        let filters = vec![
            Filters(vec![InstructionFilter::parse("0100__00 11011001 01110100 __000000 ________")]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 00__0__1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00__0_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00__01__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 00__0___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_0___1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_0_1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 00_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 000____1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 000___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 000__1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 000_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 00_____1 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 00____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 00___1__ ________"),
                InstructionFilter::parse("0100__10 11011001 01110100 00______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 01__0__1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01__0_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01__01__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 01__0___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_0___1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_0_1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 01_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 010____1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 010___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 010__1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 010_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 01_____1 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 01____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 01___1__ ________"),
                InstructionFilter::parse("0100__10 11011001 01110100 01______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 10__0__1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10__0_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10__01__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 10__0___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_0___1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_0_1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 10_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 100____1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 100___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 100__1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 100_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 10_____1 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 10____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 10___1__ ________"),
                InstructionFilter::parse("0100__10 11011001 01110100 10______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 11__0__1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11__0_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11__01__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 11__0___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_0___1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_0_1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 11_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 110____1 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 110___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 110__1__ ________"),
                InstructionFilter::parse("0100___0 11011001 01110100 110_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 11_____1 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 11____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 11___1__ ________"),
                InstructionFilter::parse("0100__10 11011001 01110100 11______ ________"),
            ]),
        ];

        let pre_chosen = vec![
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 11__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11__10__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 11__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_1___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_1__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_1_0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 11_1____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 111____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 111___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 111__0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 111_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 11_____0 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 11____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 11___0__ ________"),
                InstructionFilter::parse("0100__11 11011001 01110100 11______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 11__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11__11__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 11__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_0___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 11_0_1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 11_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 111____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 111___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 111__1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 111_____ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 11_____0 ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 11____0_ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 11___1__ ________"),
                InstructionFilter::parse("0100__01 11011001 01110100 11______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 10__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10__10__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 10__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_1___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_1__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_1_0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 10_1____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 101____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 101___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 101__0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 101_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 10_____0 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 10____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 10___0__ ________"),
                InstructionFilter::parse("0100__11 11011001 01110100 10______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 10__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10__11__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 10__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_0___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 10_0_1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 10_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 101____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 101___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 101__1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 101_____ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 10_____0 ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 10____0_ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 10___1__ ________"),
                InstructionFilter::parse("0100__01 11011001 01110100 10______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 01__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01__10__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 01__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_1___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_1__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_1_0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 01_1____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 011____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 011___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 011__0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 011_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 01_____0 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 01____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 01___0__ ________"),
                InstructionFilter::parse("0100__11 11011001 01110100 01______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 01__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01__11__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 01__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_0___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 01_0_1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 01_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 011____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 011___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 011__1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 011_____ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 01_____0 ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 01____0_ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 01___1__ ________"),
                InstructionFilter::parse("0100__01 11011001 01110100 01______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 00__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00__10__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 00__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_1___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_1__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_1_0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 00_1____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 001____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 001___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 001__0__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 001_____ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 00_____0 ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 00____0_ ________"),
                InstructionFilter::parse("0100__1_ 11011001 01110100 00___0__ ________"),
                InstructionFilter::parse("0100__11 11011001 01110100 00______ ________"),
            ]),
            Filters(vec![
                InstructionFilter::parse("0100____ 11011001 01110100 00__1__0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00__1_0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00__11__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 00__1___ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_0___0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_0__0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 00_0_1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 00_0____ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 001____0 ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 001___0_ ________"),
                InstructionFilter::parse("0100____ 11011001 01110100 001__1__ ________"),
                InstructionFilter::parse("0100___1 11011001 01110100 001_____ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 00_____0 ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 00____0_ ________"),
                InstructionFilter::parse("0100__0_ 11011001 01110100 00___1__ ________"),
                InstructionFilter::parse("0100__01 11011001 01110100 00______ ________"),
            ]),
        ];

        assert_covering_set_selected(&filters, &pre_chosen);
    }

    fn filters_from_str(s: &str) -> Vec<Filters> {
        let mut filters = Vec::new();
        let mut set = Vec::new();
        for f in s.split('\n') {
            let f = f.trim();
            if f.is_empty() {
                if !set.is_empty() {
                    filters.push(Filters(set.clone()));
                    set = Vec::new();
                }
            } else {
                set.push(InstructionFilter::parse(f));
            }
        }

        if !set.is_empty() {
            filters.push(Filters(set));
        }

        filters
    }

    #[test]
    fn select_covering_set8() {
        let filters = filters_from_str(include_str!("select_covering_set8.txt"));
        assert_covering_set_selected(&filters, &[]);
    }
}
