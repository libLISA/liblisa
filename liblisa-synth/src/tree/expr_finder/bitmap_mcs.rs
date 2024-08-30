use std::collections::HashMap;
use std::time::Instant;

use liblisa::semantics::default::builder::hole;
use liblisa::semantics::default::computation::{ExpressionComputation, OutputEncoding};
use liblisa::semantics::default::expr;
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::utils::bitmap::{BitmapSlice, GrowingBitmap};
use liblisa::utils::{bitmask_u128, bitmask_u64, MinimumCoveringSet, Timeout};
use liblisa::value::{AsValue, OwnedValue, Value, ValueArrayEquality};
use log::{debug, info, warn};

use super::ExpressionFinder;
use crate::search::{CompressedIterComputation, ComputationEnumerator};
use crate::templates::EXPR_TEMPLATES;
use crate::tree::PreparedCase;
use crate::InputSlice;

#[derive(Clone)]
struct Grouping {
    map: GrowingBitmap,
    current: Option<CompressedIterComputation>,
    position: usize,
    negative: Vec<usize>,
    step: usize,
}

#[derive(Clone)]
struct Matches {
    bitmap: GrowingBitmap,

    /// ones_minimap[N] = true if for any M in N..N+64 bitmap[M] = true
    ones_minimap: GrowingBitmap,
}

impl Matches {
    pub fn new(bitmap: GrowingBitmap) -> Self {
        let ones_minimap = bitmap.data().iter().map(|&x| x != 0).collect::<GrowingBitmap>();

        Self {
            ones_minimap,
            bitmap,
        }
    }
}

impl Grouping {
    fn to_template_computation(&self, enumerator: &ComputationEnumerator) -> ExpressionComputation {
        self.current.unwrap().decompress(enumerator).to_template_computation()
    }
}

#[derive(Clone)]
pub struct Case {
    case: PreparedCase,
    inputs: Vec<OwnedValue>,
    matches: Matches,
}

fn find_position_matching_bitmaps(start_position: usize, rows: &[&GrowingBitmap]) -> Option<usize> {
    let mut index = start_position;

    'outer: loop {
        for row in rows.iter() {
            let old_index = index;
            index = row.first_bit_set_from(index)?;

            if old_index != index {
                continue 'outer
            }
        }

        assert!(rows.iter().all(|row| row[index]));

        return Some(index)
    }
}

fn find_position_matching(start_position: usize, expected: &[(&Matches, bool)]) -> Option<usize> {
    if expected.len() == 1 {
        if expected[0].1 {
            expected[0].0.bitmap.first_bit_set_from(start_position)
        } else {
            expected[0].0.bitmap.first_bit_unset_from(start_position)
        }
    } else {
        let ones = expected
            .iter()
            .filter(|&&(_, expected)| expected)
            .map(|(row, _)| &row.ones_minimap)
            .collect::<Vec<_>>();

        let offset_end = expected.iter().map(|(row, _)| row.bitmap.data().len()).min().unwrap();

        let mut offset = start_position / 64;

        if offset >= offset_end {
            return None
        }

        if start_position % 64 != 0 && ones.iter().all(|v| v[offset]) {
            let data = expected
                .iter()
                .map(|&(row, expected)| {
                    if expected {
                        row.bitmap.data()[offset]
                    } else {
                        !row.bitmap.data()[offset]
                    }
                })
                .reduce(|a, b| a & b)
                .unwrap();
            let data = data & !bitmask_u64((start_position % 64) as u32);

            if data != 0 {
                return Some(offset * 64 + data.trailing_zeros() as usize)
            }

            offset += 1;
        }

        while offset < offset_end {
            let new_offset = find_position_matching_bitmaps(offset, &ones)?;
            if new_offset >= offset_end {
                return None
            }

            let data = expected
                .iter()
                .map(|&(row, expected)| {
                    if expected {
                        row.bitmap.data()[new_offset]
                    } else {
                        !row.bitmap.data()[new_offset]
                    }
                })
                .reduce(|a, b| a & b)
                .unwrap();

            if data != 0 {
                return Some(new_offset * 64 + data.trailing_zeros() as usize)
            }

            offset = new_offset + 1;
        }

        None
    }
}

#[derive(Clone)]
pub struct BitmapMcsExpressionFinder {
    cases: Vec<Case>,
    groups: Vec<Grouping>,
    pending_groups: Vec<Grouping>,
    enumerator: ComputationEnumerator<'static>,
    timeout: Timeout,
    failed: bool,
    step_threshold: usize,
    threshold_size: usize,
    output_bits: usize,
    use_endianness: bool,
    output_type: IoType,
    last_processed_case: usize,
}

impl ExpressionFinder for BitmapMcsExpressionFinder {
    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        let enumerator = ComputationEnumerator::new(&EXPR_TEMPLATES, input_types, output_type);
        Self {
            cases: Vec::new(),
            groups: vec![Grouping {
                map: GrowingBitmap::new(),
                current: None,
                negative: Vec::new(),
                position: 0,
                step: 0,
            }],
            pending_groups: Vec::new(),
            enumerator,
            timeout: Timeout::default(),
            failed: false,
            step_threshold: 0,
            threshold_size: 0,
            output_bits: output_type.num_bits(),
            use_endianness: output_type.num_bits() > 8,
            output_type,
            last_processed_case: 0,
        }
    }

    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: Value) {
        if self.timeout.is_timed_out() || self.failed {
            return
        }

        let new_index = self.cases.len();
        info!("Adding {inputs:X?} -> {output:X?} as index={new_index}");

        let case = PreparedCase::new(inputs, output, &self.enumerator);

        if let Some(existing) = self.cases.iter().find(|existing| existing.inputs.value_eq(inputs)) {
            if case.comparison != existing.case.comparison {
                warn!("Invalid encoding: two different outputs seen for {inputs:X?}");
                self.failed = true;
                return
            } else {
                panic!(
                    "Case already added: {inputs:X?} -> {output:X?} vs. {:X?} -> {:X?}",
                    existing.inputs, existing.case.comparison
                );
            }
        }

        self.cases.push(Case {
            case,
            inputs: inputs.as_owned(),
            matches: Matches::new(GrowingBitmap::new()),
        });
    }

    fn find_expressions(&mut self) -> Vec<ExpressionComputation> {
        if self.failed {
            return Vec::new()
        }

        let identities = self
            .cases
            .iter()
            .map(|case| {
                case.case
                    .arg_slice()
                    .iter()
                    .map(|&arg| arg & bitmask_u128(self.output_bits as u32) as i128 == case.case.comparison.big_endian)
                    .collect::<GrowingBitmap>()
            })
            .collect::<Vec<_>>();

        info!("Identities: {identities:#?}");
        if identities.iter().all(|id| !id.is_all_zeros()) {
            info!("We could cover output with identities only!");
            let decisions = identities
                .iter()
                .map(|m| m.iter_one_indices().collect::<Vec<_>>())
                .collect::<Vec<_>>();
            let num_choices = decisions.iter().map(|v| v.iter().copied().max().unwrap()).max().unwrap() + 1;

            let mcs = MinimumCoveringSet::of(decisions, num_choices);
            let mcs = mcs.into_vec();

            info!("Need identities: {mcs:?}");

            let template = expr!(hole::<0>());
            return mcs
                .into_iter()
                .map(|index| {
                    ExpressionComputation::new(
                        template.to_owned(),
                        [self.enumerator.args()[index]].into_iter().collect(),
                        OutputEncoding::UnsignedBigEndian,
                        self.output_type,
                    )
                })
                .collect()
        }

        while self.last_processed_case < self.cases.len() {
            let case = &self.cases[self.last_processed_case];
            info!("Processing case {}: {:X?}", self.last_processed_case, case.case);
            let matches = {
                let mut result = GrowingBitmap::new();
                let mut index = 0;
                let mut enumerator = self.enumerator.clone();

                while let Some(expr) = enumerator.find_next() {
                    let compare = expr.prepared_compare_eq_with_args_indirect(case.case.args.as_slice(), &case.case.comparison);

                    if compare.big_endian {
                        result.set(index);
                    }
                    index += 1;

                    if self.use_endianness {
                        if compare.little_endian {
                            result.set(index);
                        }
                        index += 1;
                    }
                }

                result
            };

            info!(
                "Total expressions: {}, of which {} match true ({}%)",
                matches.len(),
                matches.count_ones(),
                (matches.count_ones() * 100).checked_div(matches.len()).unwrap_or(0)
            );
            // debug!("Matches: {matches:?}");

            let new_groupings =
                Self::split_groups_on_case(&mut self.groups, &self.enumerator, self.last_processed_case, &case.case);
            self.groups.extend(new_groupings);

            self.groups.retain(|group| {
                if group.step > self.step_threshold {
                    self.pending_groups.push(group.clone());
                    false
                } else {
                    true
                }
            });

            self.cases[self.last_processed_case].matches = Matches::new(matches);
            Self::update_groups(
                self.use_endianness,
                self.step_threshold,
                &self.enumerator,
                &self.timeout,
                &mut self.groups,
                &self.cases[..self.last_processed_case + 1],
            );

            self.check_feasability();
            self.last_processed_case += 1;

            if self.failed {
                return Vec::new()
            }
        }

        loop {
            if self.failed || self.timeout.is_timed_out() {
                info!("Failed={}; Timeout={}", self.failed, self.timeout.is_timed_out());
                return Vec::new()
            }

            debug!("Groupings:");

            self.groups.sort_by_key(|g| g.step);

            for grouping in self.groups.iter() {
                debug!(
                    " - {:?} (step={}) {}",
                    grouping.map,
                    grouping.step,
                    grouping
                        .current
                        .map(|x| x
                            .decompress(&self.enumerator)
                            .to_template_computation()
                            .display(ARG_NAMES)
                            .to_string())
                        .unwrap_or(String::new())
                );
            }

            let used_groupings = &self.groups;

            let decisions = (0..self.cases.len())
                .map(|index| {
                    used_groupings
                        .iter()
                        .enumerate()
                        .filter(|(_, grouping)| grouping.map[index])
                        .map(|(index, _)| index)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            if decisions.iter().any(|d| d.is_empty()) {
                let mut seen = GrowingBitmap::new_all_zeros(self.cases.len());
                let min_needed = self
                    .groups
                    .iter()
                    .chain(self.pending_groups.iter())
                    .find(|group| seen.or_with(&group.map) && seen.is_all_ones());

                if let Some(min_needed) = min_needed {
                    assert!(
                        self.step_threshold < min_needed.step,
                        "Decisions: {decisions:?} (from {} groupings with step_threshold={}), min_needed={}",
                        self.groups.len(),
                        self.step_threshold,
                        min_needed.step
                    );
                    self.increase_step_threshold(min_needed.step);
                    continue
                } else {
                    info!("Unable to cover all cases");
                    self.failed = true;
                    return Vec::new()
                }
            }

            info!("Decisions: {decisions:?}");
            let mcs = MinimumCoveringSet::of(decisions, used_groupings.len());
            info!("Mcs = {mcs:?}");

            let mcs = mcs.into_vec();
            if mcs.len() > self.threshold_size {
                let max_steps = self
                    .groups
                    .iter()
                    .chain(self.pending_groups.iter())
                    .map(|g| g.step)
                    .max()
                    .unwrap();

                if self.step_threshold < max_steps {
                    info!("Increasing step threshold to {max_steps}");
                    self.increase_step_threshold(max_steps);
                    continue
                } else {
                    self.threshold_size = mcs.len();
                }
            }

            let max_step_used = mcs.iter().map(|&index| used_groupings[index].step).max().unwrap();

            let result = mcs
                .into_iter()
                .map(|index| used_groupings[index].to_template_computation(&self.enumerator))
                .collect::<Vec<_>>();

            if self.step_threshold != max_step_used {
                assert!(self.step_threshold > max_step_used);

                info!("Decreasing step threshold: {} => {max_step_used}", self.step_threshold);
                self.step_threshold = max_step_used;

                self.groups.retain(|group| {
                    if group.step > self.step_threshold {
                        self.pending_groups.push(group.clone());
                        false
                    } else {
                        true
                    }
                });
            }

            return result
        }
    }

    fn set_timeout(&mut self, stop_at: Instant) {
        self.timeout.set_timeout_at(stop_at);
    }

    fn has_given_up(&self) -> bool {
        self.failed
    }
}

impl BitmapMcsExpressionFinder {
    fn check_feasability(&mut self) {
        let mut unseen = GrowingBitmap::new_all_ones(self.last_processed_case);
        for grouping in self.groups.iter().chain(self.pending_groups.iter()) {
            unseen.clear_from(&grouping.map);
        }

        if !unseen.is_all_zeros() {
            info!("Unable to cover some items: {unseen:?}");
            self.failed = true;
        }
    }

    fn increase_step_threshold(&mut self, new_threshold: usize) {
        let s = Instant::now();
        info!("Increasing step threshold {} => {new_threshold}", self.step_threshold);

        let mut new_pending = Vec::new();

        self.step_threshold = new_threshold;
        while let Some(min_size) = self
            .pending_groups
            .iter()
            .filter(|g| g.step <= new_threshold)
            .map(|g| g.map.len())
            .min()
        {
            let mut groups = Vec::new();
            self.pending_groups.retain(|group| {
                if group.map.len() == min_size {
                    groups.push(group.clone());
                    false
                } else {
                    true
                }
            });

            Self::update_groups(
                self.use_endianness,
                self.step_threshold,
                &self.enumerator,
                &self.timeout,
                &mut groups,
                &self.cases[..min_size],
            );
            if self.timeout.is_timed_out() {
                return
            }

            assert!(!groups.iter().any(|g| g.current.is_none()));

            for (case_index, case) in self.cases.iter().enumerate().skip(min_size) {
                if self.timeout.is_timed_out() {
                    return
                }

                let new_groupings = Self::split_groups_on_case(&mut groups, &self.enumerator, case_index, &case.case);
                groups.extend(new_groupings);

                groups.retain(|group| {
                    if group.step > self.step_threshold {
                        new_pending.push(group.clone());
                        false
                    } else {
                        true
                    }
                });

                Self::update_groups(
                    self.use_endianness,
                    self.step_threshold,
                    &self.enumerator,
                    &self.timeout,
                    &mut groups,
                    &self.cases[..case_index + 1],
                );
                if self.timeout.is_timed_out() {
                    return
                }

                assert!(!groups.iter().any(|g| g.current.is_none()));
            }

            self.groups.extend(groups);
        }

        if self.timeout.is_timed_out() {
            return
        }

        assert!(!self.groups.iter().any(|g| g.current.is_none()));

        self.pending_groups.extend(new_pending);
        self.check_feasability();

        info!("Increasing step threshold took {}ms", s.elapsed().as_millis());
    }

    fn update_groups(
        use_endianness: bool, step_threshold: usize, enumerator: &ComputationEnumerator, timeout: &Timeout,
        groups: &mut Vec<Grouping>, cases: &[Case],
    ) {
        if groups.is_empty() || timeout.is_timed_out() {
            return
        }

        info!("Finding new positions...");

        let mut combined = Vec::new();
        if cases.len() >= 3 {
            let groupings = groups
                .iter()
                .filter(|g| g.current.is_none())
                .filter(|g| g.map.count_ones() >= 3)
                .collect::<Vec<_>>();

            let mut remaining_maps = groupings.iter().map(|g| g.map.clone()).collect::<Vec<_>>();
            info!(
                "Considering pre-computing some cases together for the {} groupings that need a new predicate, {} out of step threshold",
                groupings.len(),
                groupings.iter().filter(|g| g.step > step_threshold).count()
            );

            while remaining_maps.len() > 10 {
                info!("Maps remaining: {}", remaining_maps.len());
                let mut indices = Vec::new();
                let mut subset = remaining_maps.iter().collect::<Vec<_>>();
                let mut map = GrowingBitmap::new_all_ones(cases[0].matches.bitmap.len());
                for _ in 0..3 {
                    if let Some((best_index, _)) = (0..cases.len())
                        .filter(|index| !indices.contains(index))
                        .map(|index| (index, subset.iter().filter(|map| map[index]).count()))
                        .filter(|&(_, count)| count > 0)
                        .max_by_key(
                            |&(_index, count)| count, // as i64 * 10_000 - map.anded_with(&cases[index].matches.bitmap).count_ones() as i64
                        )
                    {
                        indices.push(best_index);
                        subset.retain(|map| map[best_index]);
                        map.and_with(&cases[best_index].matches.bitmap);
                    } else {
                        break
                    }
                }

                let best_group_count = subset.len();
                let best_num_preds = map.count_ones();

                // let mut best_group_count = 0;
                // let mut best_num_preds = 0;
                // for a in 0..cases.len() {
                //     for b in a + 1..cases.len() {
                //         for c in b + 1..cases.len() {
                //             let num_groups = remaining.iter()
                //                 .filter(|g| g.map[a] && g.map[b] && g.map[c])
                //                 .count();

                //             if num_groups > best_group_count {
                //                 let map = cases[a].matches.bitmap.anded_with(&cases[b].matches.bitmap);
                //                 let map = map.anded_with(&cases[c].matches.bitmap);
                //                 let num_preds = map.count_ones();

                //                 if num_preds < 500_000 {
                //                     best_group_count = num_groups;
                //                     best_num_preds = num_preds;
                //                     indices = vec![ a, b, c ];
                //                 }
                //             }
                //         }
                //     }
                // }

                info!("Best indices: {indices:?} cover {best_group_count} groups");
                info!("Number of results from the combination: {best_num_preds}");

                remaining_maps.retain_mut(|g| {
                    for &index in indices.iter() {
                        g.reset(index);
                    }

                    g.count_ones() > 1
                });

                if best_group_count > 0 {
                    combined.push((indices, Matches::new(map)));
                }

                if best_group_count <= 5 {
                    break
                }
            }
        }

        let s = Instant::now();
        let mut num = 0;

        groups.retain_mut(|grouping| {
            if timeout.is_timed_out() {
                return false
            }

            if grouping.current.is_none() {
                num += 1;
                let mut expected = Vec::new();
                let mut already_matched = GrowingBitmap::new();

                for (indices, map) in combined.iter() {
                    if indices.iter().all(|index| grouping.map[index]) && indices.iter().any(|index| !already_matched[index]) {
                        for &index in indices.iter() {
                            already_matched.set(index);
                        }

                        expected.push((map, true));
                    }
                }

                expected.extend(
                    cases
                        .iter()
                        .zip(grouping.map.iter())
                        .enumerate()
                        .filter(|(index, _)| !already_matched[index])
                        .map(|(_, (case, expected))| (&case.matches, expected)),
                );

                if let Some(position) = find_position_matching(grouping.position, &expected) {
                    grouping.position = position;
                } else {
                    debug!("Removing {:?}", grouping.map);
                    return false
                }
            }

            true
        });

        info!(
            "Finding new positions took {}ms / {}us per grouping",
            s.elapsed().as_millis(),
            s.elapsed().as_micros().checked_div(num).unwrap_or(0)
        );

        let mut indices_to_find = groups
            .iter()
            .filter(|g| g.current.is_none())
            .map(|g| if use_endianness { g.position / 2 } else { g.position })
            .collect::<Vec<_>>();
        indices_to_find.sort();
        indices_to_find.dedup();

        let mut exprs = HashMap::new();
        let mut last_index = 0;
        let mut enumerator = enumerator.clone();
        for &index in indices_to_find.iter() {
            enumerator.skip(index - last_index);
            last_index = index + 1;

            let expr = enumerator.find_next().unwrap();
            exprs.insert(
                index,
                (
                    expr.compress(OutputEncoding::UnsignedBigEndian),
                    expr.compress(OutputEncoding::UnsignedLittleEndian),
                ),
            );
        }

        for grouping in groups.iter_mut() {
            if grouping.current.is_none() {
                if use_endianness {
                    let n = grouping.position / 2;
                    let (big_endian, little_endian) = exprs.get(&n).unwrap();
                    grouping.current = Some(match grouping.position % 2 {
                        0 => *big_endian,
                        1 => *little_endian,
                        _ => unreachable!(),
                    });
                } else {
                    let n = grouping.position;
                    let (big_endian, _) = exprs.get(&n).unwrap();
                    grouping.current = Some(*big_endian);
                }
                debug!(
                    "Grouping {:?} = {}.",
                    grouping.map,
                    grouping.to_template_computation(&enumerator).display(ARG_NAMES)
                );
            }
        }
    }

    fn split_groups_on_case(
        groups: &mut [Grouping], enumerator: &ComputationEnumerator, case_index: usize, case: &PreparedCase,
    ) -> Vec<Grouping> {
        let mut new_groupings = Vec::new();
        for grouping in groups.iter_mut() {
            grouping.map.reset(case_index);
            let new_case_matches = grouping.current.map(|e| {
                let e = e.decompress(enumerator);
                e.prepared_compare_eq_with_args_indirect(case.args.as_slice(), &case.comparison)
            });

            let mut map = grouping.map.clone();
            map.set(case_index);
            let mut new_grouping = Grouping {
                map,
                current: grouping.current,
                negative: grouping.negative.clone(),
                position: grouping.position,
                step: grouping.step,
            };

            if new_case_matches.unwrap_or(false) {
                grouping.current = None;
                grouping.step += 1;
            } else {
                new_grouping.current = None;
                new_grouping.step += 1;
            }

            new_groupings.push(new_grouping);
        }
        new_groupings
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use liblisa::semantics::{Computation, IoType, ARG_NAMES};
    use liblisa::value::{AsValue, OwnedValue, Value};
    use test_log::test;

    use crate::tree::expr_finder::bitmap_mcs::BitmapMcsExpressionFinder;
    use crate::tree::expr_finder::{ExpressionFinder, TestSynthesizer};
    use crate::{synthesize_from_fn, SynthesizerBase};

    #[test]
    pub fn find_mux() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TestSynthesizer::<BitmapMcsExpressionFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                if inputs[2].unwrap_num() == 1 {
                    inputs[0].to_owned_value()
                } else {
                    inputs[1].to_owned_value()
                }
            })
        };
        let result = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f);
        println!("Result: {result:?}");
        assert!(result.is_some());
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_jump() {
        for _ in 0..100 {
            println!();
            println!();
            println!();

            let inputs = &[
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 1,
                },
            ];
            let s = TestSynthesizer::<BitmapMcsExpressionFinder>::new(
                inputs,
                IoType::Integer {
                    num_bits: 64,
                },
            );
            let f = |inputs: &[Value]| {
                Some(OwnedValue::Num({
                    if inputs[2].unwrap_num() == 1 {
                        inputs[0].unwrap_num().wrapping_add(inputs[1].unwrap_num())
                    } else {
                        inputs[1].unwrap_num()
                    }
                    .wrapping_add(2)
                }))
            };
            let result = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f);
            println!("Result: {result:?}");
            assert!(result.is_some());
        }
    }

    #[test]
    pub fn manual_find_jump_bad_case() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let mut s = BitmapMcsExpressionFinder::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );

        s.add_case(
            &[Value::Num(0x000000000000016D), Value::Num(0x000000000000016D), Value::Num(1)],
            Value::Num(0x2DC),
        );
        s.add_case(
            &[Value::Num(0xFFFFFFFFFFFFFFF6), Value::Num(0xFFFFFFFFFFFFFFF6), Value::Num(0)],
            Value::Num(0xFFFFFFFFFFFFFFF8),
        );
        s.add_case(
            &[Value::Num(0x0001E01AC1400000), Value::Num(0x0001E01AC1400000), Value::Num(0)],
            Value::Num(0x1E01AC1400002),
        );
        s.add_case(
            &[Value::Num(0x00003FFE70C7443A), Value::Num(0x00000471A4E418E2), Value::Num(0)],
            Value::Num(0x471A4E418E4),
        );
        s.add_case(
            &[Value::Num(0x000000000000006B), Value::Num(0x00000009B9F00000), Value::Num(1)],
            Value::Num(0x9B9F0006D),
        );
        s.add_case(
            &[Value::Num(0x00C35994C7022E00), Value::Num(0x00C35994C7022E00), Value::Num(0)],
            Value::Num(0xC35994C7022E02),
        );
        s.add_case(
            &[Value::Num(0xFFFFFFFFFFDF6F00), Value::Num(0x00660EEC80000000), Value::Num(1)],
            Value::Num(0x660EEC7FDF6F02),
        );
        s.add_case(
            &[Value::Num(0x0000012E68400000), Value::Num(0xFFD8BFFFFFFFFFFF), Value::Num(1)],
            Value::Num(0xFFD8C12E68400001),
        );

        let expressions = s.find_expressions();
        println!("{:?}", expressions.iter().map(|e| e.display(ARG_NAMES)).format(", "));
    }

    #[test]
    pub fn find_saturate() {
        let inputs = &[IoType::Integer {
            num_bits: 32,
        }];
        let mut s = BitmapMcsExpressionFinder::new(
            inputs,
            IoType::Integer {
                num_bits: 16,
            },
        );

        s.add_case(&[Value::Num(0xACBE6976)], Value::Num(0x1634));
        s.find_expressions();
        s.add_case(&[Value::Num(0x42457CB9)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x42C1633C)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x78230900)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x8038ADEA)], Value::Num(0x8000));
        s.find_expressions();
        s.add_case(&[Value::Num(0x7AA87457)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x4DBD6F84)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x7A6458C9)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x5A0F6C23)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x13A47700)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x0ECF7800)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x2ECA542F)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x560F300A)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x5B55620A)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x49BC6B5A)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x79D40E00)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x794D5100)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x6F8A4D63)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x76836918)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x5E6B4000)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x5B743D79)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x64903B66)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x64B2270F)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x49393B3F)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x660C6F00)], Value::Num(0x7FFF));
        s.find_expressions();
        s.add_case(&[Value::Num(0x51013A01)], Value::Num(0x7FFF));
        s.find_expressions();

        let expressions = s.find_expressions();
        println!("{:?}", expressions.iter().map(|e| e.display(ARG_NAMES)).format(", "));
    }
}
