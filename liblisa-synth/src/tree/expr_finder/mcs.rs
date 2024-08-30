use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::time::Instant;

use itertools::Itertools;
use liblisa::semantics::default::computation::{ExpressionComputation, OutputEncoding, PreparedComparison};
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::{MinimumCoveringSet, Timeout};
use liblisa::value::{AsValue, Value};
use log::{debug, info};

use super::ExpressionFinder;
use crate::search::searcher::{CheckValueResult, Searcher};
use crate::search::{CompressedIterComputation, ComputationEnumerator, IterItemComputation};
use crate::templates::EXPR_TEMPLATES;
use crate::tree::mapping::{PerfectMapping, Ptr};
use crate::tree::Case;

#[derive(Clone)]
struct PrimaryCase {
    case: Case,
    choice_map: GrowingBitmap,
    num_choices: usize,
    searcher: Searcher<'static, CheckValueResult>,
}

impl Debug for PrimaryCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrimaryCase").field("case", &self.case).finish()
    }
}

#[derive(Clone)]
struct AuxiliaryCase {
    case: Case,
    choice_map: GrowingBitmap,
    num_choices: usize,
}

impl Debug for AuxiliaryCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AuxiliaryCase").field("case", &self.case).finish()
    }
}

#[derive(Clone, Debug)]
enum ActiveCase {
    Primary(PrimaryCase),
    Auxiliary(AuxiliaryCase),
}

impl ActiveCase {
    pub fn is_primary(&self) -> bool {
        matches!(self, ActiveCase::Primary(_))
    }

    pub fn choice_map(&self) -> &GrowingBitmap {
        match self {
            ActiveCase::Primary(p) => &p.choice_map,
            ActiveCase::Auxiliary(a) => &a.choice_map,
        }
    }

    fn unwrap_primary(&mut self) -> &mut PrimaryCase {
        match self {
            ActiveCase::Primary(p) => p,
            ActiveCase::Auxiliary(_) => panic!("Called unwrap_primary on an auxiliary case"),
        }
    }
}

#[derive(Clone, Debug)]
struct Grouping {
    map: GrowingBitmap,
    items: Vec<u32>,
}

#[derive(Clone)]
pub struct McsExpressionFinder {
    cases: Vec<Case>,
    active_cases: Vec<ActiveCase>,
    mcs: Vec<ExpressionComputation>,
    fast_first: bool,
    output_type: IoType,

    enumerator: ComputationEnumerator<'static>,

    all_choices: PerfectMapping<CompressedIterComputation>,
    choice_order: Vec<u32>,

    groupings: Vec<Grouping>,
    timeout_at: Timeout,
    failed: bool,
}

impl ExpressionFinder for McsExpressionFinder {
    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        Self {
            cases: Vec::new(),
            active_cases: Vec::new(),
            mcs: Vec::new(),
            fast_first: true,
            output_type,
            enumerator: ComputationEnumerator::new(&EXPR_TEMPLATES, input_types, output_type),
            all_choices: PerfectMapping::new(),
            choice_order: Vec::new(),
            groupings: Vec::new(),
            timeout_at: Timeout::default(),
            failed: false,
        }
    }

    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: Value) {
        if self.failed {
            return
        }

        info!("Adding new choice for: {:X?} -> {:X?}", inputs, output);
        self.cases.push(Case::new(inputs, output));

        // TODO: Try adding an auxiliary case first.
        let first_match_index = self.all_choices.iter_keys().position(|c| {
            let expr = c.decompress(&self.enumerator);
            expr.compare_eq(inputs, output)
        });

        let first_match_index = if first_match_index.is_none() && self.fast_first && !self.active_cases.is_empty() {
            self.expand_fast_first(inputs, output, true);
            self.all_choices.iter_keys().position(|c: &CompressedIterComputation| {
                let expr = c.decompress(&self.enumerator);
                expr.compare_eq(inputs, output)
            })
        } else {
            first_match_index
        };

        if let Some(first_match_index) = first_match_index {
            info!("Adding auxiliary case");
            let mut choice_map = GrowingBitmap::new_all_zeros(self.all_choices.len());
            let mut num_choices = 0;
            for (expr, n) in self.all_choices.iter().skip(first_match_index) {
                let expr = expr.decompress(&self.enumerator);
                if expr.compare_eq(inputs, output) {
                    choice_map.set(n as usize);
                    num_choices += 1;
                }
            }

            let new_index = self.active_cases.len();
            self.update_existing_groupings(&choice_map, new_index);

            self.active_cases.push(ActiveCase::Auxiliary(AuxiliaryCase {
                case: Case::new(inputs, output),
                choice_map,
                num_choices,
            }));
        } else {
            info!("Adding primary case");
            let ptr = self.all_choices.pointer();
            let primary_case = self.create_primary_case(inputs, output, self.fast_first);
            if primary_case.num_choices == 0 {
                self.failed = true;
                return
            }

            // Update exiting groupings
            let new_index = self.active_cases.len();
            self.update_existing_groupings(&primary_case.choice_map, new_index);

            self.active_cases.push(ActiveCase::Primary(primary_case));

            self.add_new_choices(ptr);
        }

        loop {
            self.find_new_mcs();

            let mut covered = GrowingBitmap::new_all_zeros(self.mcs.len());

            for case in self.active_cases.iter() {
                if let ActiveCase::Primary(case) = case {
                    let covered_index = self
                        .mcs
                        .iter()
                        .position(|expr| expr.compare_eq(&case.case.inputs, case.case.output.as_value()))
                        .expect("The MCS should be a *covering* set, so it should cover this case");
                    covered.set(covered_index);
                }
            }

            if let Some((_, first_noncovered_expr)) = self.mcs.iter().enumerate().find(|(index, _)| !covered[index]) {
                if self.fast_first {
                    self.expand_fast_first(inputs, output, false);
                    continue
                }

                // Each expression in the MCS should correspond to at least one distinct primary case.
                // We now have multiple expressions that are together expressing a single primary case.
                // So we need to upgrade one of the auxiliary cases into a primary case.
                let active_case_index = self
                    .active_cases
                    .iter()
                    .position(|case| {
                        if let ActiveCase::Auxiliary(case) = case {
                            let inputs = &case.case.inputs;
                            let output = case.case.output.as_value();

                            self.mcs
                                .iter()
                                .enumerate()
                                .all(|(index, expr)| !covered[index] || !expr.compare_eq(inputs, output))
                                && first_noncovered_expr.compare_eq(inputs, output)
                        } else {
                            false
                        }
                    })
                    .unwrap();
                info!("Covered: {covered:?}, auxiliary case {active_case_index} covers first uncovered MCS expression");

                let case = match &self.active_cases[active_case_index] {
                    ActiveCase::Primary(_) => unreachable!(),
                    ActiveCase::Auxiliary(case) => case.case.clone(),
                };

                let ptr = self.all_choices.pointer();
                let primary_case = self.create_primary_case(&case.inputs, case.output.as_value(), false);

                self.active_cases[active_case_index] = ActiveCase::Primary(primary_case);

                self.add_new_choices(ptr);
            } else {
                break
            }
        }

        if self.timeout_at.is_timed_out() {
            self.failed = true;
        }
    }

    fn find_expressions(&mut self) -> Vec<ExpressionComputation> {
        self.mcs.clone()
    }

    fn set_timeout(&mut self, stop_at: Instant) {
        self.timeout_at.set_timeout_at(stop_at);
    }

    fn has_given_up(&self) -> bool {
        self.failed
    }
}

impl McsExpressionFinder {
    fn expand_fast_first<V: AsValue>(&mut self, inputs: &[V], output: Value, partial: bool) {
        let primary = self
            .active_cases
            .iter_mut()
            .find(|c| c.is_primary())
            .unwrap()
            .unwrap_primary();
        let ptr = self.all_choices.pointer();
        let mut ok = false;

        while let Some((item, result)) = primary.searcher.next_expr() {
            let ptr = self.all_choices.pointer();
            Self::add_primary_case_choice(
                self.output_type,
                &mut self.all_choices,
                &mut self.choice_order,
                result,
                &mut primary.num_choices,
                item,
                &mut primary.choice_map,
            );

            if partial
                && self.all_choices.iter_inv_added_since(ptr).any(|(c, _)| {
                    let expr = c.decompress(&self.enumerator);
                    expr.compare_eq(inputs, output)
                })
            {
                ok = true;
                break
            }
        }

        self.add_new_choices(ptr);

        if !ok {
            self.fast_first = false;
        }
    }

    fn create_primary_case<V: AsValue>(&mut self, inputs: &[V], output: Value, partial: bool) -> PrimaryCase {
        let mut searcher: Searcher<'static, CheckValueResult> = Searcher::new_from_enumerator(self.enumerator.clone());
        searcher.add_case(inputs, PreparedComparison::from(&output));

        let mut choice_map = GrowingBitmap::new_all_zeros(self.all_choices.len());
        let mut num_choices = 0;
        while let Some((item, result)) = searcher.next_expr() {
            let any_match = Self::add_primary_case_choice(
                self.output_type,
                &mut self.all_choices,
                &mut self.choice_order,
                result,
                &mut num_choices,
                item,
                &mut choice_map,
            );

            if partial && any_match {
                info!("Aborting early for fast first primary case");
                break
            }
        }

        PrimaryCase {
            case: Case::new(inputs, output),
            searcher,
            choice_map,
            num_choices,
        }
    }

    fn add_primary_case_choice(
        output_type: IoType, all_choices: &mut PerfectMapping<CompressedIterComputation>, choice_order: &mut Vec<u32>,
        result: CheckValueResult, num_choices: &mut usize, item: IterItemComputation, choice_map: &mut GrowingBitmap,
    ) -> bool {
        let (tmp1, tmp2);
        let items = if output_type.num_bits() > 8 {
            tmp1 = [
                (result.big_endian, OutputEncoding::UnsignedBigEndian),
                (result.little_endian, OutputEncoding::UnsignedLittleEndian),
            ];
            &tmp1[..]
        } else {
            tmp2 = [(result.big_endian, OutputEncoding::UnsignedBigEndian)];
            &tmp2[..]
        };

        let mut any_match = false;
        for &(is_match, endianness) in items {
            any_match |= is_match;
            if is_match {
                *num_choices += 1;
                let n = all_choices.get_or_insert(item.compress(endianness)) as usize;
                choice_map.set(n);

                if n >= choice_order.len() {
                    assert!(n == choice_order.len());
                    choice_order.push(*num_choices as u32);
                } else {
                    choice_order[n] = choice_order[n].min(*num_choices as u32);
                }
            }
        }

        any_match
    }

    fn update_existing_groupings(&mut self, choice_map: &GrowingBitmap, new_index: usize) {
        info!("Updating existing groupings...");
        let mut new_groupings = Vec::new();
        for grouping in self.groupings.iter_mut() {
            let mut removed = Vec::new();

            grouping.map.reset(new_index);
            debug!("Splitting grouping {:?}", grouping.map);
            grouping.items.retain(|item| {
                let remove = choice_map[*item as usize];
                if remove {
                    removed.push(*item);
                }

                !remove
            });

            if !removed.is_empty() {
                let mut map = grouping.map.clone();
                map.set(new_index);

                debug!("Adding grouping {map:?}");

                new_groupings.push(Grouping {
                    map,
                    items: removed,
                });
            }
        }

        self.groupings.extend(new_groupings);
    }

    fn add_new_choices(&mut self, ptr: Ptr) {
        // Add new choices to groupings
        info!("Adding new choices...");

        // Update all the auxiliary cases
        for case in self.active_cases.iter_mut() {
            if let ActiveCase::Auxiliary(case) = case {
                for (comp, n) in self.all_choices.iter_inv_added_since(ptr) {
                    let expr = comp.decompress(&self.enumerator);
                    if expr.compare_eq(&case.case.inputs, case.case.output.as_value()) {
                        case.choice_map.set(n as usize);
                    }
                }
            }
        }

        let mut mapping = self
            .groupings
            .iter()
            .enumerate()
            .map(|(index, g)| (g.map.clone(), index))
            .collect::<HashMap<_, _>>();
        for (_, item) in self.all_choices.iter_inv_added_since(ptr) {
            let map = self
                .active_cases
                .iter()
                .map(|case| case.choice_map()[item as usize])
                .collect::<GrowingBitmap>();

            if let Some(&index) = mapping.get(&map) {
                self.groupings[index].items.push(item);
            } else {
                mapping.insert(map.clone(), self.groupings.len());
                self.groupings.push(Grouping {
                    map,
                    items: vec![item],
                });
            }
        }
    }

    pub fn find_new_mcs(&mut self) {
        info!("Finding new MCS");
        if self.active_cases.len() > 1 {
            self.groupings.retain(|g| !g.items.is_empty());
            self.groupings
                .sort_by_cached_key(|g| g.items.iter().map(|&index| self.choice_order[index as usize]).min().unwrap());

            info!(
                "counts = {}",
                self.active_cases
                    .iter()
                    .map(|c| match c {
                        ActiveCase::Primary(p) => format!("primary {}", p.num_choices),
                        ActiveCase::Auxiliary(a) => format!("auxiliary {}", a.num_choices),
                    })
                    .format(", ")
            );

            // for (index, case) in self.active_cases.iter().enumerate() {
            //     let first_items = case.choice_map()
            //         .iter_one_indices()
            //         .sorted_by_key(|&index| self.choice_order[index])
            //         .take(100)
            //         .map(|index| (index, self.all_choices.get_inv(index).unwrap()))
            //         .map(|(index, compressed)| {
            //             let decompressed = compressed.decompress(&self.enumerator);
            //             format!("{} <{}>", decompressed.display(ARG_NAMES), self.groupings.iter().position(|g| g.items.contains(&index)).unwrap())
            //         })
            //         .format(", ");
            //     debug!("Active case #{index} (total: {}): {}", case.num_choices(), first_items);
            // }

            let enumerator = &self.enumerator;

            info!("Groups: {}", self.groupings.len());
            let decisions = (0..self.active_cases.len())
                .map(|index| {
                    self.groupings
                        .iter()
                        .enumerate()
                        .filter(|(_, grouping)| grouping.map[index])
                        .map(|(index, _)| index)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            info!("Decisions: {decisions:?}");
            let mcs = MinimumCoveringSet::of(decisions, self.groupings.len());
            info!("Mcs = {mcs:?}");

            self.mcs = mcs
                .into_vec()
                .into_iter()
                .map(|index| {
                    let item = self.groupings[index]
                        .items
                        .iter()
                        .min_by_key(|&&index| self.choice_order[index as usize])
                        .unwrap();
                    let item = self.all_choices.get_inv(*item).unwrap();
                    let decompressed = item.decompress(enumerator);
                    decompressed.to_template_computation()
                })
                .collect::<Vec<_>>();

            info!("Mcs = {}", self.mcs.iter().map(|expr| expr.display(ARG_NAMES)).format(", "));
            const MB: usize = 1024 * 1024;
            let mem_groupings = self.groupings.iter().map(|g| g.items.len() * 4).sum::<usize>();
            let mem_choices = self.all_choices.len() * 8;
            let mem_choice_order = self.choice_order.len() * 4;
            let mem_active_cases = self.active_cases.iter().map(|c| c.choice_map().len() / 8).sum::<usize>();
            info!(
                "Estimated memory usage: {}MiB",
                (mem_groupings + mem_choices + mem_choice_order + mem_active_cases) / MB
            );
            info!("Groupings: {}MiB", mem_groupings / MB);
            info!("Choices: {}MiB", mem_choices / MB);
            info!("Choice order: {}MiB", mem_choice_order / MB);
            info!("Active cases: {}MiB", mem_active_cases / MB);
            info!(
                "Highest compressed num: {}",
                self.all_choices.iter_keys().map(|k| k.as_u64()).max().unwrap()
            );
        } else {
            let group = self.groupings.first().unwrap();
            let item = group
                .items
                .iter()
                .min_by_key(|&&index| self.choice_order[index as usize])
                .unwrap();

            let item = self.all_choices.get_inv(*item).unwrap();
            let decompressed = item.decompress(&self.enumerator);
            let expr = decompressed.to_template_computation();

            self.mcs = vec![expr];
        }
    }
}
