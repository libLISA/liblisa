use std::collections::HashSet;
use std::time::Instant;

use arrayvec::ArrayVec;
use itertools::Itertools;
use liblisa::semantics::default::computation::{ExpressionComputation, OutputEncoding};
use liblisa::semantics::default::MAX_TEMPLATE_ARGS;
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64, GrowingBitmap};
use liblisa::utils::{MinimumCoveringSet, Timeout};
use liblisa::value::{AsValue, OwnedValue};
use log::{debug, info};

use crate::predicate::{Conjunction, Term};
use crate::search::searcher::{CheckFlippableBoolResult, Searcher};
use crate::search::{CompressedIterComputation, CompressedIterComputationWithExtraData, Cons, Nil};
use crate::templates::{CONST_VALUES, SIMPLE_BOOLEAN_TEMPLATES};
use crate::tree::PreparedInputs;
use crate::utils::delta_vec::DeltaVec;

#[derive(Clone, Debug, PartialEq)]
pub struct PartialTerm {
    compressed: CompressedIterComputation,
    negate: bool,
    predicate: ExpressionComputation,
    map: GrowingBitmap,
}

impl PartialTerm {
    pub fn evaluate(&self, case: &[OwnedValue]) -> bool {
        self.predicate.evaluate(case).interpret_as_bool() ^ self.negate
    }

    pub fn to_term(&self) -> Term {
        Term::Predicate {
            negate: self.negate,
            predicate: self.predicate.clone(),
        }
    }
}

#[derive(Clone)]
struct PredicateGroup {
    bitmap: GrowingBitmap,
    items: DeltaVec<CompressedIterComputationWithExtraData<Cons<0, 1, Nil>>>,
}

#[derive(Clone)]
pub struct Combiner<'a> {
    searcher: Searcher<'a, CheckFlippableBoolResult>,

    local_match_true: Vec<Vec<OwnedValue>>,
    unprocessed_match_true: Vec<PreparedInputs>,
    processed_match_true: Vec<PreparedInputs>,

    local_match_false: Vec<Vec<OwnedValue>>,
    unprocessed_match_false: Vec<PreparedInputs>,
    chosen_match_false: Vec<PreparedInputs>,

    local_to_global_index_map: Vec<Option<usize>>,
    timeout: Timeout,
    input_indices: Vec<usize>,

    matches: Vec<PredicateGroup>,
    failed: bool,
    last_mcs_size: usize,
}

pub enum CombinerResult {
    Found(Conjunction),
    McsLimitReached,
    Failed,
}

#[derive(Debug)]
struct Delta<B> {
    bitmap: B,
    map_to: MapTo,
}

#[derive(Copy, Clone, Debug)]
enum MapTo {
    True,
    PreviousMatchFalse(usize),
}

impl Combiner<'_> {
    pub fn new<'a>(
        input_types: &[IoType], input_indices: &[usize], timeout: Timeout, targets: impl Iterator<Item = &'a Vec<OwnedValue>>,
        avoid: impl Iterator<Item = &'a Vec<OwnedValue>>,
    ) -> Self {
        info!("Finding multiple terms for input indices {input_indices:?}");
        let local_input_types = input_indices.iter().map(|&index| input_types[index]).collect::<Vec<_>>();
        let local_to_global_index_map = input_indices.iter().map(|&index| Some(index)).collect::<Vec<_>>();
        let local_match_true = {
            let mut v = targets
                .map(|case| input_indices.iter().map(|&index| case[index].clone()).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            v.sort();
            v.dedup();
            v
        };
        let local_match_false = {
            let mut v = avoid
                .map(|case| input_indices.iter().map(|&index| case[index].clone()).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            v.sort();
            v.dedup();
            v
        };

        debug!("local_match_true = {local_match_true:X?}, local_match_false = {local_match_false:X?}");

        let mut matches_0 = Vec::new();
        let mut matches_1 = Vec::new();
        let mut searcher = Searcher::<CheckFlippableBoolResult>::new_with_custom_templates(
            &SIMPLE_BOOLEAN_TEMPLATES,
            &local_input_types,
            IoType::Integer {
                num_bits: 1,
            },
        );

        if let Some(overlapping) = local_match_false.iter().find(|case| local_match_true.contains(case)) {
            info!(
                "local_match_true and local_match_false *both* contain case {overlapping:X?}, returning a Combiner with failed = true"
            );

            return Combiner {
                input_indices: input_indices.to_vec(),
                chosen_match_false: Vec::new(),
                unprocessed_match_false: Vec::new(),
                local_match_true,
                local_match_false,
                unprocessed_match_true: Vec::new(),
                processed_match_true: Vec::new(),
                local_to_global_index_map,
                matches: Vec::new(),
                searcher,
                timeout,
                failed: true,
                last_mcs_size: 0,
            }
        }

        info!("Adding cases to searcher...");
        // TODO: Only pick a few cases from local_match_true; Store the others and only add them when we generate a hypothesis that doesn't match the stored cases...
        let mut unprocessed_match_true = local_match_true
            .iter()
            .map(|v| PreparedInputs::new(v, searcher.enumerator()))
            .collect::<Vec<_>>();

        let mut processed_match_true = Vec::new();

        for _ in 0..15 {
            if !unprocessed_match_true.is_empty() {
                let existing = processed_match_true
                    .iter()
                    .flat_map(|case: &PreparedInputs| case.arg_slice().iter().copied())
                    .collect::<HashSet<i128>>();
                let best_index = unprocessed_match_true
                    .iter()
                    .position_max_by_key(|case| {
                        let mut m = existing.clone();
                        case.arg_slice().iter().filter(|&&item| m.insert(item)).count()
                    })
                    .unwrap();
                // let index = rand::thread_rng().gen_range(0..unprocessed_match_true.len());
                let item = unprocessed_match_true.remove(best_index);

                searcher.add_case(item.inputs(), true);

                processed_match_true.push(item);
            }
        }

        let mut unprocessed_match_false = local_match_false
            .iter()
            .map(|v| PreparedInputs::new(v, searcher.enumerator()))
            .collect::<Vec<_>>();

        // TODO: Intelligently select case
        let interpreted_first_case = unprocessed_match_false.remove(0);

        info!("Finding all matching predicates...");
        info!("Splitting on {:X?}", interpreted_first_case.inputs());
        // TODO: Either speed this up, or find some performant way to terminate if we timeout
        while let Some((expr, check)) = searcher.next_expr() {
            let data = expr.compress(OutputEncoding::UnsignedBigEndian).with_extra_data();
            let data = data.add_value::<0, 1>(check.flip() as u64);

            // We immediately split the predicates into two groups, because:
            // - We will end up doing that before ever generating a hypothesis anyway
            // - We will allocate two slightly-less-huge Vecs instead of one huge vec, of which the memory won't ever be reclaimed.
            if expr.evaluate_as_bool_with_args(interpreted_first_case.arg_slice()) ^ check.flip() {
                matches_1.push(data);
            } else {
                matches_0.push(data);
            }
        }

        info!("Found {} + {} matching predicates", matches_0.len(), matches_1.len());

        Combiner {
            input_indices: input_indices.to_vec(),
            chosen_match_false: vec![interpreted_first_case],
            unprocessed_match_false,
            unprocessed_match_true,
            local_match_true,
            local_match_false,
            processed_match_true,
            local_to_global_index_map,
            matches: [
                PredicateGroup {
                    bitmap: GrowingBitmap::new_all_zeros(1),
                    items: matches_0.into_iter().collect(),
                },
                PredicateGroup {
                    bitmap: GrowingBitmap::new_all_ones(1),
                    items: matches_1.into_iter().collect(),
                },
            ]
            .into_iter()
            .filter(|g| !g.items.is_empty())
            .collect(),
            searcher,
            timeout,
            failed: false,
            last_mcs_size: 0,
        }
    }

    fn add_chosen_match_false(&mut self, case: PreparedInputs) {
        let index = self.chosen_match_false.len();

        if let Some(index) = self.chosen_match_false.iter().position(|c| c.inputs() == case.inputs()) {
            let case = &self.chosen_match_false[index];

            for group in self.matches.iter() {
                let expected = group.bitmap[index];
                for p in group.items.iter() {
                    let (term, flip) = p.pop_value();
                    let term = term.decompress(self.searcher.enumerator());
                    let arg_indexes = term
                        .arg_indexes()
                        .map(|index| index as u16)
                        .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
                    let result: bool = term
                        .template()
                        .evaluate_as_bool_with_args_indirect(case.arg_slice(), &arg_indexes)
                        ^ (flip != 0);

                    assert_eq!(
                        result,
                        expected,
                        "Term {} does not match grouping, flip={}, chosen_match_false={:X?}",
                        term.to_template_computation().display(ARG_NAMES),
                        flip,
                        self.chosen_match_false
                    );
                }
            }

            panic!("Already added case to chosen_match_false: {case:X?}\n\n")
        }

        let new_groups = match (case.arg_slice().len() + 63) / 64 {
            1 => self.extract_new_groups::<1>(&case, index),
            2 => self.extract_new_groups::<2>(&case, index),
            3 => self.extract_new_groups::<3>(&case, index),
            4 => self.extract_new_groups::<4>(&case, index),
            len => panic!("Arg slice too long: {len}*64 elements"),
        };

        self.matches.extend(new_groups);
        self.chosen_match_false.push(case);

        let total_items = self.matches.iter().map(|g| g.items.len()).sum::<usize>();
        info!("Total items: {total_items}");
    }

    fn extract_new_groups<const N: usize>(&mut self, case: &PreparedInputs, index: usize) -> Vec<PredicateGroup> {
        let deltas = self.compute_deltas::<N>(case);

        info!("Deltas: {deltas:#?}");
        let start = Instant::now();

        let mut num_evals_skipped = 0;
        let mut new_groups = Vec::new();
        self.matches.retain_mut(|group| {
            let prev_values = group.bitmap.iter().collect::<Vec<_>>();
            let mut match_1 = DeltaVec::new();
            group.items.retain(|data| {
                let (term, flip) = data.pop_value();
                let term = term.decompress(self.searcher.enumerator());
                let result: bool =
                    if let Some(identical_to) = deltas.iter().find(|d| term.arg_indexes().all(|index| !d.bitmap.get(index))) {
                        num_evals_skipped += 1;
                        match identical_to.map_to {
                            MapTo::True => true,
                            MapTo::PreviousMatchFalse(index) => prev_values[index],
                        }
                    } else {
                        let arg_indexes = term
                            .arg_indexes()
                            .map(|index| index as u16)
                            .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
                        term.template()
                            .evaluate_as_bool_with_args_indirect(case.arg_slice(), &arg_indexes)
                            ^ (flip != 0)
                    };

                if result {
                    match_1.push(*data);
                    false
                } else {
                    true
                }
            });

            group.bitmap.reset(index);

            if !match_1.is_empty() {
                let mut bitmap = group.bitmap.clone();
                bitmap.set(index);
                new_groups.push(PredicateGroup {
                    bitmap,
                    items: match_1,
                });
            }

            !group.items.is_empty()
        });

        info!("That took {}ms", start.elapsed().as_millis());
        info!("Evaluations skipped thanks to deltas: {num_evals_skipped}");

        new_groups
    }

    fn compute_deltas<const N: usize>(&mut self, case: &PreparedInputs) -> Vec<Delta<FixedBitmapU64<N>>> {
        let num_consts = CONST_VALUES.len();
        let num_inputs = case.arg_slice().len() - num_consts;
        let mut seen = HashSet::new();
        let mut deltas = self
            .processed_match_true
            .iter()
            .map(|prev| (MapTo::True, prev))
            .chain(
                self.chosen_match_false
                    .iter()
                    .enumerate()
                    .map(|(index, prev)| (MapTo::PreviousMatchFalse(index), prev)),
            )
            .map(|(map_to, prev)| Delta {
                bitmap: prev
                    .arg_slice()
                    .iter()
                    .zip(case.arg_slice().iter())
                    .map(|(a, b)| a != b)
                    .collect::<FixedBitmapU64<N>>(),
                map_to,
            })
            .filter(|item| item.bitmap.iter().skip(num_consts).take(num_inputs).any(|b| !b))
            .filter(|item| seen.insert(item.bitmap.clone()))
            .collect::<Vec<_>>();
        for index in (0..deltas.len()).rev() {
            let delta = &deltas[index];
            if deltas.iter().take(index).any(|d| delta.bitmap.is_superset_of(&d.bitmap)) {
                deltas.remove(index);
            }
        }
        deltas
    }

    pub fn next_conjunction(&mut self, max_mcs_size: usize) -> CombinerResult {
        if self.failed {
            return CombinerResult::Failed
        }

        if self.chosen_match_false.is_empty() {
            let case = self.unprocessed_match_false.remove(0);
            self.add_chosen_match_false(case);
        }

        'outer: loop {
            if self.timeout.is_timed_out() {
                self.failed = true;
                return CombinerResult::Failed
            }

            let mut candidates = Vec::new();
            for group in self.matches.iter() {
                let data = group.items.first().unwrap();
                let map = &group.bitmap;
                let (term, flip) = data.pop_value();
                let flip = flip != 0;
                let predicate = term.decompress(self.searcher.enumerator());
                if !map.is_all_ones()
                    && !self
                        .matches
                        .iter()
                        .any(|other| group.bitmap.is_superset_of(&other.bitmap) && other.bitmap != group.bitmap)
                {
                    let arg_indexes = predicate
                        .arg_indexes()
                        .map(|index| index as u16)
                        .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
                    if let Some(non_matching) = self.unprocessed_match_true.iter().position(|case| {
                        !(predicate
                            .template()
                            .evaluate_as_bool_with_args_indirect(case.arg_slice(), &arg_indexes)
                            ^ flip)
                    }) {
                        let case = self.unprocessed_match_true.remove(non_matching);

                        match (case.arg_slice().len() + 63) / 64 {
                            1 => self.process_unprocessed_match_true::<1>(case),
                            2 => self.process_unprocessed_match_true::<2>(case),
                            3 => self.process_unprocessed_match_true::<3>(case),
                            4 => self.process_unprocessed_match_true::<4>(case),
                            len => panic!("Arg slice too long: {len}*64 elements"),
                        }

                        continue 'outer;
                    }

                    info!(
                        "    Found predicate candidate (negate={flip}): {}",
                        predicate.display(ARG_NAMES)
                    );

                    candidates.push(PartialTerm {
                        compressed: term,
                        negate: flip,
                        predicate: predicate.to_template_computation(),
                        map: map.clone(),
                    });
                }
            }

            candidates.sort_by_key(|term| term.compressed);

            let choices = (0..self.chosen_match_false.len())
                .map(|n| {
                    candidates
                        .iter()
                        .enumerate()
                        .filter(|(_, g)| !g.map[n])
                        .map(|(index, _)| index)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            if let Some(index) = choices.iter().position(|c| c.is_empty()) {
                info!(
                    "We have no predicates to eliminate chosen match false case #{index}: {:X?}; Match groups: {:?}",
                    self.chosen_match_false[index],
                    self.matches.iter().map(|group| &group.bitmap).format(", "),
                );

                self.failed = true;
                return CombinerResult::Failed
            }

            info!("Choices to make: {choices:?}");

            let found = MinimumCoveringSet::of(choices, self.matches.len());

            info!("Minimum covering set: {found:?}");
            let terms = found
                .into_vec()
                .into_iter()
                .map(|index| &candidates[index])
                .collect::<Vec<_>>();
            info!(
                "Terms: {}",
                terms
                    .iter()
                    .map(|term| format!("{}{}", if term.negate { "!" } else { "" }, term.predicate.display(ARG_NAMES)))
                    .format(", ")
            );

            self.last_mcs_size = terms.len();

            if let Some(index) = self
                .unprocessed_match_false
                .iter()
                .position(|case| terms.iter().all(|e| e.evaluate(case.inputs())))
            {
                let add = self.unprocessed_match_false.remove(index);
                info!("Adding case and retrying: {add:X?}");

                // TODO: Re-use candidates, don't build an entirely new list
                self.add_chosen_match_false(add.clone());

                if terms.len() > max_mcs_size {
                    break CombinerResult::McsLimitReached
                }
            } else {
                let terms = terms
                    .into_iter()
                    .map(|e| {
                        let mut term = e.to_term();
                        term.remap_inputs(&self.local_to_global_index_map);
                        term
                    })
                    .collect();
                break CombinerResult::Found(Conjunction::new(terms))
            }
        }
    }

    fn process_unprocessed_match_true<const N: usize>(&mut self, case: PreparedInputs) {
        info!("Processing unprocessed local_match_true case {case:X?}");

        let deltas = self.compute_deltas::<N>(&case);

        info!("Deltas: {deltas:#?}");
        let start = Instant::now();

        let mut num_evals_skipped = 0;
        self.matches.retain_mut(|group| {
            let prev_values = group.bitmap.iter().collect::<Vec<_>>();
            group.items.retain(|data| {
                let (term, flip) = data.pop_value();
                let term = term.decompress(self.searcher.enumerator());

                if let Some(identical_to) = deltas.iter().find(|d| term.arg_indexes().all(|index| !d.bitmap.get(index))) {
                    num_evals_skipped += 1;
                    match identical_to.map_to {
                        MapTo::True => true,
                        MapTo::PreviousMatchFalse(index) => prev_values[index],
                    }
                } else {
                    let arg_indexes = term
                        .arg_indexes()
                        .map(|index| index as u16)
                        .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
                    (flip != 0)
                        ^ term
                            .template()
                            .evaluate_as_bool_with_args_indirect(case.arg_slice(), &arg_indexes)
                }
            });

            !group.items.is_empty()
        });

        info!("That took {}ms", start.elapsed().as_millis());
        info!("Evaluations skipped thanks to deltas: {num_evals_skipped}");

        self.processed_match_true.push(case);
    }

    pub fn add_case<V: AsValue>(&mut self, inputs: &[V], output: bool) {
        let inputs = self
            .input_indices
            .iter()
            .map(|&index| inputs[index].to_owned_value())
            .collect::<Vec<_>>();

        match output {
            true => {
                if !self.local_match_true.contains(&inputs) {
                    self.unprocessed_match_true
                        .push(PreparedInputs::new(&inputs, self.searcher.enumerator()));
                    self.local_match_true.push(inputs);
                }
            },
            false => {
                if !self.local_match_false.contains(&inputs) {
                    self.unprocessed_match_false
                        .push(PreparedInputs::new(&inputs, self.searcher.enumerator()));
                    self.local_match_false.push(inputs);
                }
            },
        }
    }

    pub fn last_mcs_size(&self) -> usize {
        self.last_mcs_size
    }

    pub fn has_failed(&self) -> bool {
        self.failed
    }
}
