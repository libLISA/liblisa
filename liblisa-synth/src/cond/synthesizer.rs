use std::collections::{HashMap, HashSet};
use std::time::Instant;

use itertools::Itertools;
use liblisa::semantics::{InputValues, IoType, ARG_NAMES};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::Symmetric2DMatrix;
use liblisa::value::{AsValue, OwnedValue, Value};
use log::{debug, error, info, warn};

use super::cache::SynthesizerCache;
use super::caselist::{CaseIndex, CaseList, GroupRef};
use super::casemap::CaseMap;
use super::combine_simple::SimplePredicateCombiner;
use super::switch::Switch;
use crate::cond::isomorphisms::Isomorphism;
use crate::cond::switch::SwitchCase;
use crate::predicate::{Disjunction, Term};
use crate::{Requester, Synthesizer, SynthesizerBase};

#[derive(Debug)]
struct MatchGroup {
    input_indices: Vec<usize>,
    match_true_indices: HashSet<CaseIndex>,
    match_false_indices: HashSet<CaseIndex>,
    match_true_groups: Vec<usize>,
    match_false_groups: Vec<usize>,
}

#[derive(Debug)]
enum SynthesisStep {
    SynthesizeConjunction {
        result: usize,

        /// The indices of the case groups that should match false, by input group.
        match_groups: Vec<MatchGroup>,

        /// A list of cases we should check after generating the conjunction
        conjunction_must_not_match: Vec<CaseIndex>,
    },
    Final {
        result: usize,
    },
}

#[derive(Debug)]
struct SynthesisPlanBuilder<'a> {
    steps: Vec<SynthesisStep>,
    group_transitions: Vec<Symmetric2DMatrix>,
    expanded_groups: Vec<Vec<usize>>,
    groups_done: GrowingBitmap,
    cases_done: GrowingBitmap,
    input_group_ignored: GrowingBitmap,
    cases: &'a CaseList,
}

struct Match<'a> {
    groups: Vec<usize>,
    cases: &'a HashSet<CaseIndex>,
}

#[derive(Debug)]
struct SynthesisPlan(Vec<SynthesisStep>);

impl SynthesisPlan {
    pub fn make(cases: &CaseList, isomorphisms: &[Isomorphism]) -> Self {
        let mut groups_remaining = cases.iter_groups().collect::<Vec<_>>();

        let group_transitions = cases.compute_group_transitions();

        let mut builder = SynthesisPlanBuilder {
            steps: Vec::new(),
            expanded_groups: (0..cases.num_groups()).map(|n| vec![n]).collect::<Vec<_>>(),
            group_transitions,
            cases_done: GrowingBitmap::new(),
            groups_done: GrowingBitmap::new(),
            input_group_ignored: GrowingBitmap::new(),
            cases,
        };

        while cases
            .iter_cases_indices()
            .any(|case_index| !builder.cases_done[case_index.as_usize()])
        {
            let result_counts = {
                let mut m = HashMap::new();
                for group in groups_remaining.iter() {
                    *m.entry(group.result()).or_insert(0) += 1;
                }

                m
            };

            if let Some(result) = result_counts.keys().copied().reduce(|mut a, b| {
                a.restrict_to(b);
                a
            }) && (!result.is_empty() || result_counts.keys().all(|m| m.is_empty()))
            {
                let final_result = result.first_index();

                if !builder.remaining_cases(final_result).is_empty() {
                    while let Some(group) = groups_remaining.pop() {
                        debug!(
                            "Matching group #{} before building final group, because we have missed cases remaining",
                            group.group_index()
                        );
                        builder.resolve_group(group);
                    }
                }

                let input_indices = cases.input_groups().flat_map(|g| g.iter()).copied().collect::<Vec<_>>();
                let remaining_cases = builder.remaining_cases(final_result);
                let must_not_match = cases
                    .iter_cases_indices()
                    .filter(|case_index| !builder.cases_done[case_index.as_usize()])
                    .filter(|case_index| {
                        cases[case_index]
                            .result()
                            .map(|other_result| other_result.matches(final_result))
                            .unwrap_or(false)
                    })
                    .collect::<Vec<_>>();

                if !remaining_cases.is_empty() {
                    info!("Before building the final group, we need to handle some missed cases: {remaining_cases:?}");

                    let results = remaining_cases
                        .iter()
                        .flat_map(|case_index| cases[case_index].result())
                        .collect::<HashSet<_>>();

                    for result in results.iter() {
                        let result = result.first_index();
                        let (match_true_cases, match_false_cases) = remaining_cases
                            .iter()
                            .partition(|&case_index| cases[case_index].result().unwrap().matches(result));
                        let match_group = builder.create_match_group(
                            result,
                            Match {
                                groups: Vec::new(),
                                cases: &match_true_cases,
                            },
                            Match {
                                groups: Vec::new(),
                                cases: &match_false_cases,
                            },
                            &mut GrowingBitmap::new(),
                            input_indices.clone(),
                        );

                        for case_index in match_group.match_true_indices.iter() {
                            builder.cases_done.set(case_index.as_usize());
                        }

                        info!("Matching {result} for {} remaining cases", match_true_cases.len());

                        builder.steps.push(SynthesisStep::SynthesizeConjunction {
                            result,
                            match_groups: vec![match_group],
                            conjunction_must_not_match: must_not_match
                                .iter()
                                .copied()
                                .filter(|&case_index| !cases[case_index].result().unwrap().matches(result))
                                .collect(),
                        });
                    }
                }

                info!("Building final group from: {result_counts:?}");
                builder.steps.push(SynthesisStep::Final {
                    result: final_result,
                });

                for case in cases.iter_cases_indices() {
                    builder.cases_done.set(case.as_usize());
                }

                groups_remaining.clear();
            }

            let applicable_isomorphism = isomorphisms
                .iter()
                .filter(|i| {
                    i.is_applicable(&builder.expanded_groups, builder.cases)
                        && !builder.input_group_ignored[i.input_group_index()]
                })
                .max_by_key(|i| (i.other_input_groups().len(), i.input_group_index()));
            if let Some(applicable_isomorphism) = applicable_isomorphism {
                debug!("Applying isomorphism: {applicable_isomorphism:#?}");
                let resolve = applicable_isomorphism
                    .groups_to_resolve()
                    .iter()
                    .min_by_key(|r| {
                        (
                            r.groups_to_resolve.len(),
                            r.groups_to_resolve.iter().copied().min().unwrap_or(0),
                        )
                    })
                    .unwrap();

                debug!("Groups to resolve: {:?}", resolve.groups_to_resolve);
                for &group_index in resolve.groups_to_resolve.iter() {
                    if !builder.groups_done[group_index] {
                        builder.resolve_group(builder.cases.group(group_index));
                    }
                }

                let expanded_groups = builder.expanded_groups.clone();
                for indices in builder.expanded_groups.iter_mut() {
                    let new = indices
                        .iter()
                        .flat_map(|index| {
                            applicable_isomorphism
                                .joined_group_indices()
                                .iter()
                                .filter(|g| g.contains(index))
                        })
                        .flat_map(|g| g.iter())
                        .flat_map(|&index| expanded_groups[index].iter())
                        .chain(indices.iter())
                        .copied()
                        .unique()
                        .collect::<Vec<_>>();

                    *indices = new;
                }

                debug!("Expanded groups: {:?}", builder.expanded_groups);

                groups_remaining.retain(|group| {
                    let group_index = group.group_index();
                    resolve.base_indices.contains(&group_index)
                        || !applicable_isomorphism
                            .joined_group_indices()
                            .iter()
                            .flat_map(|indices| indices.iter())
                            .any(|&index| builder.expanded_groups[index].contains(&group_index))
                });

                debug!(
                    "Groups remaining: {:?}",
                    groups_remaining.iter().map(|g| g.group_index()).format(", ")
                );

                builder.input_group_ignored.set(applicable_isomorphism.input_group_index());
            } else {
                // Match the result with the least groups
                let (result_to_match, _) = result_counts
                    .iter()
                    .min_by_key(|(map, count)| (map.len(), *count, map.first_index()))
                    .unwrap();

                debug!(
                    "Matching result {result_to_match:?} in groups {}",
                    groups_remaining.iter().map(|g| g.group_index()).join(", ")
                );

                while let Some(removal_index) = groups_remaining.iter().position(|group| group.result() == *result_to_match) {
                    let group = groups_remaining.remove(removal_index);
                    debug!("Matching group #{}", group.group_index());
                    builder.resolve_group(group);
                }
            }
        }

        let last = builder.steps.last_mut().unwrap();
        if let SynthesisStep::SynthesizeConjunction {
            result, ..
        } = last
        {
            *last = SynthesisStep::Final {
                result: *result,
            };
        }

        SynthesisPlan(builder.steps)
    }

    fn iter(&self) -> impl Iterator<Item = &SynthesisStep> {
        self.0.iter()
    }
}

impl SynthesisPlanBuilder<'_> {
    fn resolve_group(&mut self, group: GroupRef) {
        let match_true_group_indices = self.expanded_groups[group.group_index()]
            .iter()
            .filter(|&&group_index| self.groups_done.set(group_index))
            .copied()
            .collect::<Vec<_>>();

        assert!(!match_true_group_indices.is_empty());

        let result = match_true_group_indices
            .iter()
            .map(|&group_index| self.cases.group(group_index).result())
            .reduce(|mut a, b| {
                a.restrict_to(b);
                a
            })
            .unwrap();

        assert!(
            !result.is_empty(),
            "Created a match group with an empty result\ngroup={group:?}\nmatch_true_group_indices={match_true_group_indices:?}\nself={self:?}"
        );

        let result = result.first_index();

        let match_false_groups = self
            .cases
            .input_groups()
            .zip(self.group_transitions.iter())
            .enumerate()
            .filter(|(input_group_index, _)| !self.input_group_ignored[input_group_index])
            .map(|(_, (input_indices, transitions))| {
                (
                    input_indices.to_vec(),
                    match_true_group_indices
                        .iter()
                        .flat_map(|&group_index| transitions.iter_row_indices(group_index))
                        .flat_map(|index| self.expanded_groups[index].iter().copied())
                        .collect::<HashSet<_>>(),
                )
            })
            .collect::<Vec<_>>();

        debug!("Resolving groups {match_true_group_indices:?} vs {match_false_groups:?} with result {result}");

        // Normally, we include all cases. However, we exclude:
        let match_true_cases = match_true_group_indices
            .iter()
            .flat_map(|&group_index| self.cases.group(group_index).case_indices())
            // Exclude cases th: &CaseIndexat we have already matched (this only happens when a case belongs to multiple groups)
            .filter(|case_index| !self.cases_done[case_index.as_usize()])
            .filter(|case_index| {
                // Exclude cases that overlap with one of the match_false groups...
                let overlaps_with_match_false_group = self.cases[case_index]
                    .groups()
                    .iter()
                    .any(|group_index| match_false_groups.iter().any(|(_, s)| s.contains(group_index)));

                // ...unless this is the last chance for us to match this case
                let last_chance = self.cases[case_index]
                    .groups()
                    .iter()
                    .all(|group_index| match_true_group_indices.contains(group_index) || self.groups_done[group_index]);

                !overlaps_with_match_false_group || last_chance
            })
            .collect::<HashSet<_>>();
        debug!("    Match true = {:X?}", match_true_cases);

        let mut already_excluded = GrowingBitmap::new();
        let match_groups = match_false_groups
            .into_iter()
            .map(|(input_indices, match_false_group_indices)| {
                debug!("Group indices: {match_false_group_indices:?}");
                let match_false_cases = match_false_group_indices
                    .iter()
                    .map(|&index| self.cases.group(index))
                    .flat_map(|group| group.case_indices())
                    // Exclude cases that could also be in one of the groups we're match_true'ing
                    .filter(|case_index| {
                        !self.cases[case_index]
                            .groups()
                            .iter()
                            .any(|group_index| match_true_group_indices.contains(group_index))
                    })
                    .collect::<HashSet<_>>();

                self.create_match_group(
                    result,
                    Match {
                        groups: match_true_group_indices.clone(),
                        cases: &match_true_cases,
                    },
                    Match {
                        groups: match_false_group_indices.iter().copied().collect(),
                        cases: &match_false_cases,
                    },
                    &mut already_excluded,
                    input_indices,
                )
            })
            .collect::<Vec<_>>();

        // TODO: If any match_true is empty
        // TODO: Eliminate match_groups with empty match_falses

        for case_index in self.cases.iter_cases_indices() {
            if match_groups
                .iter()
                .all(|match_group| match_group.match_true_indices.contains(&case_index))
            {
                debug!("Marking case as done: {case_index:?}");
                self.cases_done.set(case_index.as_usize());
            }
        }

        // Cases that we haven't matched yet, and that return something different from what we're generating here.
        let conjunction_must_not_match = self
            .cases
            .iter_cases_indices()
            .filter(|case_index| !self.cases_done[case_index.as_usize()])
            .filter(|case_index| self.cases[case_index].result().map(|r| !r.matches(result)).unwrap_or(false))
            .filter(|case_index| !match_groups.iter().any(|g| g.match_false_indices.contains(case_index)))
            .collect::<Vec<_>>();

        self.steps.push(SynthesisStep::SynthesizeConjunction {
            result,
            match_groups,
            conjunction_must_not_match,
        });
    }

    fn create_match_group(
        &self, result: usize, match_true: Match, match_false: Match, already_excluded: &mut GrowingBitmap,
        input_indices: Vec<usize>,
    ) -> MatchGroup {
        let local_match_true = match_true
            .cases
            .iter()
            .map(|case| {
                input_indices
                    .iter()
                    .map(|&index| self.cases[case].inputs()[index].clone())
                    .collect::<Vec<_>>()
            })
            .collect::<HashSet<_>>();

        debug!("Creating match group with result {result} on input indices {input_indices:?}");
        let match_false_indices = match_false
            .cases
            .iter()
            .copied()
            // Exclude cases we've already matched to false in a previous term of this conjunction
            .filter(|case_index| !already_excluded[case_index.as_usize()])
            // Exclude cases that have the exact same value as the local_match_true values.
            // This sometimes happens when we haven't been able to match a case present in multiple groups,
            // and this group is the last one left.
            .filter(|case_index: &CaseIndex| {
                !local_match_true.contains(
                    &input_indices
                        .iter()
                        .map(|&index| self.cases[case_index].inputs()[index].clone())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<HashSet<_>>();

        debug!("match_false_indices = {match_false_indices:?}");

        for index in match_false_indices.iter() {
            already_excluded.set(index.as_usize());
        }

        let match_true_indices = match_true.cases.clone();

        debug!("match_true_indices = {match_true_indices:?}");

        {
            let local_match_false = {
                let mut v = match_false_indices
                    .iter()
                    .map(|case| {
                        input_indices
                            .iter()
                            .map(|&index| self.cases[case].inputs()[index].clone())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();

                v.sort();
                v.dedup();
                v
            };

            if let Some(overlapping_case) = local_match_false.iter().find(|&case| local_match_true.contains(case)) {
                panic!("Overlapping case {overlapping_case:X?} generated from {:?}", self.cases);
            }

            if let Some(overlapping_case) = local_match_true.iter().find(|&case| local_match_false.contains(case)) {
                panic!("Overlapping case {overlapping_case:X?} generated from {:?}", self.cases);
            }
        }

        if match_true_indices.iter().any(|index| match_false_indices.contains(index)) {
            panic!(
                "Identical case on both sides: match_true_indices={match_true_indices:?}, match_false_indices={match_false_indices:?}; Overlapping: {:?};\n\n {self:?}",
                match_true_indices
                    .iter()
                    .filter(|index| match_false_indices.contains(index))
                    .format(", ")
            )
        }

        MatchGroup {
            input_indices,
            match_true_indices,
            match_false_indices,
            match_true_groups: match_true.groups,
            match_false_groups: match_false.groups,
        }
    }

    fn remaining_cases(&self, final_result: usize) -> Vec<CaseIndex> {
        self.cases
            .iter_cases_indices()
            .filter(|case_index| !self.cases_done[case_index.as_usize()])
            .filter(|case_index| {
                self.cases[case_index]
                    .result()
                    .map(|other_result| !other_result.matches(final_result))
                    .unwrap_or(false)
            })
            .collect::<Vec<_>>()
    }
}

#[derive(Clone, Debug)]
pub struct ConditionSynthesizer {
    input_types: Vec<IoType>,
    hypothesis: Option<Switch>,
    cases: CaseList,
    /// Set to true if we failed to synthesize a good condition for a group.
    /// There is no point in re-trying the same synthesis again until we actually get a new group.
    needs_new_group: bool,
    waiting_for_new_group: usize,
    needs_group_stability: bool,
    waiting_for_group_stability: usize,
    cache: Vec<SynthesizerCache<SimplePredicateCombiner<'static>>>,
    failed: bool,
    permanent_fail: bool,
    timeout_at: Option<Instant>,
    group_conditions: Vec<Vec<(Disjunction, bool)>>,
}

impl SynthesizerBase for ConditionSynthesizer {
    type Hypothesis = Switch;
    type Computation = Switch;

    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        assert_eq!(
            output_type,
            IoType::Integer {
                num_bits: 8
            }
        );

        Self {
            input_types: input_types.to_vec(),
            cases: CaseList::new(input_types),
            hypothesis: None,
            needs_new_group: false,
            waiting_for_new_group: 0,
            cache: vec![SynthesizerCache::default(); 1usize.checked_shl(input_types.len() as u32).expect("Too many inputs")],
            failed: false,
            permanent_fail: false,
            timeout_at: None,
            needs_group_stability: false,
            waiting_for_group_stability: 0,
            group_conditions: Vec::new(),
        }
    }

    fn hypothesis(&self) -> Option<&Self::Hypothesis> {
        self.hypothesis.as_ref()
    }

    fn has_given_up(&self) -> bool {
        self.failed
    }

    fn needs_requester(&self) -> bool {
        true
    }

    fn set_timeout(&mut self, stop_at: Instant) {
        self.timeout_at = Some(stop_at);
        self.cases.set_timeout(stop_at);
    }

    fn into_computation(self) -> Option<Self::Computation> {
        self.hypothesis
    }
}

impl Synthesizer<CaseMap> for ConditionSynthesizer {
    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: &CaseMap) -> bool {
        self.hypothesis
            .as_ref()
            .map(|hyp| output.matches(hyp.evaluate(inputs)))
            .unwrap_or(false)
    }

    fn add_case<V: AsValue>(&mut self, _inputs: &[V], _output: CaseMap) {
        panic!("ProtoSynth needs the requester")
    }

    fn add_case_with_requests<V: AsValue>(&mut self, inputs: &[V], output: CaseMap, requester: &mut impl Requester<CaseMap>) {
        if self.failed {
            self.hypothesis = None;
            return
        }

        let group_conditions_consistent = self.group_conditions_are_consistent(inputs, &output, requester);
        let is_relevant = self.increases_variety(inputs) || !group_conditions_consistent.unwrap_or(false);
        let causes_regroup = group_conditions_consistent.is_none();
        if self.needs_group_stability && self.waiting_for_group_stability < 10_000 {
            self.hypothesis = None;

            if causes_regroup {
                if let Err(err) = self.cases.add_case(inputs, Some(output), requester) {
                    warn!("CaseList::add_case failed: {err}");
                    info!("Case list: {:?}", self.cases);
                    self.failed = true;
                    return
                }

                self.waiting_for_group_stability = 0;

                if !self.join_inputs_if_needed(requester) {
                    return;
                }
            } else {
                self.waiting_for_group_stability += 1;
            }

            return
        }

        if !self.is_consistent(inputs, &output) || is_relevant {
            if self.waiting_for_new_group < 1000 {
                info!(
                    "{inputs:X?} => {output:X?}; {} cases, {} cached synthesizers",
                    self.cases.len(),
                    self.cache.iter().map(|c| c.len()).sum::<usize>()
                );
                info!(
                    "Hypothesis predicted: {:X?}",
                    self.hypothesis.as_ref().map(|hyp| hyp.evaluate(inputs))
                );
            }

            #[cfg(debug_assertions)]
            {
                let requester_out = requester.request(inputs);
                if requester_out.unwrap() != output {
                    requester.request_debug(inputs);
                    panic!("Requester gave different response: {requester_out:?} vs {output:?} for {inputs:X?}");
                }
            }

            if self.needs_new_group {
                assert!(self.hypothesis.is_none());

                if !causes_regroup {
                    self.waiting_for_new_group += 1;

                    info!(
                        "waiting_for_new_group={} (num_groups={})",
                        self.waiting_for_new_group,
                        self.cases.num_groups()
                    );
                    if self.waiting_for_new_group >= 50_000 {
                        self.failed = true;
                    }

                    return
                } else {
                    self.needs_new_group = false;
                    self.waiting_for_new_group = 0;
                }
            }

            let existing_case = self.cases.find_case(inputs);
            if let Some(existing_case) = existing_case {
                if existing_case.result().map(|r| !r.overlaps(output)).unwrap_or(true) {
                    self.failed = true;
                    self.permanent_fail = true;
                    self.hypothesis = None;
                    warn!(
                        "New incoming case {inputs:X?} => {output:X?} does not match existing case: {:X?} -> {:X?}",
                        existing_case.inputs(),
                        existing_case.result()
                    );
                    return;
                }
            }

            if self.hypothesis.is_some()
                && let Some(existing_case) = existing_case
            {
                if existing_case.result().map(|c| c.is_empty()).unwrap_or(false) {
                    self.failed = true;
                    self.hypothesis = None;
                    error!("Cases are in invalid state: {:X?}", existing_case);
                    return
                }

                panic!(
                    "Hypothesis does not cover existing case:\n Hypothesis: {}\n Case: {:X?}\n\n Caselist: {:?}",
                    self.hypothesis.as_ref().unwrap().display(ARG_NAMES),
                    existing_case,
                    self.cases
                );
            } else if existing_case.is_none() {
                if let Err(err) = self.cases.add_case(inputs, Some(output), requester) {
                    warn!("CaseList::add_case failed: {err}");
                    info!("Case list: {:?}", self.cases);
                    self.failed = true;
                    return
                }
            }

            self.hypothesis = None;

            if !self.join_inputs_if_needed(requester) {
                return
            }

            let missing_result_index = self.cases.iter_groups().position(|group| group.result().is_empty());
            if let Some(group_index) = missing_result_index {
                let mut s = Switch::new();
                s.add_case(SwitchCase::new(Disjunction::always_true(), 0));

                info!("Setting always-true hypothesis because we're missing a result for group #{group_index}");
                self.hypothesis = Some(s);
            } else {
                let isomorphisms = if self.cases.num_groups() > 2 {
                    Isomorphism::all_of(&self.cases)
                } else {
                    Vec::new()
                };
                let plan = SynthesisPlan::make(&self.cases, &isomorphisms);
                debug!("Synthesis plan: {plan:#?}");

                self.tick();

                if let Some(result) = self.formulate_hypothesis(&plan) {
                    // TODO: See if we can move some switch conditions around to eliminate CaseMatches
                    info!("Hypothesis: {}", result.display(ARG_NAMES));

                    if !self.failed {
                        for case in self.cases.iter_cases_indices() {
                            let case = &self.cases[case];
                            let hyp_result = result.evaluate(case.inputs());
                            if case
                                .result()
                                .map(|r| !r.is_empty() && !r.matches(hyp_result))
                                .unwrap_or(false)
                            {
                                panic!(
                                    "Case {case:X?} does not match hypothesis: {}\nExpected: {:?}, found: {hyp_result:?}\n\nPlan: {plan:#?}\n\nCases: {:?}",
                                    result.display(ARG_NAMES),
                                    case.result(),
                                    self.cases
                                );
                            }
                        }

                        self.hypothesis = Some(result);
                    }
                } else {
                    assert!(self.failed || self.needs_new_group || self.needs_group_stability);
                }
            }
        }
    }
}

impl ConditionSynthesizer {
    pub fn is_timed_out(&self) -> bool {
        self.timeout_at.map(|timeout| Instant::now() >= timeout).unwrap_or(false)
    }

    /// Returns true if the synthesizer failed because it is inherently impossible to synthesize this expression.
    /// For example, when observation can return different results for the same inputs.
    pub fn permanent_fail(&self) -> bool {
        self.permanent_fail
    }

    pub fn contains_case<V: AsValue>(&self, inputs: &[V]) -> bool
    where
        [V]: hashbrown::Equivalent<InputValues>,
    {
        self.cases.contains_case(inputs)
    }

    pub fn increases_variety<V: AsValue>(&self, inputs: &[V]) -> bool {
        self.cases.increases_variety(inputs)
    }

    pub fn group_conditions_are_consistent<V: AsValue>(
        &self, inputs: &[V], output: &CaseMap, requester: &mut impl Requester<CaseMap>,
    ) -> Option<bool> {
        if let Some(group) = self.cases.determine_group(inputs, Some(*output), requester) {
            if output.len() > 1 {
                // TODO!
                return Some(true)
            }

            if let Some(cons) = self.group_conditions.get(group) {
                for (con, flip) in cons.iter() {
                    let val = con.evaluate(inputs) ^ flip;
                    if !val {
                        info!(
                            "For group #{group} we were expecting {con}, flip={flip} to yield true for {inputs:X?} -> {output:?}, but it returned false"
                        );
                        return Some(false)
                    }
                }
            }

            Some(true)
        } else {
            None
        }
    }

    fn formulate_hypothesis(&mut self, plan: &SynthesisPlan) -> Option<Switch> {
        self.group_conditions = self.cases.iter_groups().map(|_| Vec::new()).collect();

        info!("Formulating a hypothesis...");
        let mut cases_matched = GrowingBitmap::new();
        let mut switch = Switch::new();
        for step in plan.iter() {
            if self.is_timed_out() {
                self.failed = true;
                return None
            }

            match step {
                SynthesisStep::SynthesizeConjunction {
                    result,
                    match_groups,
                    conjunction_must_not_match,
                    ..
                } => {
                    info!("Formulating for step {step:?}");
                    let mut condition = Disjunction::always_true();

                    for item in match_groups.iter() {
                        if !item.match_false_indices.is_empty() {
                            let key = usize::try_from(
                                item.input_indices
                                    .iter()
                                    .map(|index| 1 << index)
                                    .reduce(|a, b| a | b)
                                    .unwrap(),
                            )
                            .unwrap();
                            let match_true_indices = item
                                .match_true_indices
                                .iter()
                                .copied()
                                .filter(|case_index| !cases_matched[case_index.as_usize()])
                                .collect::<Vec<_>>();
                            let match_false_indices = item.match_false_indices.iter().copied().collect::<Vec<_>>();
                            let input_indices = &item.input_indices;

                            if self.cache[key].get(&match_false_indices, &match_true_indices).is_some() {
                                info!("MISSED OPPORTUNITY: Could have used negated synthesizer as well...");
                            }

                            let (mut synthesizer, exact) = if let Some((synthesizer, exact)) =
                                self.cache[key].get(&match_true_indices, &match_false_indices)
                            {
                                (synthesizer.clone(), exact)
                            } else {
                                info!("No old synthesizers are suitable, creating a new one");
                                let mut s = SimplePredicateCombiner::new(
                                    &self.input_types,
                                    input_indices.clone(),
                                    IoType::Integer {
                                        num_bits: 1,
                                    },
                                );
                                if let Some(timeout_at) = self.timeout_at {
                                    s.set_timeout(timeout_at);
                                }

                                (s, false)
                            };

                            if !exact {
                                debug!("For inputs {:?}", input_indices);
                                debug!("  Match true:");
                                for case in match_true_indices.iter() {
                                    debug!("   - {case:?} {:X?}", self.cases[case].inputs());
                                }

                                debug!("  Match false:");
                                for case in match_false_indices.iter() {
                                    debug!("   - {case:?} {:X?}", self.cases[case].inputs());
                                }

                                let would_use_combined_solution = synthesizer.add_multiple_cases(
                                    match_true_indices
                                        .iter()
                                        .map(|index| (self.cases[index].inputs(), true))
                                        .chain(match_false_indices.iter().map(|index| (self.cases[index].inputs(), false))),
                                    !self.needs_group_stability,
                                );

                                if would_use_combined_solution {
                                    assert!(!self.needs_group_stability);
                                    self.needs_group_stability = true;
                                    info!("Aborting early, so we can first ensure group stability");
                                    return None
                                }
                            } else {
                                info!("Re-using exact synthesizer result");
                            }

                            if let Some(con) = synthesizer.hypothesis() {
                                let using_combined_solution = synthesizer.using_combined_solution();
                                let con = con.clone();
                                info!("Found terms: {}", con);

                                for &group_index in item.match_true_groups.iter() {
                                    self.group_conditions[group_index].push((con.clone(), false));
                                }

                                for &group_index in item.match_false_groups.iter() {
                                    self.group_conditions[group_index].push((con.clone(), true));
                                }

                                if !exact {
                                    self.cache[key].add(&match_true_indices, &match_false_indices, synthesizer)
                                }

                                info!(
                                    "Extending condition {} with {}",
                                    condition.display(ARG_NAMES),
                                    con.display(ARG_NAMES)
                                );
                                condition.and_also(&con);

                                if !self.needs_group_stability && using_combined_solution {
                                    self.needs_group_stability = true;
                                    info!("Aborting so we can first ensure group stability");
                                    return None
                                }
                            } else {
                                error!("Synthesis failed with {:?}", self.cases);
                                self.needs_new_group = true;
                                self.hypothesis = None;
                                return None
                            }
                        }
                    }

                    for case_index in self.cases.iter_cases_indices() {
                        if self.cases[case_index].result().map(|r| r.matches(*result)).unwrap_or(false)
                            && condition.evaluate(self.cases[case_index].inputs())
                        {
                            cases_matched.set(case_index.as_usize());
                        }
                    }

                    for conj in condition.iter_mut() {
                        let cases_to_avoid = conjunction_must_not_match
                            .iter()
                            .copied()
                            .filter(|case_index| !cases_matched[case_index.as_usize()])
                            .filter(|case_index| conj.evaluate(self.cases[case_index].inputs()))
                            .collect::<Vec<_>>();

                        if !cases_to_avoid.is_empty() {
                            // TODO: We should try to insert cases that will allow us to exclude these cases via transitions
                            info!("Excluding cases to avoid");
                            debug!("Manually excluding the following cases: {cases_to_avoid:?}");
                            conj.and_also_term(Term::CaseMatch {
                                negate: true,
                                input_indices: self.input_types.iter().copied().enumerate().collect(),
                                cases: cases_to_avoid
                                    .iter()
                                    .map(|case_index| self.cases[case_index].inputs().to_vec())
                                    .collect(),
                            });
                        }
                    }

                    // TODO: Filter CaseMatches for values that are already excluded / matched by the other terms in the conjunction
                    info!(
                        "Filtering unneeded case matches from condition: {}",
                        condition.display(ARG_NAMES)
                    );
                    for conjunction in condition.iter_mut() {
                        let actual_terms = conjunction
                            .iter()
                            .filter(|t| matches!(t, Term::Predicate { .. }))
                            .cloned()
                            .collect::<Vec<_>>();

                        if !actual_terms.is_empty() {
                            conjunction.retain_mut(|term| match term {
                                Term::CaseMatch { negate, input_indices, cases } => if *negate {
                                    cases.retain(|case| {
                                        let inputs = Self::create_case_from_partial(self.input_types.len(), input_indices, case);
                                        let already_matched = switch.conditions().any(|disjunction|
                                            disjunction.iter().any(|conjunction| {
                                                conjunction.iter().all(|term| term.used_input_indices().iter()
                                                    .all(|index| input_indices.iter().any(|(other_index, _)| index == other_index)
                                                ))
                                                && conjunction.evaluate(&inputs)
                                            })
                                        );
                                        if already_matched {
                                            return false
                                        }

                                        for term in actual_terms.iter() {
                                            if term.used_input_indices().iter()
                                                .all(|index| input_indices.iter().any(|(other_index, _)| index == other_index)
                                            ) {
                                                debug!("Term {} is applicable for input indices {input_indices:?}", term);
                                                if !term.evaluate(&inputs) {
                                                    debug!("Eliminating {case:X?} because it is covered by {} (tested with inputs {inputs:X?})", term);
                                                    return false
                                                }
                                            }
                                        }

                                        true
                                    });

                                    !cases.is_empty()
                                } else {
                                    true
                                },
                                Term::Predicate { .. } => true,
                            });
                        }
                    }

                    if !match_groups.is_empty() || !condition.is_always_false() {
                        switch.add_case(SwitchCase::new(condition, *result));
                    }
                },
                SynthesisStep::Final {
                    result,
                } => switch.add_case(SwitchCase::new(Disjunction::always_true(), *result)),
            }
        }

        Some(switch)
    }

    fn create_case_from_partial<'a>(
        num_inputs: usize, input_indices: &[(usize, IoType)], case: &'a [OwnedValue],
    ) -> Vec<Value<'a>> {
        (0..num_inputs)
            .map(|index| {
                input_indices
                    .iter()
                    .zip(case.iter())
                    .find(|&(&(input_index, _), _)| input_index == index)
                    .map(|(_, val)| val.as_value())
                    .unwrap_or(Value::Num(0))
            })
            .collect::<Vec<_>>()
    }

    fn check_input_joins(&self) -> Option<Vec<usize>> {
        let transitions = self.cases.compute_group_transitions();
        if transitions.len() >= 2 {
            let mut max_num = 8;
            let mut max = (&[][..], &[][..]);
            for (index_a, (transitions_a, input_group_a)) in transitions.iter().zip(self.cases.input_groups()).enumerate() {
                for (index_b, (transitions_b, input_group_b)) in transitions.iter().zip(self.cases.input_groups()).enumerate() {
                    if index_a < index_b {
                        let mut max_reachable = 0;

                        for group_index in 0..self.cases.num_groups() {
                            let mut seen = GrowingBitmap::new();
                            let mut frontier = vec![group_index];

                            while let Some(group_index) = frontier.pop() {
                                for target_group in transitions_a
                                    .iter_row_indices(group_index)
                                    .chain(transitions_b.iter_row_indices(group_index))
                                {
                                    if seen.set(target_group) {
                                        frontier.push(target_group);
                                    }
                                }
                            }

                            let num_seen = seen.count_ones();
                            if num_seen > max_reachable {
                                max_reachable = num_seen;
                            }
                        }

                        debug!("For input groups ({input_group_a:?}, {input_group_b:?}), {max_reachable} groups are reachable");

                        if max_reachable > max_num {
                            if (input_group_a.len() == 1 && self.input_types[input_group_a[0]].num_bits() <= 1)
                                || (input_group_b.len() == 1 && self.input_types[input_group_b[0]].num_bits() <= 1)
                            {
                                debug!("TODO: Come up with a proper metric to avoid joining with 1-bit inputs...")
                            } else {
                                max = (input_group_a, input_group_b);
                                max_num = max_reachable;
                            }
                        }
                    }
                }
            }

            if max_num > 8 {
                return Some(max.0.iter().chain(max.1.iter()).copied().collect())
            }

            // for group in self.cases.iter_groups() {
            //     // The number of different groups we can transition to for any given input index
            //     let mut sizes = transitions.iter().zip(self.cases.input_groups())
            //         .map(|(transitions, input_indices)| {
            //             let unique = transitions.iter_row_indices(group.group_index())
            //                 .filter(|&group_index| group_index != group.group_index())
            //                 .count();
            //             (input_indices, unique)
            //         }).collect::<Vec<_>>();
            //     sizes.sort_by_key(|&(_, len)| len);

            //     if sizes.len() >= 2 {
            //         let [(a_indices, a_num), (b_indices, b_num)]: [(_, _); 2] = sizes[sizes.len() - 2..].try_into().unwrap();
            //         let n = a_num * b_num;
            //         if n > 15 {
            //             let indices = a_indices.iter().chain(b_indices.iter()).copied().collect::<Vec<_>>();
            //             return Some(indices)
            //         }
            //     }
            // }
        }

        None
    }

    fn tick(&mut self) {
        for c in self.cache.iter_mut() {
            c.tick();
        }
    }

    fn join_inputs_if_needed(&mut self, requester: &mut impl Requester<CaseMap>) -> bool {
        loop {
            debug!("Caselist ({} cases): {:?}", self.cases.len(), self.cases);

            if let Some(indices) = self.check_input_joins() {
                info!("Joining inputs into {indices:?}");
                if let Err(err) = self.cases.join_inputs(&indices, requester) {
                    warn!("CaseList::join_inputs failed: {err}");
                    self.failed = true;
                    return false
                }

                self.needs_new_group = false;
                self.waiting_for_group_stability = 0;
            } else {
                break
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::IoType;
    use liblisa::value::{AsValue, OwnedValue, Value};
    use test_log::test;

    use super::ConditionSynthesizer;
    use crate::cond::casemap::CaseMap;
    use crate::{FnRequester, Requester, Synthesizer, SynthesizerBase};

    fn test_with_cases(s: &mut ConditionSynthesizer, requester: &mut impl Requester<CaseMap>, cases: &[&[OwnedValue]]) {
        for inputs in cases {
            let output = requester.request(inputs).unwrap();
            println!("Adding new case: {inputs:02X?} -> {output:?}");
            s.add_case_with_requests(inputs, output, requester);
        }
    }

    #[test]
    pub fn overfitted_condition() {
        let mut f = |inputs: &[Value<'_>]| {
            let (a, b) = (inputs[0].unwrap_bytes(), inputs[1].unwrap_bytes());
            let (a, b) = (
                i16::from_le_bytes(a.try_into().unwrap()),
                i16::from_le_bytes(b.try_into().unwrap()),
            );

            Some(CaseMap::new(if a < b { [false, true] } else { [true, false] }.into_iter()))
        };

        let mut s = ConditionSynthesizer::new(
            &[
                IoType::Bytes {
                    num_bytes: 2,
                },
                IoType::Bytes {
                    num_bytes: 2,
                },
            ],
            IoType::Integer {
                num_bits: 8,
            },
        );

        use OwnedValue::Bytes;
        let mut requester = FnRequester(&mut f);
        test_with_cases(
            &mut s,
            &mut requester,
            &[
                &[Bytes(vec![0xB6, 0x96]), Bytes(vec![0x7A, 0x7F])], // Output: 1
                &[Bytes(vec![0x5E, 0x38]), Bytes(vec![0x03, 0xEA])], // Output: 0
                &[Bytes(vec![0xA8, 0x1F]), Bytes(vec![0x00, 0x00])], // Output: 0
                &[Bytes(vec![0x01, 0x94]), Bytes(vec![0xBC, 0xD6])], // Output: 1
                &[Bytes(vec![0x7F, 0xFE]), Bytes(vec![0xFF, 0xF1])], // Output: 0
                &[Bytes(vec![0x84, 0x30]), Bytes(vec![0xFF, 0xFF])], // Output: 0
                &[Bytes(vec![0x62, 0x81]), Bytes(vec![0x00, 0x00])], // Output: 1
                &[Bytes(vec![0x80, 0x4E]), Bytes(vec![0xFF, 0xFF])], // Output: 0
                &[Bytes(vec![0x5B, 0x98]), Bytes(vec![0x00, 0x00])], // Output: 1
                &[Bytes(vec![0xAD, 0x34]), Bytes(vec![0xE6, 0x00])], // Output: 0
                &[Bytes(vec![0x05, 0x00]), Bytes(vec![0xFF, 0xFF])], // Output: 0
            ],
        );

        let inputs = &[Bytes(vec![0x05, 0x00]), Bytes(vec![0x7B, 0x7F])];
        let output = requester.request(inputs).unwrap();
        assert_eq!(
            s.group_conditions_are_consistent(inputs, &output, &mut requester),
            Some(false)
        );

        test_with_cases(
            &mut s,
            &mut requester,
            &[
                // TODO: This example should trigger re-evaluation of the incorrect conditions!
                inputs, // Output: 1
            ],
        );
    }
}
