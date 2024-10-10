use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Index;
use std::time::Instant;

use arrayvec::ArrayVec;
use hashbrown::HashSet;
use itertools::Itertools;
use liblisa::semantics::{InputValues, IoType};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::{Symmetric2DMatrix, Timeout};
use liblisa::value::{AsValue, OwnedValue, Value};
use log::{debug, info, trace, warn};

use super::casemap::CaseMap;
use super::input_hash::{InputHash, InputHasher};
use super::transitions::{Transition, TransitionMap, Transitions};
use super::MAX_INPUTS;
use crate::Requester;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct CaseIndex(u32);

impl CaseIndex {
    pub fn as_usize(self) -> usize {
        self.0.try_into().unwrap()
    }
}

impl Debug for CaseIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum CaseListError {
    #[error("calls to requester.request return different values for the same case")]
    ObservationsInconsistent,

    #[error("timed out")]
    Timeout,
}

#[derive(Clone, Debug)]
pub struct Case {
    inputs: Vec<OwnedValue>,
    hash: InputHash,
    result: Option<CaseMap>,
    transition_map: TransitionMap,
    primary_group: usize,
    all_groups: Vec<usize>,
    primary: bool,
}

impl Case {
    pub fn groups(&self) -> &[usize] {
        &self.all_groups
    }

    pub fn result(&self) -> Option<CaseMap> {
        self.result
    }

    pub fn inputs(&self) -> &[OwnedValue] {
        &self.inputs
    }
}

#[derive(Clone, Debug)]
pub struct Group {
    result: CaseMap,
    transition_map: TransitionMap,
    primary: CaseIndex,
}

impl Group {
    fn could_contain(&self, result: Option<CaseMap>, transition_map: &TransitionMap) -> bool {
        result.map(|result| result.covers(self.result)).unwrap_or(true) && self.transition_map.overlaps(transition_map)
    }

    fn could_join(&self, result: Option<CaseMap>, transition_map: &TransitionMap) -> bool {
        result.map(|result| result.overlaps(self.result)).unwrap_or(true) && self.transition_map.overlaps(transition_map)
    }
}

#[derive(Copy, Clone)]
pub struct GroupRef<'a> {
    caselist: &'a CaseList,
    group_index: usize,
    group: &'a Group,
}

impl<'a> GroupRef<'a> {
    pub fn result(&self) -> CaseMap {
        self.group.result
    }

    pub fn case_indices(&self) -> impl Iterator<Item = CaseIndex> + 'a {
        let group_index = self.group_index;
        self.caselist
            .cases
            .iter()
            .enumerate()
            .filter(move |(_, case)| case.all_groups.contains(&group_index))
            .map(|(index, _)| CaseIndex(index.try_into().unwrap()))
    }

    pub fn cases(&self) -> impl Iterator<Item = &'a Case> + 'a {
        let group_index = self.group_index;
        self.caselist
            .cases
            .iter()
            .filter(move |case| case.all_groups.contains(&group_index))
    }

    pub fn relations_for<'r>(&self, input_indices: &'r [usize]) -> RelationRef<'a, 'r> {
        RelationRef {
            caselist: self.caselist,
            input_indices,
            case_index: self.group.primary,
        }
    }

    pub fn group_index(&self) -> usize {
        self.group_index
    }
}

impl Debug for GroupRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.group, f)
    }
}

pub struct RelationRef<'a, 'i> {
    caselist: &'a CaseList,
    input_indices: &'i [usize],
    case_index: CaseIndex,
}

impl<'a, 'i: 'a> RelationRef<'a, 'i> {
    pub fn transition_indices(&self) -> impl Iterator<Item = CaseIndex> + 'a {
        let map = self
            .input_indices
            .iter()
            .map(|index| 1u64 << index)
            .reduce(|a, b| a | b)
            .unwrap();

        let hash = self.caselist[self.case_index].hash;
        let caselist = self.caselist;
        let inputs = self.caselist[self.case_index].inputs();
        let query = self.caselist.input_hasher.create_inputs_equal_query_inv(self.input_indices);

        self.caselist
            .cases_by_hash
            .iter()
            .filter(move |(&other_hash, _)| query.check(hash, other_hash))
            .flat_map(|(_, case_indices)| case_indices.iter().copied())
            .filter(move |&case_index| {
                caselist[case_index]
                    .inputs()
                    .iter()
                    .zip(inputs.iter())
                    .enumerate()
                    .all(|(index, (lhs, rhs))| map & (1 << index) != 0 || lhs == rhs)
            })
    }

    pub fn transitions(&self) -> impl Iterator<Item = &'a Case> {
        self.transition_indices().map(|index| &self.caselist[index])
    }
}

#[derive(Clone, Debug)]
struct InputGroup {
    indices: Vec<usize>,
    values: HashSet<ArrayVec<OwnedValue, MAX_INPUTS>>,
}

impl InputGroup {
    /// Returns whether new.
    fn add_values_if_new(&mut self, inputs: &[OwnedValue]) -> bool {
        let values = self.extract_values(inputs);

        self.values.insert(values)
    }

    fn extract_values<V: AsValue>(&self, inputs: &[V]) -> ArrayVec<OwnedValue, MAX_INPUTS> {
        self.indices
            .iter()
            .map(|&index| inputs[index].to_owned_value())
            .collect::<ArrayVec<_, MAX_INPUTS>>()
    }

    fn mux_values(&self, base_inputs: &[OwnedValue], new_values: &[OwnedValue]) -> Vec<OwnedValue> {
        base_inputs
            .iter()
            .zip(new_values.iter())
            .enumerate()
            .map(|(index, (lhs, rhs))| {
                if self.indices.contains(&index) {
                    rhs.clone()
                } else {
                    lhs.clone()
                }
            })
            .collect()
    }

    fn iter_all_variations<'a>(
        &'a self, base_inputs: &'a [OwnedValue],
    ) -> impl Iterator<Item = ArrayVec<Value<'a>, MAX_INPUTS>> + 'a {
        self.values.iter().map(|val| {
            let mut m = base_inputs.iter().map(AsValue::as_value).collect::<ArrayVec<_, MAX_INPUTS>>();

            for (&index, val) in self.indices.iter().zip(val.iter()) {
                m[index] = val.as_value();
            }

            m
        })
    }
}

#[derive(Clone)]
pub struct CaseList {
    /// The main list of cases.
    cases: Vec<Case>,

    /// Used to quickly find all cases that only differ by some inputs.
    cases_by_hash: HashMap<InputHash, Vec<CaseIndex>>,

    /// Used to quickly determine if we already added the case
    cases_hashset: HashSet<InputValues>,
    transitions: Vec<Transitions>,
    groups: Vec<Group>,
    input_groups: Vec<InputGroup>,
    timeout_at: Timeout,
    input_hasher: InputHasher,
}

impl Debug for CaseList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "CaseList({}) (transitions={:X?}) {{",
            self.input_groups.iter().map(|g| format!("{:?}", g.indices)).join(", "),
            self.transitions
        )?;
        for (group_index, group) in self.groups.iter().enumerate() {
            writeln!(
                f,
                " * Group #{group_index} result={:?} {:?}",
                group.result, group.transition_map
            )?;
            for (case_index, case) in self
                .cases
                .iter()
                .enumerate()
                .filter(|(_, case)| case.all_groups.contains(&group_index))
            {
                write!(
                    f,
                    "   - #{case_index}{} {:X?} -> {:?}",
                    if case.primary { "*" } else { "" },
                    case.inputs,
                    case.result
                )?;

                if case.all_groups.len() > 1 {
                    write!(f, " (other groups: {:?})", case.all_groups)?;
                }

                if case.transition_map.len() <= 64 {
                    write!(f, " {:?}", case.transition_map)?;
                }

                writeln!(f)?;

                // writeln!(f, "      {}", self.relations_for_case(CaseIndex(case_index as u16))
                //     .map(|rel| format!("{:?} => {}", rel.input_indices, rel.transition_indices().map(|s| format!("{s:?}")).join(", ")))
                //     .join("; ")
                // )?;
            }
        }
        writeln!(f, "}}")?;

        Ok(())
    }
}

impl CaseList {
    pub fn new(input_types: &[IoType]) -> Self {
        Self {
            cases: Vec::new(),
            cases_by_hash: HashMap::new(),
            cases_hashset: HashSet::new(),
            transitions: vec![Transitions::from_vec(Vec::new())],
            groups: Vec::new(),
            input_groups: input_types
                .iter()
                .enumerate()
                .map(|(n, _)| InputGroup {
                    indices: vec![n],
                    values: HashSet::new(),
                })
                .collect(),
            timeout_at: Timeout::default(),
            input_hasher: InputHasher::new(input_types),
        }
    }

    pub fn is_timed_out(&self) -> bool {
        self.timeout_at.is_timed_out()
    }

    pub fn set_timeout(&mut self, stop_at: Instant) {
        self.timeout_at.set_timeout_at(stop_at);
    }

    pub fn add_case<V: AsValue>(
        &mut self, inputs: &[V], result: Option<CaseMap>, requester: &mut impl Requester<CaseMap>,
    ) -> Result<CaseIndex, CaseListError> {
        let index = self.cases.len();
        if index >= u16::MAX as usize {
            panic!("CaseList cannot contain more than 65k entries");
        }

        let inputs = inputs.iter().map(AsValue::to_owned_value).collect::<Vec<_>>();

        // First add the new case itself
        let mut primaries_changed = false;
        if self.insert_internal(inputs, requester, result)? {
            primaries_changed |= self.regroup();
        }

        // Now we need to add new transitions related to this case
        // We don't need to do it for any cases we might add internally, as these are always composed from existing values.
        info!("Computing new transitions derived from this case");
        let case = &self.cases[index];
        let mut new_cases = HashSet::new();
        let primaries = self.iter_primaries().cloned().collect::<Vec<_>>();
        for ig in self.input_groups.iter_mut() {
            if ig.add_values_if_new(&case.inputs) {
                for primary in primaries.iter() {
                    let new_inputs = ig.mux_values(&primary.inputs, &case.inputs);
                    if !self.cases_hashset.contains(&new_inputs) {
                        new_cases.insert(new_inputs);
                    }
                }
            }
        }

        self.add_new_cases(new_cases, primaries_changed, requester)?;
        self.update_transitions(requester)?;

        Ok(CaseIndex(index.try_into().unwrap()))
    }

    fn add_new_cases(
        &mut self, mut new_cases: HashSet<Vec<OwnedValue>>, mut primaries_changed: bool, requester: &mut impl Requester<CaseMap>,
    ) -> Result<(), CaseListError> {
        info!("Adding new cases...");
        while !new_cases.is_empty() || primaries_changed {
            if self.is_timed_out() {
                return Err(CaseListError::Timeout)
            }

            info!(
                "Iteration with primaries_changed={primaries_changed}, new_cases={}",
                new_cases.len()
            );
            if primaries_changed {
                // Every time the primary cases in each group change, we will need to apply the transitions to the new primary case.
                self.insert_cases_for_new_primaries(&mut new_cases)?;

                primaries_changed = false;
            }

            let mut need_regroup = false;
            for inputs in new_cases.drain().sorted() {
                if self.is_timed_out() {
                    return Err(CaseListError::Timeout)
                }

                let result = requester.request(&inputs);
                need_regroup |= self.insert_internal(inputs, requester, result)?;
            }

            if need_regroup {
                primaries_changed |= self.regroup();
            }
        }

        Ok(())
    }

    fn insert_cases_for_new_primaries(&mut self, new_cases: &mut HashSet<Vec<OwnedValue>>) -> Result<(), CaseListError> {
        let primaries = self.iter_primaries().cloned().collect::<Vec<_>>();
        for ig in self.input_groups.iter_mut() {
            for primary in primaries.iter() {
                for inputs in ig.iter_all_variations(&primary.inputs) {
                    if !self.cases_hashset.contains(&inputs[..]) {
                        if self.timeout_at.is_timed_out() {
                            return Err(CaseListError::Timeout)
                        }

                        new_cases.insert(inputs.iter().map(AsValue::to_owned_value).collect());
                    }
                }
            }
        }

        Ok(())
    }

    pub fn increases_variety<V: AsValue>(&self, inputs: &[V]) -> bool {
        self.input_groups
            .iter()
            .any(|g| g.values.len() < 8 && !g.values.contains(&g.extract_values(inputs)))
    }

    pub fn determine_group<V: AsValue>(
        &self, inputs: &[V], result: Option<CaseMap>, requester: &mut impl Requester<CaseMap>,
    ) -> Option<usize> {
        let transition_map = TransitionMap::build_ext(&self.transitions, inputs, result, requester);
        let group = self.groups.iter().position(|g| g.transition_map.overlaps(&transition_map));

        match group {
            Some(group_index) => {
                let primary_result_len = self[self.groups[group_index].primary]
                    .result
                    .unwrap_or(CaseMap::new_from_u64(u64::MAX))
                    .len();

                if result.map(|r| r.len() < primary_result_len).unwrap_or(false) {
                    None
                } else {
                    Some(group_index)
                }
            },
            None => None,
        }
    }

    pub fn contains_case<V: AsValue>(&self, inputs: &[V]) -> bool
    where
        [V]: hashbrown::Equivalent<InputValues>,
    {
        self.cases_hashset.contains(inputs)
    }

    fn insert_internal(
        &mut self, inputs: Vec<OwnedValue>, requester: &mut impl Requester<CaseMap>, result: Option<CaseMap>,
    ) -> Result<bool, CaseListError> {
        info!("Internal insert: {inputs:X?} -> {result:?}");
        let transition_map = TransitionMap::build(&self.transitions, &inputs, requester);
        let group = self.groups.iter().position(|group| group.could_join(result, &transition_map));
        // let index = self.cases.len();

        if self.cases_hashset.contains(&inputs) {
            panic!("CaseList already contains case for: {inputs:X?}; {self:?}");
        }

        let transition_lookup = {
            let mut m = HashMap::new();

            for (index, tr) in self.transitions.iter().enumerate() {
                let map = tr.iter().fold(0, |acc, item| acc | (1 << item.input_index));
                m.entry(map).or_insert_with(Vec::new).push((index, tr));
            }

            m
        };

        for case in self.cases.iter() {
            let map = case
                .inputs
                .iter()
                .zip(inputs.iter())
                .enumerate()
                .map(|(index, (lhs, rhs))| ((lhs != rhs) as u64) << index)
                .reduce(|a, b| a | b)
                .unwrap();

            if let Some(&(transition_index, _)) = transition_lookup.get(&map).and_then(|v| {
                v.iter()
                    .find(|(_, tr)| tr.iter().all(|item| case.inputs()[item.input_index] == item.value))
            }) {
                if transition_map.get(transition_index) != case.result() {
                    info!(
                        "Inconsistent observations: {:?} vs {:?} for {:X?}",
                        transition_map.get(transition_index),
                        case.result(),
                        case.inputs()
                    );
                    // requester.request_debug(case.inputs());
                    return Err(CaseListError::ObservationsInconsistent)
                }
            }
        }

        let need_regroup = match group {
            None => true,
            Some(group_index) => {
                if let Some(result) = result {
                    assert!(
                        self.groups[group_index].result.overlaps(result),
                        "Seems like the result that was added is inconsistent with our observations: transition_map={transition_map:?}, transitions = {:X?}",
                        self.transitions
                    );
                }

                let primary_result_len = self[self.groups[group_index].primary]
                    .result
                    .unwrap_or(CaseMap::new_from_u64(u64::MAX))
                    .len();
                if result.map(|r| r.len() < primary_result_len).unwrap_or(false) {
                    true
                } else {
                    // We don't need a group update, but maybe we need to restrict...
                    if let Some(result) = result {
                        self.groups[group_index].result.restrict_to(result);
                    }

                    self.groups[group_index].transition_map.restrict_to(&transition_map);

                    false
                }
            },
        };

        let all_groups = self
            .groups
            .iter()
            .enumerate()
            .filter(|(_, group)| group.could_contain(result, &transition_map))
            .map(|(index, _)| index)
            .collect();
        self.cases_hashset.insert(inputs.iter().cloned().collect());
        let hash = self.input_hasher.hash(&inputs);
        self.cases_by_hash
            .entry(hash)
            .or_default()
            .push(CaseIndex(self.cases.len().try_into().unwrap()));
        self.cases.push(Case {
            inputs,
            hash,
            result,
            primary_group: group.unwrap_or(0),
            all_groups,
            transition_map,
            primary: false,
        });

        Ok(need_regroup)
    }

    fn rebuild_groups(&mut self) -> Vec<usize> {
        info!("Rebuilding groups...");
        self.groups.clear();
        let mut new_group = vec![0; self.cases.len()];

        for (case_index, case) in self.cases.iter().enumerate() {
            if let Some(index) = self
                .groups
                .iter()
                .position(|group| group.could_join(case.result, &case.transition_map))
            {
                trace!("Adding case {case_index} to existing group #{index}");
                if let Some(result) = case.result {
                    self.groups[index].result.restrict_to(result);
                }

                self.groups[index].transition_map.restrict_to(&case.transition_map);

                new_group[case_index] = index;
            } else {
                new_group[case_index] = self.groups.len();
                self.groups.push(Group {
                    // If this case has no result we use a "everything" casemap, that hopefully will get refined
                    // by cases we will consider after this one.
                    result: case.result.unwrap_or(CaseMap::new_from_u64(u64::MAX)),
                    transition_map: case.transition_map.clone(),
                    primary: CaseIndex(case_index.try_into().unwrap()),
                });
            };
        }

        for case in self.cases.iter() {
            for group in self.groups.iter_mut() {
                if group.could_join(case.result(), &case.transition_map) {
                    if let Some(result) = case.result() {
                        group.result.restrict_to(result);
                    }

                    group.transition_map.restrict_to(&case.transition_map);
                }
            }
        }

        new_group
    }

    fn regroup(&mut self) -> bool {
        let new_group = self.rebuild_groups();

        info!("Regrouping into {} groups according to: {new_group:?}", self.groups.len());

        let mut primary_len = vec![usize::MAX; self.groups.len()];
        for (case_index, (case, group)) in self.cases.iter_mut().zip(new_group.into_iter()).enumerate() {
            if case.primary_group != group {
                case.primary_group = group;
            }

            case.all_groups = self
                .groups
                .iter()
                .enumerate()
                .filter(|(_, group)| group.could_contain(case.result, &case.transition_map))
                .map(|(index, _)| index)
                .collect();

            if case.all_groups.is_empty() {
                println!("No group for case #{case_index:?} (should be {group}) {case:?}");
                panic!("No group for case #{case_index:?} in: {self:?}");
            }

            if case.result.map(|m| m.len() < primary_len[group]).unwrap_or(false) {
                primary_len[group] = case.result.unwrap().len();
                self.groups[group].primary = CaseIndex(case_index.try_into().unwrap());
            }
        }

        let mut primaries_updated = false;
        for (case_index, case) in self.cases.iter_mut().enumerate() {
            let primary = self
                .groups
                .iter()
                .any(|g| g.primary == CaseIndex(case_index.try_into().unwrap()));
            if case.primary != primary {
                debug!("Case #{case_index}: primary={primary}");
                case.primary = primary;
                primaries_updated = true;
            }
        }

        primaries_updated
    }

    fn values_in_group(&self, group: GroupRef, input_indices: &[usize]) -> HashMap<Vec<Value>, Vec<CaseIndex>> {
        let mut m = HashMap::new();
        for case_index in group.case_indices() {
            let case = &self[case_index];
            let values = input_indices
                .iter()
                .map(|&index| case.inputs()[index].as_value())
                .collect::<Vec<_>>();

            m.entry(values).or_insert_with(Vec::new).push(case_index);
        }

        m
    }

    pub fn compute_group_transitions(&self) -> Vec<Symmetric2DMatrix> {
        info!("Computing group transitions...");

        // TODO: Make this faster. Don't use relation_for_case, but instead loop over the cases once and add all relations as we go.
        self.input_groups().map(|input_indices| {
            let mut m = Symmetric2DMatrix::new();

            debug!("Checking transitions for inputs {input_indices:?}");
            for case_index in self.iter_cases_indices() {
                let case = &self[case_index];

                if case.groups().len() == 1 {
                    let transitions = self.relation_for_case(case_index, input_indices);
                    for other_case in transitions.transitions() {
                        if other_case.groups().len() == 1 && case.groups().iter().all(|group_index| !other_case.groups().contains(group_index)) {
                            let group_index = case.groups()[0];
                            let other_group_index = other_case.groups()[0];
                            if m.set(group_index, other_group_index) {
                                debug!("Transition between groups #{group_index} and #{other_group_index} because of cases #{case_index:?} and {:X?}", other_case.inputs());
                            }
                        }
                    }
                }
            }

            m
        }).collect::<Vec<_>>()
    }

    fn find_inconsistency(
        &self, transitions: &[Symmetric2DMatrix], ignored_inconsistencies: &[Symmetric2DMatrix],
    ) -> Option<(usize, usize, CaseIndex, usize, Vec<CaseIndex>)> {
        info!("Finding inconsistencies...");
        for (input_group_index, ((input_group, transitions), ignored_inconsistencies)) in self
            .input_groups
            .iter()
            .zip(transitions.iter())
            .zip(ignored_inconsistencies.iter())
            .enumerate()
        {
            let group_values = self
                .iter_groups()
                .map(|group| self.values_in_group(group, &input_group.indices))
                .collect::<Vec<_>>();

            for case_index in self.iter_cases_indices() {
                let case = &self[case_index];
                let case_val = input_group
                    .indices
                    .iter()
                    .map(|&index| case.inputs()[index].as_value())
                    .collect::<Vec<_>>();

                for &group_index in case.groups().iter() {
                    debug!(
                        "For case {case_index:?}, checking {group_index} <-> {:?}",
                        transitions.iter_row_indices(group_index).format(", ")
                    );
                    for target_group_index in transitions.iter_row_indices(group_index) {
                        if !ignored_inconsistencies.get(group_index, target_group_index) {
                            let target_group_values = &group_values[target_group_index];

                            if let Some(other_case_indices) = target_group_values.get(&case_val) {
                                debug!("Other case indices for group {target_group_index}: {other_case_indices:?}");
                                // Ignore other_case_indices that could belong to either group
                                let other_case_indices = other_case_indices
                                    .iter()
                                    .copied()
                                    .filter(|case_index| {
                                        self[case_index]
                                            .groups()
                                            .iter()
                                            .all(|group_index| !case.groups().contains(group_index))
                                    })
                                    .collect::<Vec<_>>();
                                let num_target_values = target_group_values
                                    .values()
                                    .filter(|case_indices| {
                                        case_indices.iter().any(|case_index| {
                                            self[case_index]
                                                .groups()
                                                .iter()
                                                .all(|group_index| !case.groups().contains(group_index))
                                        })
                                    })
                                    .count();
                                debug!(
                                    "Filtered other case indices: {other_case_indices:?}; Num target values: {num_target_values}"
                                );
                                if num_target_values > 1 && !other_case_indices.is_empty() {
                                    debug!(
                                        "Inconsistency over input indices {:?}: {case_index:X?} vs {other_case_indices:?}\n\nIn: {self:?}",
                                        input_group
                                    );

                                    return Some((
                                        input_group_index,
                                        group_index,
                                        case_index,
                                        target_group_index,
                                        other_case_indices,
                                    ))
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    fn update_transitions(&mut self, requester: &mut impl Requester<CaseMap>) -> Result<(), CaseListError> {
        info!("Checking for inconsistencies");
        // TODO: Ignore inconsistencies by (group_index, group_index) instead of (case_index, case_index)
        let mut ignored_inconsistencies = vec![Symmetric2DMatrix::new(); self.input_groups.len()];

        #[derive(Debug)]
        struct Inconsistency {
            lhs: Vec<CaseIndex>,
            rhs: Vec<CaseIndex>,
        }

        impl Inconsistency {
            fn results_for<'a>(
                cases: impl Iterator<Item = &'a Case> + 'a, transition: &'a Transitions,
                requester: &'a mut impl Requester<CaseMap>,
            ) -> impl Iterator<Item = Option<CaseMap>> + 'a {
                cases.map(move |case| transition.check_transition(case.inputs(), requester))
            }

            fn transition_is_useful(
                &self, transition: &Transitions, cases: &CaseList, requester: &mut impl Requester<CaseMap>,
            ) -> bool {
                let lhs_results = Self::results_for(self.lhs.iter().map(|&case_index| &cases[case_index]), transition, requester)
                    .collect::<HashSet<_>>();
                let mut rhs_results =
                    Self::results_for(self.rhs.iter().map(|&case_index| &cases[case_index]), transition, requester);

                debug!("lhs_results = {lhs_results:?}");

                let is_useful = rhs_results.any(|rhs_result| {
                    debug!("rhs_result = {rhs_result:?}");

                    lhs_results.iter().any(|lhs_result| match (lhs_result, rhs_result) {
                        (Some(lhs_result), Some(rhs_result)) => !lhs_result.overlaps(rhs_result),
                        (None, Some(_)) | (Some(_), None) => true,
                        (None, None) => false,
                    })
                });

                debug!("is_useful = {is_useful}");

                is_useful
            }
        }

        let mut transitions = self.compute_group_transitions();

        // Find inconsistencies
        while let Some((input_group_index, group_index, case_index, other_group_index, other_case_indices)) =
            self.find_inconsistency(&transitions, &ignored_inconsistencies)
        {
            let case = &self[case_index];

            let input_group = &self.input_groups[input_group_index];
            let other_input_indices = self
                .input_groups
                .iter()
                .enumerate()
                .filter(|&(index, _)| index != input_group_index)
                .flat_map(|(_, input_group)| input_group.indices.iter())
                .copied()
                .collect::<Vec<_>>();

            let cases_responsible_for_transition = {
                let mut pairs = Vec::new();
                for case_index in self.group(group_index).case_indices() {
                    let case = &self[case_index];
                    let transitions = self.relation_for_case(case_index, &input_group.indices);

                    for other_case_index in transitions.transition_indices() {
                        let other_case = &self[other_case_index];
                        if case
                            .groups()
                            .iter()
                            .all(|group_index| !other_case.groups().contains(group_index))
                            && case.groups().len() == 1
                            && other_case.groups().len() == 1
                            && other_case.groups().contains(&other_group_index)
                        {
                            pairs.push((case_index, other_case_index));
                        }
                    }
                }

                pairs
            };

            info!("Responsible for the transition existing: {cases_responsible_for_transition:?}");

            // TODO: Rework this.
            // - We have a transition between group G1 and G2, because there exist some cases between which there is a transition.
            // - We have cases in both G1 and G2 with the same values for the input group.
            // - We want to:
            //    - Keep the cases that caused the transition in the same groups
            //    - Separate the cases with identical values in either G1 or G2 into their own group
            // - Or vice versa?

            let inconsistencies = [
                // All cases in group_index matching case_index vs all cases in group_index NOT matching case_index.
                Inconsistency {
                    lhs: vec![case_index],
                    rhs: self
                        .group(group_index)
                        .case_indices()
                        .filter(|&case_index| {
                            input_group
                                .indices
                                .iter()
                                .any(|&index| self[case_index].inputs()[index] != case.inputs()[index])
                                && !self[case_index].groups().contains(&other_group_index)
                        })
                        .collect::<Vec<_>>(),
                },
                // All cases in other_group_index matching case_index vs all cases in other_group_index NOT matching case_index.
                Inconsistency {
                    lhs: other_case_indices.clone(),
                    rhs: self
                        .group(other_group_index)
                        .case_indices()
                        .filter(|&case_index| {
                            input_group
                                .indices
                                .iter()
                                .any(|&index| self[case_index].inputs()[index] != case.inputs()[index])
                                && !self[case_index]
                                    .groups()
                                    .iter()
                                    .any(|group_index| case.groups().contains(group_index))
                        })
                        .collect::<Vec<_>>(),
                },
                // The cases responsible for the transition vs all other cases in group `group_index`.
                {
                    let lhs = cases_responsible_for_transition
                        .iter()
                        .map(|&(case_index, _)| case_index)
                        .unique()
                        .collect::<Vec<_>>();
                    Inconsistency {
                        rhs: self
                            .group(group_index)
                            .case_indices()
                            .filter(|case_index| !lhs.contains(case_index))
                            .collect(),
                        lhs,
                    }
                },
                // The cases responsible for the transition vs all other cases in group `other_group_index`.
                {
                    let lhs = cases_responsible_for_transition
                        .iter()
                        .map(|&(_, case_index)| case_index)
                        .unique()
                        .collect::<Vec<_>>();
                    Inconsistency {
                        rhs: self
                            .group(other_group_index)
                            .case_indices()
                            .filter(|case_index| !lhs.contains(case_index))
                            .collect(),
                        lhs,
                    }
                },
            ];

            // TODO: There's another inconsistency we could check:
            // for any group G in case.groups(): the case `case` vs all other cases that don't match `case` for input_group.

            info!(
                "Inconsistency over input group #{input_group_index:?} with case {case_index:?} and inconsistencies {inconsistencies:?}"
            );

            let new_transitions = self
                .group(group_index)
                .cases()
                .chain(self.group(other_group_index).cases())
                .flat_map(|case| {
                    [
                        other_input_indices
                            .iter()
                            .map(|&input_index| Transition {
                                input_index,
                                value: case.inputs()[input_index].to_owned_value(),
                            })
                            .collect::<Transitions>(),
                        input_group
                            .indices
                            .iter()
                            .map(|&input_index| Transition {
                                input_index,
                                value: case.inputs()[input_index].to_owned_value(),
                            })
                            .collect::<Transitions>(),
                    ]
                })
                .collect::<Vec<_>>();

            info!("Checking if any transition is useful: {new_transitions:X?}");

            if let Some(useful_transition) = new_transitions.into_iter().find(|tr| {
                debug!("Checking {tr:X?}");
                if self.transitions.contains(tr) {
                    debug!("Transition {tr:X?} already exists");
                    return false
                }

                let any_useful = inconsistencies.iter().any(|ic| {
                    // Abort early if we've timed out
                    if self.is_timed_out() {
                        return true
                    }

                    ic.transition_is_useful(tr, self, requester)
                });
                debug!("Transition {tr:X?} useful for any inconsistency: {any_useful}");

                any_useful
            }) {
                if self.is_timed_out() {
                    return Err(CaseListError::Timeout)
                }

                self.add_transition(useful_transition, requester)?;
                transitions = self.compute_group_transitions();
            } else {
                ignored_inconsistencies[input_group_index].set(group_index, other_group_index);

                info!(
                    "No useful transitions for inconsistencies between group #{group_index} and #{other_group_index}: {inconsistencies:?}"
                );
                debug!("self: {self:?}");
                warn!(
                    "Ignoring inconsistencies between group #{group_index} and #{other_group_index} because we are unable to find a transition to resolve the inconsistency."
                );
            }

            info!("Finding next inconsistency...");

            if self.is_timed_out() {
                return Err(CaseListError::Timeout)
            }
        }

        info!(
            "We now have {} cases, {} transitions, {} hashes",
            self.cases.len(),
            self.transitions.len(),
            self.cases.iter().map(|case| case.hash).collect::<HashSet<_>>().len()
        );

        Ok(())
    }

    fn add_transition(
        &mut self, new_transition: Transitions, requester: &mut impl Requester<CaseMap>,
    ) -> Result<(), CaseListError> {
        if self.transitions.contains(&new_transition) {
            // TODO: If we've already added the transition, we should ignore the transition between these two groups.
            // If the input had *any* effect whatsoever on the output, we would have seen a difference.
            // The fact that we didn't, proves this input isn't used to distinguish between the two groups.
            panic!("Already added transition: {new_transition:X?} to {self:?}");
            // let group_a = case.group();
            // let group_b = self[other_case_indices[0]].group();
            // warn!("Ignoring transitions between groups {group_a:?} and {group_b:?}");

            // ignored_transitions[input_group_index].set(group_a, group_b);
        }
        for case in self.cases.iter_mut() {
            case.transition_map.push_transition(&case.inputs, &new_transition, requester);
        }

        self.transitions.push(new_transition);

        if self.regroup() {
            self.add_new_cases(HashSet::new(), true, requester)?;
        }

        Ok(())
    }

    pub fn iter_primaries(&self) -> impl Iterator<Item = &Case> + '_ {
        self.groups.iter().map(|group| &self[group.primary])
    }

    pub fn iter_groups(&self) -> impl Iterator<Item = GroupRef> {
        self.groups.iter().enumerate().map(|(group_index, group)| GroupRef {
            caselist: self,
            group_index,
            group,
        })
    }

    pub fn group(&self, group_index: usize) -> GroupRef {
        GroupRef {
            caselist: self,
            group_index,
            group: &self.groups[group_index],
        }
    }

    pub fn relation_for_case<'a, 'r>(&'a self, case_index: CaseIndex, input_indices: &'r [usize]) -> RelationRef<'a, 'r> {
        RelationRef {
            caselist: self,
            input_indices,
            case_index,
        }
    }

    pub fn num_groups(&self) -> usize {
        self.groups.len()
    }

    pub fn join_inputs(&mut self, indices: &[usize], requester: &mut impl Requester<CaseMap>) -> Result<(), CaseListError> {
        info!("Finding applicable indices");
        let applicable_indices = self
            .input_groups
            .iter()
            .enumerate()
            .filter(|(_, group)| indices.iter().any(|&index| group.indices.contains(&index)))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();

        info!("Applicable indices = {applicable_indices:?}");

        let first = applicable_indices[0];
        let rest = &applicable_indices[1..];

        let from = rest
            .iter()
            .rev()
            .map(|&index| self.input_groups.remove(index))
            .collect::<Vec<_>>();

        let primaries = self.iter_primaries().cloned().collect::<Vec<_>>();
        let target = &mut self.input_groups[first];

        for input_group in from {
            target.indices.extend(input_group.indices);
        }

        target.indices.sort();
        target.values.clear();

        info!("Re-scanning all values");

        for case in self.cases.iter() {
            target.add_values_if_new(&case.inputs);
        }

        let mut transitions_to_remove = GrowingBitmap::new_all_zeros(self.transitions.len());
        let mut index = 0;
        self.transitions.retain(|tr| {
            let result =
                indices.iter().all(|&index| tr.contains_input(index)) || indices.iter().all(|&index| !tr.contains_input(index));

            if !result {
                transitions_to_remove.set(index);
            }

            index += 1;

            result
        });

        for case in self.cases.iter_mut() {
            case.transition_map.remove_transitions(&transitions_to_remove);
        }

        // TODO: Only in debug mode...
        #[cfg(debug_assertions)]
        for case in self.cases.iter() {
            assert_eq!(
                case.transition_map,
                TransitionMap::build(&self.transitions, case.inputs(), requester)
            );
        }

        let mut new_cases = HashSet::new();
        for primary in primaries.iter() {
            for inputs in target.iter_all_variations(&primary.inputs) {
                if !self.cases_hashset.contains(&inputs[..]) {
                    new_cases.insert(inputs.iter().map(AsValue::to_owned_value).collect());
                }
            }
        }

        let primaries_changed = self.regroup();

        self.add_new_cases(new_cases, primaries_changed, requester)?;
        self.update_transitions(requester)?;

        info!(
            "Input joining of indices {indices:?} complete! We now have {} cases and {} transitions",
            self.cases.len(),
            self.transitions.len()
        );

        Ok(())
    }

    pub fn input_groups(&self) -> impl Iterator<Item = &[usize]> + '_ {
        self.input_groups.iter().map(|g| &g.indices[..])
    }

    pub fn iter_cases_indices(&self) -> impl Iterator<Item = CaseIndex> {
        (0..self.cases.len()).map(|index| CaseIndex(index.try_into().unwrap()))
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.cases.len()
    }

    pub fn find_case<V: AsValue>(&self, inputs: &[V]) -> Option<&Case> {
        self.cases.iter().find(|case| {
            case.inputs
                .iter()
                .zip(inputs.iter())
                .all(|(a, b)| a.as_value() == b.as_value())
        })
    }
}

impl Index<CaseIndex> for CaseList {
    type Output = Case;

    fn index(&self, index: CaseIndex) -> &Self::Output {
        &self.cases[index.0 as usize]
    }
}

impl Index<&CaseIndex> for CaseList {
    type Output = Case;

    fn index(&self, index: &CaseIndex) -> &Self::Output {
        &self[*index]
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::IoType;
    use liblisa::value::{AsValue, OwnedValue, Value};
    use test_log::test;

    use super::CaseList;
    use crate::cond::casemap::CaseMap;
    use crate::{FnRequester, Requester};

    #[test]
    pub fn groups_are_updated_correctly() {
        let mut f = |inputs: &[Value<'_>]| {
            use Value::*;

            Some(CaseMap::new(
                match inputs {
                    [Num(0x00), Num(0x00)] => [true, true],
                    [Num(0xD0), Num(0x00)] => [false, true],
                    [Num(0x00), Num(0xDB)] => [true, false],
                    [Num(0xD0), Num(0xDB)] => [true, false],
                    _ => unreachable!(),
                }
                .into_iter(),
            ))
        };
        let mut requester = FnRequester(&mut f);

        let mut l = CaseList::new(&[
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ]);
        l.add_case(
            &[OwnedValue::Num(0xD0), OwnedValue::Num(0x00)],
            Some(CaseMap::new([false, true].into_iter())),
            &mut requester,
        )
        .unwrap();

        l.add_case(
            &[OwnedValue::Num(0x00), OwnedValue::Num(0xDB)],
            Some(CaseMap::new([true, false].into_iter())),
            &mut requester,
        )
        .unwrap();

        println!("{l:?}");

        assert_eq!(l.group(0).case_indices().count(), 2);
        assert_eq!(l.group(1).case_indices().count(), 3);
    }

    #[test]
    pub fn variants_are_added() {
        let mut f = |inputs: &[Value<'_>]| {
            let zf = inputs[1].unwrap_num();
            let sf = inputs[2].unwrap_num();
            let of = inputs[3].unwrap_num();
            let flip_offset = inputs[4].unwrap_num();

            let val = if flip_offset >> 8 != 0 {
                zf == 0 && sf == of
            } else {
                zf == 1 || sf != of
            };

            Some(CaseMap::new_from_u64(if val { 0b10 } else { 0b01 }))
        };
        let mut requester = FnRequester(&mut f);

        let mut l = CaseList::new(&[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 9,
            },
        ]);

        for case in [
            &[
                Value::Num(0x220AACFFFFFA),
                Value::Num(1),
                Value::Num(1),
                Value::Num(0),
                Value::Num(0x110),
            ],
            &[
                Value::Num(0xFFFFFFFFFFF4DFEE),
                Value::Num(1),
                Value::Num(0),
                Value::Num(1),
                Value::Num(0x61),
            ],
            &[
                Value::Num(0xFFB),
                Value::Num(0),
                Value::Num(0),
                Value::Num(0),
                Value::Num(0x103),
            ],
        ] {
            let result = requester.request(case);
            l.add_case(case, result, &mut requester).unwrap();
        }

        println!("{l:?}");

        assert!(l
            .find_case(&[
                Value::Num(0xFFB),
                Value::Num(1),
                Value::Num(0),
                Value::Num(0),
                Value::Num(0x103)
            ])
            .is_some());
        assert!(l
            .find_case(&[
                Value::Num(0xFFB),
                Value::Num(0),
                Value::Num(1),
                Value::Num(0),
                Value::Num(0x103)
            ])
            .is_some());
        assert!(l
            .find_case(&[
                Value::Num(0xFFB),
                Value::Num(0),
                Value::Num(0),
                Value::Num(1),
                Value::Num(0x103)
            ])
            .is_some());
        assert!(l
            .find_case(&[
                Value::Num(0xFFB),
                Value::Num(0),
                Value::Num(0),
                Value::Num(0),
                Value::Num(0x61)
            ])
            .is_some());
        // assert_eq!(l.group(1).case_indices().count(), 2);
        // assert_eq!(l.group(2).case_indices().count(), 1);
    }

    #[test]
    pub fn no_groups_without_result() {
        //         - #0 [Bytes([A9, 43, 33, 38]), Bytes([0, 0, 80, CE, CE, DF, 75, D6])] -> Some(<0, 1>) [<0, 1>]
        //         [0] => #2, #6; [1] => #3
        //      - #2* [Bytes([21, FE, AE, BB]), Bytes([0, 0, 80, CE, CE, DF, 75, D6])] -> Some(1) [1]
        //         [0] => #0, #6; [1] => #1, #5
        //      - #3 [Bytes([A9, 43, 33, 38]), Bytes([B8, AE, F, 25, CE, 80, 0, 0])] -> Some(<0, 1, 2>) [<0, 1, 2>]
        //         [0] => #1, #7; [1] => #0
        //      - #4 [Bytes([24, 34, F5, E1]), Bytes([11, CA, 34, 50, D8, F9, FF, FF])] -> Some(0) [1]
        //         [0] => #5; [1] => #6, #7
        //      - #5 [Bytes([21, FE, AE, BB]), Bytes([11, CA, 34, 50, D8, F9, FF, FF])] -> Some(1) [1]
        //         [0] => #4; [1] => #1, #2
        //      - #6 [Bytes([24, 34, F5, E1]), Bytes([0, 0, 80, CE, CE, DF, 75, D6])] -> Some(1) [1]
        //         [0] => #0, #2; [1] => #4, #7
        //      - #7 [Bytes([24, 34, F5, E1]), Bytes([B8, AE, F, 25, CE, 80, 0, 0])] -> Some(<1, 2>) [<1, 2>]
        //         [0] => #1, #3; [1] => #4, #6
        //    * Group #1 result=<1, 2>
        //      - #1* [Bytes([21, FE, AE, BB]), Bytes([B8, AE, F, 25, CE, 80, 0, 0])] -> Some(<1, 2>) [<1, 2>]
        let mut f = |inputs: &[Value<'_>]| {
            let k = match (inputs[0].unwrap_bytes(), inputs[1].unwrap_bytes()) {
                (&[0xA9, 0x43, 0x33, 0x38], &[0x0, 0x0, 0x80, 0xCE, 0xCE, 0xDF, 0x75, 0xD6]) => &[0, 1][..],
                (&[0x21, 0xFE, 0xAE, 0xBB], &[0x0, 0x0, 0x80, 0xCE, 0xCE, 0xDF, 0x75, 0xD6]) => &[1],
                (&[0xA9, 0x43, 0x33, 0x38], &[0xB8, 0xAE, 0xF, 0x25, 0xCE, 0x80, 0x0, 0x0]) => &[0, 1, 2],
                (&[0x24, 0x34, 0xF5, 0xE1], &[0x11, 0xCA, 0x34, 0x50, 0xD8, 0xF9, 0xFF, 0xFF]) => &[0],
                (&[0x21, 0xFE, 0xAE, 0xBB], &[0x11, 0xCA, 0x34, 0x50, 0xD8, 0xF9, 0xFF, 0xFF]) => &[1],
                (&[0x24, 0x34, 0xF5, 0xE1], &[0x0, 0x0, 0x80, 0xCE, 0xCE, 0xDF, 0x75, 0xD6]) => &[1],
                (&[0x24, 0x34, 0xF5, 0xE1], &[0xB8, 0xAE, 0xF, 0x25, 0xCE, 0x80, 0x0, 0x0]) => &[1, 2],
                (&[0x21, 0xFE, 0xAE, 0xBB], &[0xB8, 0xAE, 0xF, 0x25, 0xCE, 0x80, 0x0, 0x0]) => &[1, 2],
                (&[0xA9, 0x43, 0x33, 0x38], &[0x11, 0xCA, 0x34, 0x50, 0xD8, 0xF9, 0xFF, 0xFF]) => &[0, 1], // I don't know!

                _ => unimplemented!("{inputs:X?}"),
            };

            Some(CaseMap::new((0..3).map(|n| k.contains(&n))))
        };
        let mut requester = FnRequester(&mut f);

        let mut l = CaseList::new(&[
            IoType::Bytes {
                num_bytes: 4,
            },
            IoType::Bytes {
                num_bytes: 8,
            },
        ]);

        for case in [
            &[
                Value::Bytes(&[0xA9, 0x43, 0x33, 0x38]),
                Value::Bytes(&[0x0, 0x0, 0x80, 0xCE, 0xCE, 0xDF, 0x75, 0xD6]),
            ],
            &[
                Value::Bytes(&[0x21, 0xFE, 0xAE, 0xBB]),
                Value::Bytes(&[0xB8, 0xAE, 0xF, 0x25, 0xCE, 0x80, 0x0, 0x0]),
            ],
            &[
                Value::Bytes(&[0x24, 0x34, 0xF5, 0xE1]),
                Value::Bytes(&[0x11, 0xCA, 0x34, 0x50, 0xD8, 0xF9, 0xFF, 0xFF]),
            ],
        ] {
            let result = requester.request(case);
            l.add_case(case, result, &mut requester).unwrap();
            println!("{l:?}");
        }

        println!("{l:?}");

        for group in l.iter_groups() {
            assert!(!group.result().is_empty());
        }
    }
}
