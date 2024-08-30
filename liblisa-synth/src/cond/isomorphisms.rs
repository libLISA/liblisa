use std::collections::HashMap;

use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::Symmetric2DMatrix;
use liblisa::value::AsValue;
use log::{debug, info};

use super::caselist::{CaseIndex, CaseList, GroupRef};

#[derive(Clone, Debug)]
pub struct Spliced<'a> {
    input_indices: Vec<usize>,
    other_input_indices: Vec<usize>,
    groups: Vec<Vec<GroupRef<'a>>>,
}

impl<'a> Spliced<'a> {
    pub fn by(cases: &'a CaseList, input_group_index: usize) -> Self {
        let mut unseen = cases.iter_groups().collect::<Vec<_>>();
        let mut result = Vec::new();

        let input_indices = cases
            .input_groups()
            .enumerate()
            .filter(|&(index, _)| index == input_group_index)
            .flat_map(|(_, items)| items.iter())
            .copied()
            .collect::<Vec<_>>();

        // TODO: Also for smaller subsets of other_input_indices...
        let other_input_indices = cases
            .input_groups()
            .enumerate()
            .filter(|&(index, _)| index != input_group_index)
            .flat_map(|(_, items)| items.iter())
            .copied()
            .collect::<Vec<_>>();

        while let Some(item) = unseen.pop() {
            debug!("Expanding from group #{}", item.group_index());

            let mut group_of_groups = vec![item];
            let mut seen = GrowingBitmap::new();
            seen.set(item.group_index());

            let mut frontier = 0;
            while frontier < group_of_groups.len() {
                let new = &group_of_groups[frontier];
                for item in new.relations_for(&other_input_indices).transition_indices() {
                    for &group_index in cases[item].groups().iter() {
                        if !seen.set(group_index) {
                            unseen.retain(|group| {
                                if group.group_index() != group_index {
                                    true
                                } else {
                                    group_of_groups.push(*group);
                                    false
                                }
                            });
                        }
                    }
                }

                frontier += 1;
            }

            result.push(group_of_groups);
        }

        Spliced {
            input_indices,
            other_input_indices,
            groups: result,
        }
    }

    fn compute_bijective_map<'r>(
        &self, num_groups: usize, lhs: &[GroupRef<'r>], rhs: &[GroupRef<'r>],
    ) -> Option<BijectiveMap<'r>> {
        if lhs.is_empty() || lhs.len() != rhs.len() {
            return None
        }

        info!(
            "Determining bijectivity between groups {:?} and groups {:?} using input indices {:?}",
            lhs.iter().map(|g| g.group_index()).collect::<Vec<_>>(),
            rhs.iter().map(|g| g.group_index()).collect::<Vec<_>>(),
            self.input_indices
        );
        let mut seen = GrowingBitmap::new();
        let mut mapping = Vec::with_capacity(lhs.len());
        for lhs in lhs.iter() {
            let relations = lhs.relations_for(&self.input_indices);
            if let Some((group_indices, true)) = relations
                .transitions()
                .map(|case| (case.groups(), true))
                .reduce(|(a, unique_a), (b, unique_b)| (a, unique_a && unique_b && a == b))
            {
                if group_indices.len() > 1 {
                    return None;
                }

                let group_index = group_indices[0];

                if seen.set(group_index) {
                    if let Some(rhs) = rhs.iter().find(|g| g.group_index() == group_index) {
                        debug!("Mapping: {lhs:?} <-> {rhs:?}");
                        mapping.push((*lhs, *rhs));
                    }
                } else {
                    debug!("Group {lhs:?} has no unique mapping");
                    return None
                }
            } else {
                debug!("Group {lhs:?} has no mapping");
                return None
            }
        }

        info!("Done!");

        if mapping.is_empty() {
            None
        } else {
            Some(BijectiveMap::new(
                num_groups,
                mapping,
                self.input_indices.clone(),
                self.other_input_indices.clone(),
            ))
        }
    }

    pub fn bijective_groups(&self, cases: &CaseList) -> Vec<Vec<BijectiveMap>> {
        let mut is_bijective = Symmetric2DMatrix::new();
        let mut maps = Vec::new();

        for (x, lhs) in self.groups.iter().enumerate() {
            for (y, rhs) in self.groups.iter().enumerate() {
                if x < y {
                    if let Some(map) = self.compute_bijective_map(cases.num_groups(), lhs, rhs) {
                        info!("Comparing transitions in bijective map ({x}, {y})");
                        if map.transitions_equal(cases) {
                            info!("All transitions in bijective map are equal: {map:?}");
                            is_bijective.set(x, y);
                            maps.push((x, y, map));
                        } else {
                            info!("Bijective map does not have equal transitions: {map:?}");
                        }
                    }
                }
            }
        }

        info!("Bijectivity: {is_bijective:?}");
        info!("Bijective maps: {maps:?}");

        let mut groups = Vec::new();

        while let Some((x, y, item)) = maps.pop() {
            let mut group = vec![item];
            let mut indices = vec![x, y];

            let mut frontier = 0;
            while frontier < indices.len() {
                let new = indices[frontier];

                maps.retain(|(x, y, item)| {
                    if *x == new || *y == new {
                        group.push(item.clone());

                        if !indices.contains(x) {
                            indices.push(*x);
                        }

                        if !indices.contains(y) {
                            indices.push(*y);
                        }

                        false
                    } else {
                        true
                    }
                });

                frontier += 1;
            }

            groups.push(group);
        }

        groups
    }
}

#[derive(Clone)]
pub struct BijectiveMap<'r> {
    mapping: Vec<(GroupRef<'r>, GroupRef<'r>)>,
    lhs_to_rhs: Vec<Option<usize>>,
    rhs_to_lhs: Vec<Option<usize>>,
    input_indices: Vec<usize>,
    other_input_indices: Vec<usize>,
}

impl std::fmt::Debug for BijectiveMap<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BijectiveMap")
            .field(
                "mapping",
                &self
                    .mapping
                    .iter()
                    .map(|(lhs, rhs)| (lhs.group_index(), rhs.group_index()))
                    .collect::<Vec<_>>(),
            )
            .field("lhs_to_rhs", &self.lhs_to_rhs)
            .field("rhs_to_lhs", &self.rhs_to_lhs)
            .field("input_indices", &self.input_indices)
            .field("other_input_indices", &self.other_input_indices)
            .finish()
    }
}

impl<'r> BijectiveMap<'r> {
    pub fn new(
        num_groups: usize, mapping: Vec<(GroupRef<'r>, GroupRef<'r>)>, input_indices: Vec<usize>, other_input_indices: Vec<usize>,
    ) -> Self {
        let mut lhs_to_rhs = vec![None; num_groups];
        let mut rhs_to_lhs = vec![None; num_groups];

        for (lhs, rhs) in mapping.iter() {
            lhs_to_rhs[lhs.group_index()] = Some(rhs.group_index());
            rhs_to_lhs[rhs.group_index()] = Some(lhs.group_index());
        }

        Self {
            mapping,
            lhs_to_rhs,
            rhs_to_lhs,
            input_indices,
            other_input_indices,
        }
    }

    /// Returns whether the cases have transitions that are equal under the bijective mapping.
    /// Assumes that the bijective mapping is bijective.
    /// That means you should make sure there is a 1-to-1 relation between cases.
    fn cases_equal(&self, cases: &CaseList, lhs_case_index: CaseIndex, rhs_case_index: CaseIndex) -> bool {
        let lhs_transitions = cases
            .relation_for_case(lhs_case_index, &self.other_input_indices)
            .transitions()
            .map(|case| {
                let sliced = self
                    .other_input_indices
                    .iter()
                    .map(|&index| case.inputs()[index].as_value())
                    .collect::<Vec<_>>();
                (sliced, case.groups())
            })
            .collect::<HashMap<_, _>>();
        let mut rhs_transitions = cases
            .relation_for_case(rhs_case_index, &self.other_input_indices)
            .transitions()
            .map(|case| {
                let sliced = self
                    .other_input_indices
                    .iter()
                    .map(|&index| case.inputs()[index].as_value())
                    .collect::<Vec<_>>();
                (sliced, case.groups())
            })
            .collect::<HashMap<_, _>>();

        for (lhs_slice, lhs_groups) in lhs_transitions.iter() {
            if let Some(rhs_groups) = rhs_transitions.remove(lhs_slice) {
                if rhs_groups.iter().any(|&rhs_group| {
                    self.rhs_to_lhs[rhs_group]
                        .map(|expected_lhs_group| !lhs_groups.contains(&expected_lhs_group))
                        .unwrap_or(false)
                }) {
                    return false;
                }
            }
        }

        for (rhs_slice, rhs_groups) in rhs_transitions.iter() {
            if let Some(&lhs_groups) = lhs_transitions.get(rhs_slice) {
                if lhs_groups.iter().any(|&lhs_group| {
                    self.lhs_to_rhs[lhs_group]
                        .map(|expected_rhs_group| !rhs_groups.contains(&expected_rhs_group))
                        .unwrap_or(false)
                }) {
                    return false;
                }
            }
        }

        true
    }

    fn groups_equal(&self, cases: &CaseList, lhs: &GroupRef, rhs: &GroupRef) -> bool {
        let mut rhs_seen = GrowingBitmap::new();
        for lhs_case_index in lhs.case_indices() {
            if let Some(rhs_case_index) = cases
                .relation_for_case(lhs_case_index, &self.input_indices)
                .transition_indices()
                .next()
            {
                rhs_seen.set(rhs_case_index.as_usize());

                if !self.cases_equal(cases, lhs_case_index, rhs_case_index) {
                    return false
                }
            }
        }

        let unseen_rhs_case_indices = rhs.case_indices().filter(|index| !rhs_seen[index.as_usize()]);
        for rhs_case_index in unseen_rhs_case_indices {
            if let Some(lhs_case_index) = cases
                .relation_for_case(rhs_case_index, &self.input_indices)
                .transition_indices()
                .next()
            {
                if !self.cases_equal(cases, lhs_case_index, rhs_case_index) {
                    return false
                }
            }
        }

        true
    }

    pub fn transitions_equal(&self, cases: &CaseList) -> bool {
        for (lhs, rhs) in self.mapping.iter() {
            if !self.groups_equal(cases, lhs, rhs) {
                return false
            }
        }

        true
    }
}

#[derive(Debug)]
pub struct ResolveGroup {
    /// The groups that we will use as a base for the remaining operations to synthesize.
    pub base_indices: Vec<usize>,

    /// The group indices that we need to resolve first.
    pub groups_to_resolve: Vec<usize>,
}

#[derive(Debug)]
pub struct Isomorphism {
    /// The input group index we're using as a bijective map between subgraphs.
    input_group_index: usize,

    other_input_groups: Vec<usize>,

    /// The group indices that could be joined.
    joined_group_indices: Vec<Vec<usize>>,

    /// In order to join the groups as described in `joined_group_indices`,
    /// the following groups need to have been matched already.
    groups_to_resolve: Vec<ResolveGroup>,
}

impl Isomorphism {
    fn join_overlapping(groups: &mut Vec<Vec<usize>>) {
        let mut index = 0;
        while index < groups.len() {
            let mut new = true;
            while new {
                new = false;
                for other_index in (index + 1..groups.len()).rev() {
                    if groups[other_index].iter().any(|n| groups[index].contains(n)) {
                        let group = groups.remove(other_index);
                        for v in group {
                            if !groups[index].contains(&v) {
                                groups[index].push(v);
                            }
                        }

                        new = true;
                    }
                }
            }

            index += 1;
        }
    }

    pub fn all_of(cases: &CaseList) -> Vec<Self> {
        if cases.input_groups().count() <= 1 {
            return Vec::new()
        }

        let mut isomorphisms = Vec::new();
        for (input_group_index, input_group) in cases.input_groups().enumerate() {
            info!("Determining isomorphisms using input group #{input_group_index}: {input_group:?} as bijection");

            let spliced = Spliced::by(cases, input_group_index);
            info!("Spliced: {spliced:?}");

            let bijective_groups = spliced.bijective_groups(cases);
            info!("Bijective groups: {bijective_groups:?}");

            for bijective_group in bijective_groups.into_iter() {
                let mut joined_group_indices = bijective_group
                    .iter()
                    .flat_map(|map| {
                        map.rhs_to_lhs
                            .iter()
                            .enumerate()
                            .flat_map(|(a, b)| b.map(|b| (a, b)))
                            .map(|(a, b)| vec![a, b])
                    })
                    .collect::<Vec<_>>();

                joined_group_indices.sort();
                joined_group_indices.dedup();

                Self::join_overlapping(&mut joined_group_indices);

                let group_slices = {
                    let mut v = bijective_group
                        .iter()
                        .flat_map(|group| {
                            [
                                group.lhs_to_rhs.iter().flatten().copied().collect::<Vec<_>>(),
                                group.rhs_to_lhs.iter().flatten().copied().collect::<Vec<_>>(),
                            ]
                        })
                        .collect::<Vec<_>>();

                    v.sort();
                    v.dedup();

                    v
                };

                let groups_to_resolve = group_slices
                    .iter()
                    .map(|slice| ResolveGroup {
                        base_indices: slice.clone(),
                        groups_to_resolve: slice
                            .iter()
                            .flat_map(|&group_index| {
                                let expected_result = cases.group(group_index).result();
                                joined_group_indices
                                    .iter()
                                    .find(|indices| indices.contains(&group_index))
                                    .unwrap()
                                    .iter()
                                    .copied()
                                    .filter(move |&other_group_index| {
                                        !cases.group(other_group_index).result().overlaps(expected_result)
                                    })
                            })
                            .collect::<Vec<_>>(),
                    })
                    .collect::<Vec<_>>();

                isomorphisms.push(Isomorphism {
                    input_group_index,
                    other_input_groups: cases
                        .input_groups()
                        .enumerate()
                        .filter(|&(index, _)| index != input_group_index)
                        .map(|(index, _)| index)
                        .collect(),
                    joined_group_indices,
                    groups_to_resolve,
                });
            }
        }

        info!("Isomorphisms: {isomorphisms:?}");

        isomorphisms
    }

    pub fn input_group_index(&self) -> usize {
        self.input_group_index
    }

    pub fn other_input_groups(&self) -> &[usize] {
        &self.other_input_groups
    }

    pub fn joined_group_indices(&self) -> &[Vec<usize>] {
        &self.joined_group_indices
    }

    pub fn groups_to_resolve(&self) -> &[ResolveGroup] {
        &self.groups_to_resolve
    }

    pub fn is_applicable(&self, expanded_groups: &[Vec<usize>], cases: &CaseList) -> bool {
        for group_indices in self.joined_group_indices.iter() {
            if let Some(result) = group_indices
                .iter()
                .flat_map(|&group_index| expanded_groups[group_index].iter())
                .map(|&group_index| cases.group(group_index).result())
                .reduce(|mut a, b| {
                    a.restrict_to(b);
                    a
                })
            {
                if result.is_empty() {
                    return false
                }
            } else {
                return false;
            }
        }

        true
    }
}
