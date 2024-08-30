use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::mem::swap;

use log::{debug, info, trace};
use rand::seq::SliceRandom;
use rand::Rng;

use crate::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64, GrowingBitmap};
use crate::utils::mcs::Decision;

#[derive(Clone, Debug)]
struct Entry<M> {
    map: M,
    path: Vec<u32>,
}

impl<M> Entry<M> {
    fn new(map: M) -> Entry<M> {
        Entry {
            map,
            path: Default::default(),
        }
    }
}

struct Choice {
    original_index: usize,
    elimination_map: GrowingBitmap,
}

pub struct Bfs<'a> {
    decisions: &'a [Decision],
    num_choices: usize,
    choice_elimination_maps: Vec<Choice>,
}

trait EliminationMap: Hash + Eq + Clone + BitmapSlice {
    fn from_bitmap(bitmap: &GrowingBitmap) -> Self;

    fn new() -> Self;
    fn and_with(&mut self, bitmap: &impl BitmapSlice) -> bool;
    fn is_superset_of(&self, other: &Self) -> bool;
}

impl EliminationMap for GrowingBitmap {
    fn from_bitmap(bitmap: &GrowingBitmap) -> Self {
        bitmap.clone()
    }

    fn new() -> Self {
        GrowingBitmap::new()
    }

    fn and_with(&mut self, bitmap: &impl BitmapSlice) -> bool {
        self.and_with(bitmap)
    }

    fn is_superset_of(&self, other: &Self) -> bool {
        self.is_superset_of(other)
    }
}

impl<const N: usize> EliminationMap for FixedBitmapU64<N> {
    fn from_bitmap(bitmap: &GrowingBitmap) -> Self {
        FixedBitmapU64::try_from(bitmap).unwrap()
    }

    fn new() -> Self {
        FixedBitmapU64::default()
    }

    fn and_with(&mut self, other: &impl BitmapSlice) -> bool {
        Bitmap::and_with(self, other)
    }

    fn is_superset_of(&self, other: &Self) -> bool {
        Bitmap::is_superset_of(self, other)
    }
}

impl<'a> Bfs<'a> {
    pub fn new(decisions: &'a [Decision], num_choices: usize) -> Self {
        let mut seen = HashSet::new();
        let choice_elimination_maps = (0..num_choices)
            .map(|choice| Choice {
                original_index: choice,
                elimination_map: decisions.iter().map(|d| !d.contains(choice)).collect::<GrowingBitmap>(),
            })
            .filter(|choice|
                // If we've already seen a choice that eliminated strictly more than this choice, we can skip this one.
                !seen.iter().any(|seen| choice.elimination_map.is_superset_of(seen))
                // If we've already seen this exact configuration, we can skip it
                && seen.insert(choice.elimination_map.clone()))
            .collect::<Vec<_>>();

        for (index, choice) in choice_elimination_maps.iter().enumerate() {
            debug!(
                " - Choice #{index} (original={}): {:?}",
                choice.original_index, choice.elimination_map
            );
        }

        Self {
            decisions,
            num_choices,
            choice_elimination_maps,
        }
    }

    fn find_random_solution(&self, rng: &mut impl Rng, path: &mut Vec<u32>, choice_elimination_maps: &[GrowingBitmap]) {
        let mut map = GrowingBitmap::new_all_ones(self.decisions.len());

        path.clear();

        for (decision_index, decision) in self.decisions.iter().enumerate() {
            if map[decision_index] {
                // Find the choice that eliminates the most decisions
                let choice_index = *decision.nums.choose(rng).unwrap();
                map.and_with(&choice_elimination_maps[choice_index]);
                path.push(choice_index as u32);
            }
        }
    }

    fn find_best_random_solution(&self, num_tries: usize) -> Vec<u32> {
        let choice_elimination_maps = (0..self.num_choices)
            .map(|choice| self.decisions.iter().map(|d| !d.contains(choice)).collect::<GrowingBitmap>())
            .collect::<Vec<_>>();

        // TODO: Allow an RNG to be passed in. (and preferrably pass in xoshiro256)
        let mut rng = rand::thread_rng();

        let mut best = Vec::new();
        self.find_random_solution(&mut rng, &mut best, &choice_elimination_maps);
        debug!("First random solution : {best:?}");

        let mut path = Vec::new();
        for _ in 0..num_tries {
            self.find_random_solution(&mut rng, &mut path, &choice_elimination_maps);

            if path.len() < best.len() {
                debug!("Better random solution: {path:?}");
                best.clone_from(&path);
            }
        }

        best
    }

    fn choice_would_violate<K: EliminationMap + Debug>(
        _path: &[u32], _new_candidate: usize, _choice_elimination_maps: &[K],
    ) -> bool {
        // TODO: This doesn't do anything as long as we're also checking against the explored map.
        // let mut prev_cover = K::new();
        // let candidate_cover = &choice_elimination_maps[new_candidate];

        // for &item in path.iter() {
        //     let new_cover = choice_elimination_maps[item as usize].cleared_from(&prev_cover);
        //     if new_cover.is_subset_of(candidate_cover) {
        //         info!("Do not take {new_candidate} after {:?}, because {item} will no longer have a critical hyperedge. new_cover={:?}, candidate_cover={candidate_cover:?}, prev_cover={prev_cover:?}", path, GrowingBitmap::from_slice(&new_cover));
        //         return true
        //     }

        //     prev_cover.or_with(&choice_elimination_maps[item as usize].flipped());
        // }

        false
    }

    fn run_single_decision<K: EliminationMap + Debug>(
        &self, choice_elimination_maps: &[K], availability_constraints: &[K], frontier: &mut Vec<Entry<K>>,
        explored: &mut HashSet<K>, next_frontier: &mut Vec<Entry<K>>,
    ) -> Option<Vec<u32>> {
        trace!("Frontier: {frontier:#?}");

        let mut num_suboptimal_skipped = 0;

        let mut new_map = K::new();
        let mut tmp = K::new();
        for entry in frontier.iter() {
            let mut any = false;
            let start_index = entry.path.last().map(|&x| x + 1).unwrap_or(0);
            // TODO: Determine end_index. There's no point in picking the last entry if that doesn't result in a solution...
            for (choice_index, (elimination_map, availability_constraint)) in choice_elimination_maps
                .iter()
                .zip(availability_constraints.iter())
                .enumerate()
                .skip(start_index as usize)
            {
                if !entry.map.anded_with(availability_constraint).is_all_zeros() {
                    break
                }

                if !elimination_map.is_superset_of(&entry.map) {
                    new_map.clone_from(&entry.map);
                    new_map.and_with(elimination_map);

                    trace!("New map: {new_map:?} (path={:?} + {choice_index})", entry.path);
                    if let Some(index) = choice_elimination_maps.iter().take(choice_index).position(|elimination_map| {
                        let other = entry.map.anded_with(elimination_map);

                        // info!("Other: {:?}", GrowingBitmap::from_slice(&other));

                        other.is_subset_of(&new_map)
                    }) {
                        debug!(
                            "Choice {0:?} + {choice_index} is suboptimal, because {0:?} + {choice_index} is a subset of {0:?} + {index}",
                            entry.path
                        );
                        num_suboptimal_skipped += 1;
                    } else if !explored.contains(&new_map)
                        && !Self::choice_would_violate(&entry.path, choice_index, choice_elimination_maps)
                    {
                        // TODO: This eliminates more cases, but is too expensive to run...
                        let is_suboptimal = choice_elimination_maps.iter().enumerate().take(choice_index).find(
                            |(choice_index, elimination_map)| {
                                tmp.clone_from(&new_map);
                                tmp.and_with(*elimination_map);

                                explored.contains(&tmp) && !entry.path.contains(&(*choice_index as u32))
                            },
                        );

                        if let Some((suboptimal_index, _)) = is_suboptimal {
                            debug!(
                                "Choice {0:?} + {choice_index} is suboptimal, because {0:?} + {choice_index} + {suboptimal_index} already exists",
                                entry.path
                            );
                            num_suboptimal_skipped += 1;
                        } else {
                            explored.insert(new_map.clone());

                            let entry = Entry {
                                map: new_map.clone(),
                                path: {
                                    let mut p = entry.path.clone();
                                    p.push(choice_index as u32);
                                    p
                                },
                            };

                            if new_map.is_all_zeros() {
                                return Some(entry.path)
                            } else {
                                next_frontier.push(entry);
                                any = true;
                            }
                        }
                    } else {
                        trace!(
                            "Skipping {:?} + {choice_index}, because it doesn't provide any new states",
                            entry.path
                        )
                    }
                }
            }

            if !any {
                trace!("Entry {entry:?} died, because it could not yield any good states")
            }
        }

        info!("Wanted to skip {num_suboptimal_skipped} this round");

        debug!("Next frontier size: {}", explored.len());
        None
    }

    fn run_decisions<K: EliminationMap + Debug>(&mut self, max: usize) -> Option<Vec<u32>> {
        let start_map = GrowingBitmap::new_all_ones(self.decisions.len());
        let mut frontier = vec![Entry::new(K::from_bitmap(&start_map))];
        let mut explored = HashSet::new();

        let choice_elimination_maps = self
            .choice_elimination_maps
            .iter()
            .map(|m| K::from_bitmap(&m.elimination_map))
            .collect::<Vec<_>>();

        let mut availability_constraints = Vec::new();
        let mut result = K::from_bitmap(&start_map);
        for map in choice_elimination_maps.iter().rev() {
            result.and_with(map);
            availability_constraints.push(result.clone());
        }

        availability_constraints.reverse();
        info!("Availability constraints: {availability_constraints:#?}");

        for size in 0..max {
            debug!("Running iteration for size={size}");

            let mut next_frontier = Vec::new();
            if let Some(result) = self.run_single_decision(
                &choice_elimination_maps,
                &availability_constraints,
                &mut frontier,
                &mut explored,
                &mut next_frontier,
            ) {
                return Some(result)
            }

            swap(&mut frontier, &mut next_frontier);
        }

        None
    }

    // TODO: Generic parameters for choice size C (u16/u32)
    // TODO: Generic parameters for path P (ArrayVec<C, N> if N <= 8, Vec<C>)
    fn run_internal(&mut self, max: usize) -> Vec<usize> {
        // General purpose loop that can handle > 56 remaining decisions

        let result = match (self.decisions.len() + 63) / 64 {
            1 => self.run_decisions::<FixedBitmapU64<1>>(max),
            2 => self.run_decisions::<FixedBitmapU64<2>>(max),
            3 => self.run_decisions::<FixedBitmapU64<3>>(max),
            4 => self.run_decisions::<FixedBitmapU64<4>>(max),
            _ => self.run_decisions::<GrowingBitmap>(max),
        };

        // We start by using GrowingBitmap for > 56 remaining decisions
        result
            .unwrap()
            .into_iter()
            .map(|n| self.choice_elimination_maps[n as usize].original_index)
            .collect()
    }

    pub fn run(&mut self) -> Vec<usize> {
        debug!("Running BFS...");

        let random_solution = self.find_best_random_solution(10_000);
        debug!("Best random solution: {random_solution:?}");
        debug!("Best random solution is {} items", random_solution.len());

        let max = random_solution.len();
        self.run_internal(max)
    }
}
