use std::collections::VecDeque;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use arrayvec::ArrayVec;
use itertools::Itertools;
use liblisa::arch::{Arch, CpuState};
use liblisa::oracle::{MappableArea, Oracle};
use liblisa::state::jit::{ComplexJitState, MaybeJitState, SimpleJitState};
use liblisa::state::random::{randomized_bytes_into_arrayvec, randomized_bytes_select_nth, randomized_value, StateGen};
use liblisa::state::{AsSystemState, StateByte, SystemState, SystemStateByteView};
use liblisa::value::MutValue;
use log::{debug, error, info, trace};
use rand::seq::SliceRandom;
use rand::Rng;

use super::flow::Dataflow;
use super::results::{AnalysisResult, IgnorableDifferences};
use super::spec::ButEntry;
use super::DataflowAnalysisError;
use crate::dataflow::fuzz::Fuzz;
use crate::dataflow::results::compute_changed;
use crate::dataflow::spec::{Equivalence, EquivalenceSpec};

pub struct FlowAnalyzer3<'a, A: Arch, M: MappableArea> {
    state_gen: StateGen<'a, A, M>,
    view: SystemStateByteView<'a, A>,
    results: AnalysisResult<'a, A, M>,
    oid_gen: ObservationIdGenerator,
    interesting_states: Vec<Rc<Base<'a, A>>>,
}

pub struct Dataflows<A: Arch> {
    pub dataflows: Vec<Dataflow<A::Reg>>,
    pub found_dependent_bytes: bool,
}

#[derive(Debug, Clone)]
pub struct Goal<A: Arch> {
    pub(crate) bytes: Vec<StateByte>,
    pub(crate) ignorable_differences: IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask>,
    pub(crate) needs_adapt: bool,
    pub(crate) num_observed: usize,
    pub(crate) num_failed: usize,
    pub(crate) spec: EquivalenceSpec<A>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ModificationEquality {
    Equal,
    Unequal,
    BytewiseUnequal,
}

impl<A: Arch> Goal<A> {
    pub fn new(view: SystemStateByteView<A>, bytes: Vec<StateByte>, needs_adapt: bool) -> Goal<A> {
        Self {
            num_observed: 0,
            num_failed: 0,
            needs_adapt,
            ignorable_differences: IgnorableDifferences::default(),
            spec: EquivalenceSpec::from_neqs(view, bytes.iter().copied()),
            bytes,
        }
    }

    fn is_single_byte(&self) -> bool {
        self.bytes.len() == 1
    }

    fn spec(&self) -> &EquivalenceSpec<A> {
        &self.spec
    }

    fn modify_state(&self, view: SystemStateByteView<A>, state: &mut SystemState<A>, value: u8) {
        for byte in self.bytes.iter() {
            view.set(state, *byte, value);
        }
    }

    fn modifications_are_fully_unequal(
        &self, view: SystemStateByteView<A>, from: &SystemState<A>, to: &SystemState<A>,
    ) -> ModificationEquality {
        let mut any = false;
        let mut all = true;
        for &b in self.bytes.iter() {
            if view.bytes_unequal(b, from, to) {
                any = true;
            } else {
                all = false;
            }
        }

        if all {
            ModificationEquality::BytewiseUnequal
        } else if any {
            ModificationEquality::Unequal
        } else {
            ModificationEquality::Equal
        }
    }
}

#[derive(Debug, Clone)]
pub struct Base<'j, A: Arch> {
    pub from: MaybeJitState<'j, A>,
    pub to: SystemState<A>,
    // pub destinations: Vec<StateByte>,
}

pub fn modify_state_with_spec<A: Arch, R: Rng>(
    rng: &mut R, view: SystemStateByteView<A>, state: &mut SystemState<A>, spec: &EquivalenceSpec<A>,
) {
    match spec {
        EquivalenceSpec::AllEqBut(spec) => {
            for ButEntry {
                reg,
                full_mask,
                bytes,
            } in spec.but()
            {
                view.modify_reg(state, reg, |value| match value {
                    MutValue::Num(orig) => {
                        let mut new_val = *orig;
                        if let Some(mask) = reg.mask() {
                            let alt_val: u64 = rng.gen();
                            for &byte in bytes {
                                assert!(byte < 8);
                                let mask = (0xFF << (byte * 8)) & mask;

                                if mask == 0 {
                                    panic!("The mask for byte {byte} of register {reg:?} contains no bits");
                                }

                                let new = {
                                    let base = *orig & mask;
                                    let mut new_byte = alt_val & mask;
                                    while new_byte == base {
                                        new_byte = rng.gen::<u64>() & mask;
                                    }

                                    new_byte
                                };

                                new_val = (new_val & !mask) | new;
                            }
                        } else {
                            let mut remaining_mask = *full_mask;
                            while remaining_mask != 0 {
                                let x = randomized_value(rng);

                                // "Compare" with xor
                                let cmp = *orig ^ x;

                                // Collect comparison result in lowest bit of each byte
                                let cmp = cmp | (cmp >> 4);
                                let cmp = cmp | (cmp >> 2);
                                let cmp = cmp | (cmp >> 1);

                                // Mask out the other bits
                                let cmp = cmp & 0x0101_0101_0101_0101;

                                // Expand the comparison such that all bits are either set or unset
                                let fulfilled_mask = cmp * 0xff;

                                // Apply the new values
                                if fulfilled_mask > 0 {
                                    new_val = (x & remaining_mask) | (new_val & !remaining_mask);
                                    remaining_mask &= !fulfilled_mask;
                                }
                            }
                        };

                        *orig = new_val;
                    },
                    MutValue::Bytes(bytedata) => {
                        if bytes.len() > 1 {
                            // if bytedata.len() % 8 == 0 {
                            //     const MAX_STACK_LEN: usize = 128;
                            //     let mut alt_val = [0u8; MAX_STACK_LEN];
                            //     let mut remaining_mask = [0u64; MAX_STACK_LEN / 8];
                            //     for &byte in bytes {
                            //         remaining_mask[byte / 8] |= 0xff << ((byte % 8) * 8);
                            //     }

                            //     let size = bytedata.len() / 8;

                            //     while remaining_mask.iter().take(size).any(|m| *m != 0) {
                            //         // Try to avoid allocation for small buffers
                            //         randomized_bytes_into_buffer(rng, &mut alt_val[0..bytedata.len()]);

                            //         for (index, remaining_mask) in remaining_mask.iter_mut().enumerate().take(size) {
                            //             let orig = u64::from_be_bytes(bytedata[index * 8..(index + 1) * 8].try_into().unwrap());
                            //             let x = u64::from_be_bytes(alt_val[index * 8..(index + 1) * 8].try_into().unwrap());

                            //             // "Compare" with xor
                            //             let cmp = orig ^ x;

                            //             // Collect comparison result in lowest bit of each byte
                            //             let cmp = cmp | (cmp >> 4);
                            //             let cmp = cmp | (cmp >> 2);
                            //             let cmp = cmp | (cmp >> 1);

                            //             // Mask out the other bits
                            //             let cmp = cmp & 0x01010101_01010101;

                            //             // Expand the comparison such that all bits are either set or unset
                            //             let fulfilled_mask = cmp * 0xff;

                            //             // Apply the new values
                            //             if fulfilled_mask > 0 {
                            //                 let new_val = (x & *remaining_mask) | (orig & !*remaining_mask);
                            //                 bytedata[index * 8..(index + 1) * 8].copy_from_slice(&new_val.to_be_bytes());

                            //                 *remaining_mask &= !fulfilled_mask;
                            //             }
                            //         }
                            //     }
                            // } else {
                            let mut alt_val = ArrayVec::<_, 4096>::new();
                            randomized_bytes_into_arrayvec(rng, &mut alt_val, bytedata.len());
                            let alt_val = alt_val.as_mut_slice();

                            for &byte in bytes {
                                bytedata[byte] = {
                                    let base = bytedata[byte];
                                    let mut val = alt_val[byte];
                                    while val == base {
                                        val = randomized_bytes_select_nth(rng, byte);
                                    }

                                    val
                                };
                            }
                            // }
                        } else {
                            let byte = bytes[0];
                            let base = bytedata[byte];
                            bytedata[byte] = loop {
                                let val = randomized_bytes_select_nth(rng, byte);
                                if val != base {
                                    break val
                                }
                            };
                        }
                    },
                });
            }
        },
    }
}

pub fn modify_state_with_spec_possibly_eq<A: Arch, R: Rng>(
    rng: &mut R, view: SystemStateByteView<A>, state: &mut SystemState<A>, spec: &EquivalenceSpec<A>,
) {
    match spec {
        EquivalenceSpec::AllEqBut(spec) => {
            for ButEntry {
                reg,
                full_mask,
                bytes,
            } in spec.but()
            {
                view.modify_reg(state, reg, |value| match value {
                    MutValue::Num(orig) => {
                        let reg_mask = reg.mask().unwrap_or(u64::MAX);
                        debug_assert_eq!(*orig & !reg_mask, 0);
                        let mask = full_mask & reg_mask;
                        let new_val = if reg.mask().is_some() {
                            rng.gen()
                        } else {
                            randomized_value(rng)
                        };

                        *orig = (new_val & mask) | (*orig & !mask);
                    },
                    MutValue::Bytes(bytedata) => {
                        if bytes.len() > 1 {
                            let mut alt_val = ArrayVec::<_, 4096>::new();
                            randomized_bytes_into_arrayvec(rng, &mut alt_val, bytedata.len());
                            let alt_val = alt_val.as_mut_slice();

                            for &byte in bytes {
                                bytedata[byte] = alt_val[byte];
                            }
                        } else {
                            let byte = bytes[0];
                            let base = bytedata[byte];
                            bytedata[byte] = loop {
                                let val = randomized_bytes_select_nth(rng, byte);
                                if val != base {
                                    break val
                                }
                            };
                        }
                    },
                });
            }
        },
    }
}

#[derive(Debug, Clone)]
pub struct InterestingPair<'j, A: Arch> {
    pub(crate) goal_index: Option<usize>,
    pub(crate) a: Rc<Base<'j, A>>,
    pub(crate) b: Rc<Base<'j, A>>,
}

struct BaseWithGoal<'j, A: Arch> {
    goal: GoalIndex,
    base: Rc<Base<'j, A>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct GoalIndex(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ObservationId(u32);

#[derive(Clone)]
struct ObservationIdGenerator(Rc<AtomicU32>);

impl ObservationIdGenerator {
    fn new() -> ObservationIdGenerator {
        Self(Rc::new(AtomicU32::new(0)))
    }

    fn create_observation_id(&mut self) -> ObservationId {
        ObservationId(self.0.fetch_add(1, Ordering::SeqCst))
    }
}

struct InputEntry<'j, A: Arch> {
    observation_id: ObservationId,
    state_in: MaybeJitState<'j, A>,
    original: BaseWithGoal<'j, A>,
    compare_with_stored: Option<(ObservationId, GoalIndex)>,
    generated_from_enumeration: bool,
    store: bool,
}

impl<'j, A: Arch> AsSystemState<A> for InputEntry<'j, A> {
    type Output<'a>
        = <MaybeJitState<'j, A> as AsSystemState<A>>::Output<'a>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        self.state_in.as_system_state()
    }

    fn num_memory_mappings(&self) -> usize {
        self.state_in.num_memory_mappings()
    }
}

impl<'a, A: Arch, M: MappableArea> FlowAnalyzer3<'a, A, M> {
    pub fn new(state_gen: StateGen<'a, A, M>, view: SystemStateByteView<'a, A>) -> FlowAnalyzer3<'a, A, M> {
        FlowAnalyzer3 {
            state_gen,
            view,
            results: AnalysisResult::new(view),
            oid_gen: ObservationIdGenerator::new(),
            interesting_states: Vec::new(),
        }
    }

    fn check_enumerated_values<'q, R: Rng>(
        &mut self, rng: &mut R, goal_index: usize, goal: &mut Goal<A>, base: Rc<Base<'q, A>>,
        queue: &mut VecDeque<InputEntry<'q, A>>,
    ) where
        'a: 'q,
    {
        info!("Enumerating all values for {:?}", goal);
        let system_state = base.from.as_system_state();
        let from = system_state.as_ref();
        let base_value = self.view.get(from, goal.bytes[0]);
        let mut oid_gen = self.oid_gen.clone();

        let mask = if goal.is_single_byte() {
            let (reg, index) = self.view.as_reg(goal.bytes[0]);
            if let Some(mask) = reg.mask() {
                (mask >> (index * 8)) as u8
            } else {
                0xff
            }
        } else {
            0xff
        };

        // let t = Instant::now();
        queue.extend(
            SimpleJitState::build(
                &goal.bytes,
                &self.state_gen,
                self.view,
                from,
                |index, state| {
                    let n = index as u8;

                    // Skip all possibilities not matching the mask
                    if n & !mask != 0 {
                        return false;
                    }

                    trace!("{goal:?} = {n:02X}");
                    if goal.is_single_byte() {
                        if base_value == n {
                            // The state we will generate here will be identical to `base.from`
                            return false;
                        }

                        goal.modify_state(self.view, state, n);
                    } else {
                        let spec = goal.spec();
                        modify_state_with_spec_possibly_eq(rng, self.view, state, spec)
                    }

                    true
                },
                256,
            )
            .map(|item| InputEntry {
                observation_id: oid_gen.create_observation_id(),
                state_in: MaybeJitState::SimpleJit(item),
                original: BaseWithGoal {
                    base: Rc::clone(&base),
                    goal: GoalIndex(goal_index),
                },
                compare_with_stored: None,
                generated_from_enumeration: true,
                store: false,
            }),
        );
        // self.enum_time += t.elapsed();
    }

    fn expand_from_interesting_state<'q, R: Rng>(
        &mut self, interesting: &InterestingPair<'q, A>, rng: &mut R, goals: &mut [Goal<A>],
        queue: &mut VecDeque<InputEntry<'q, A>>,
    ) where
        'a: 'q,
    {
        // TODO: Can we prune the amount of states we generate here? We end up queueing a lot of practically identical cases here, for example for 490FC78C520080C000.

        info!("Expanding from interesting state (queue length={})...", queue.len());
        let view = self.view;
        let mut oid_gen = self.oid_gen.clone();
        let a_from_builder = ComplexJitState::build(
            interesting.a.from.as_system_state().as_ref().clone(),
            &self.state_gen,
            self.view,
        );
        let b_from_builder = ComplexJitState::build(
            interesting.b.from.as_system_state().as_ref().clone(),
            &self.state_gen,
            self.view,
        );
        // let t = Instant::now();
        'next_goal: for (goal_index, goal) in goals.iter().enumerate() {
            // We have a pair of states (a, b) that differ by some unknown amount of bytes.
            // There is at least one state byte S that is different after execution of a and b (proving some dataflow).
            // Here we construct a' and b' which differ in one state byte B from a and b, respectively.
            // We will then compare pairs (a, a'), (b, b') and (a', b'), to see if any state bytes in the output differ.
            // In particular, we will also check if state byte S still differs after execution of a' and b'.
            // If it doesn't, the observation of the dataflow is dependent on keeping state byte B identical.

            let mut n = 0;
            let modified_b_in = {
                let a_from = interesting.a.from.as_system_state();
                let a_from = a_from.as_ref();
                loop {
                    if let Some(state) = b_from_builder.create(&goal.bytes, |state| {
                        let spec = goal.spec();
                        modify_state_with_spec_possibly_eq(rng, view, state, spec);

                        trace!(
                            "Goal {goal_index:?} -> {}",
                            goal.bytes
                                .iter()
                                .map(|&b| format!("({b:?} / {:?}) = {:X?}", self.view.as_reg(b), self.view.get(state, b)))
                                .join(", ")
                        );

                        let equality = goal.modifications_are_fully_unequal(self.view, state, a_from);

                        (n > 5 && equality != ModificationEquality::Equal) || equality == ModificationEquality::BytewiseUnequal
                    }) {
                        break state;
                    }

                    n += 1;
                    if n > 30 {
                        continue 'next_goal;
                    }
                }
            };

            let modified_a_in = {
                let b_from = modified_b_in.as_system_state();
                let from = b_from.as_ref();
                let new_values = goal.bytes.iter().map(|&b| view.get(from, b));
                a_from_builder.create_with_change_list(&goal.bytes, new_values)
            };

            let observation_id = oid_gen.create_observation_id();
            queue.push_back(InputEntry {
                observation_id,
                state_in: modified_b_in.into(),
                original: BaseWithGoal {
                    base: Rc::clone(&interesting.b),
                    goal: GoalIndex(goal_index),
                },
                compare_with_stored: None,
                store: modified_a_in.is_some(),
                generated_from_enumeration: false,
            });

            if let Some(modified_a_in) = modified_a_in {
                queue.push_back(InputEntry {
                    observation_id: oid_gen.create_observation_id(),
                    state_in: modified_a_in.into(),
                    original: BaseWithGoal {
                        base: Rc::clone(&interesting.a),
                        goal: GoalIndex(goal_index),
                    },
                    compare_with_stored: interesting.goal_index.map(|n| (observation_id, GoalIndex(n))),
                    store: false,
                    generated_from_enumeration: false,
                });
            }
        }

        // self.expand_time += t.elapsed();

        info!("queue length = {}", queue.len());
    }

    #[allow(clippy::too_many_arguments)]
    fn check_states(
        &mut self, goals: &mut [Goal<A>], goal_index: usize, base: Rc<Base<'a, A>>, modified_in: &MaybeJitState<'a, A>,
        modified_out: &SystemState<A>, should_enumerate: bool, rng2: &mut impl Rng, queue: &mut VecDeque<InputEntry<'a, A>>,
    ) {
        let system_state = modified_in.as_system_state();
        let modified_in_state = system_state.as_ref();
        let goal = &mut goals[goal_index];
        let modified = goal
            .bytes
            .iter()
            .copied()
            .filter(|b| {
                self.view
                    .bytes_unequal(*b, base.from.as_system_state().as_ref(), modified_in_state)
            })
            .collect::<Vec<_>>();

        let tmp;
        let ignorable_differences = if modified.len() != goal.bytes.len() {
            tmp = self.results.compute_ignorable_differences(&modified);
            &tmp
        } else {
            &goal.ignorable_differences
        };

        // let t = Instant::now();
        let new_found = self.results.check_dataflows_with_ignorable_differences(
            goal,
            ignorable_differences,
            &base,
            (modified_in_state, modified_out),
        );
        // self.check_dataflow_time += t.elapsed();
        // self.num_dataflow_checks += 1;
        if new_found.any() {
            goal.ignorable_differences = self.results.compute_ignorable_differences(&goal.bytes);
            let modified = Rc::new(Base {
                // destinations: self.results.check_destinations(modified_in_state, modified_out),
                from: system_state.as_ref().clone().into(),
                to: modified_out.clone(),
            });

            if should_enumerate {
                self.check_enumerated_values(rng2, goal_index, goal, Rc::clone(&modified), queue);
            }

            let pair = InterestingPair {
                goal_index: Some(goal_index),
                a: Rc::clone(&base),
                b: Rc::clone(&modified),
            };

            self.interesting_states.push(Rc::clone(&base));
            self.interesting_states.push(Rc::clone(&modified));

            self.expand_from_interesting_state(&pair, rng2, goals, queue);
        }
    }

    fn can_generate_nonfaulting_state<O: Oracle<A>, R: Rng>(
        &mut self, rng: &mut R, oracle: &mut O, base: &SystemState<A>, spec: &EquivalenceSpec<A>,
    ) -> bool {
        let mut ok_checked = 0;

        for (modified_in, modified_out) in oracle.batch_observe_iter((0..50_000).flat_map(|_| {
            let mut modified_in = base.clone();
            modify_state_with_spec(rng, self.view, &mut modified_in, spec);

            let adapt_success = self.state_gen.adapt(&mut modified_in, false);

            #[cfg(debug_assertions)]
            if !spec.verify(self.view, base, &modified_in) {
                panic!("Spec was not upheld: {spec:#?} with base = {base:X?} and modified = {modified_in:X?}");
            }

            if adapt_success {
                Some(modified_in)
            } else {
                None
            }
        })) {
            if modified_out.is_ok() {
                trace!("Non-erroring state: {:?} modified to {:?}", base, modified_in);
                return true
            }

            ok_checked += 1;

            if ok_checked >= 5000 {
                break;
            }
        }

        debug!("Unable to generate nonfaulting state");

        false
    }

    fn find_dependent_bytes<O: Oracle<A>, R: Rng>(
        &mut self, rng: &mut R, oracle: &mut O, original_bytes: &[StateByte], base: &SystemState<A>,
    ) -> Result<Vec<StateByte>, DataflowAnalysisError<A>> {
        info!("Finding dependent bytes for {:?} in state: {:X?}", original_bytes, base);
        let mut dependent_bytes = original_bytes.to_vec();

        loop {
            let spec = EquivalenceSpec::from_neqs(self.view, dependent_bytes.iter().copied());
            if self.can_generate_nonfaulting_state(rng, oracle, base, &spec) {
                info!("Identified all dependent bytes: {:?}", dependent_bytes);
                break;
            }

            // TODO: Dependent bytes don't necessarily have to be a range; We need a Vec<StateByte> rather than a Range<StateByte>
            let mut frontier = VecDeque::new();
            let mut best_range = StateByte::new(0)..StateByte::new(self.view.size());

            info!("Checking range {:?}", best_range);
            let mid = StateByte::new((best_range.end.as_usize() - best_range.start.as_usize()) / 2 + best_range.start.as_usize());
            frontier.push_back(best_range.start..mid);
            frontier.push_back(mid..best_range.end);

            let mut new_dependent_bytes = Vec::new();
            while let Some(range) = frontier.pop_front() {
                let mut spec = EquivalenceSpec::build();
                for b in (0..self.view.size()).map(StateByte::new) {
                    if range.contains(&b) {
                        spec.insert(b, Equivalence::Neq);
                    } else {
                        spec.insert(b, Equivalence::Eq);
                    }
                }

                for byte in dependent_bytes.iter() {
                    spec.insert(*byte, Equivalence::Neq);
                }

                let spec = spec.finish(self.view);
                if self.can_generate_nonfaulting_state(rng, oracle, base, &spec) {
                    info!(
                        "Dependent byte must be somewhere in: {:?}; Spec gives modified states that don't error: {:?}",
                        range, spec
                    );
                    if range.start.as_usize() + 1 != range.end.as_usize() {
                        let mid = StateByte::new((range.start.as_usize() + range.end.as_usize()) / 2);
                        frontier.push_back(range.start..mid);
                        frontier.push_back(mid..range.end);
                    } else {
                        new_dependent_bytes.push(range.start);
                    }

                    if best_range.end.as_usize() - best_range.start.as_usize() > range.end.as_usize() - range.start.as_usize() {
                        best_range = range;
                    }
                } else {
                    info!("Eliminated: {:?}", range);
                }
            }

            if best_range == (StateByte::new(0)..StateByte::new(self.view.size())) {
                return Err(DataflowAnalysisError::NotAllBytesAreIndependentlyModifyable)
            }

            info!(
                "Identified dependent byte range: {:?} + bytes {:?}",
                best_range, new_dependent_bytes
            );
            dependent_bytes.append(&mut new_dependent_bytes);
            dependent_bytes.extend((best_range.start.as_usize()..best_range.end.as_usize()).map(StateByte::new));

            dependent_bytes.sort();
            dependent_bytes.dedup();

            for index in (0..dependent_bytes.len()).rev() {
                if original_bytes.contains(&dependent_bytes[index]) {
                    continue;
                }

                // TODO: We should have three options in this spec.
                let mut spec = EquivalenceSpec::build();
                for b in (0..self.view.size()).map(StateByte::new) {
                    spec.insert(b, Equivalence::Eq);
                }

                for byte in dependent_bytes.iter() {
                    spec.insert(*byte, Equivalence::Neq);
                }

                spec.insert(dependent_bytes[index], Equivalence::Eq);

                let spec = spec.finish(self.view);
                if self.can_generate_nonfaulting_state(rng, oracle, base, &spec) {
                    let byte = dependent_bytes.remove(index);
                    info!("Byte {:?} *is not* a dependent byte", byte);
                } else {
                    info!("Byte {:?} *is* a dependent byte", dependent_bytes[index]);
                }
            }
        }

        Ok(dependent_bytes)
    }

    fn has_single_change(&self, a: &SystemState<A>, b: &SystemState<A>) -> Option<StateByte> {
        let mut changed = None;
        let mut num_changed = 0usize;
        self.view.find_differences(a, b, &mut |b| {
            changed = Some(b);
            num_changed += 1;
        });

        if num_changed <= 1 {
            changed
        } else {
            None
        }
    }

    pub fn run<O: Oracle<A>>(
        &mut self, rng: &mut impl Rng, oracle: &mut O, likely_dependent: &[Vec<StateByte>],
    ) -> Result<Dataflows<A>, DataflowAnalysisError<A>> {
        // let start = Instant::now();

        let mut found_dependent_bytes = false;
        let mut goals = (0..self.view.size())
            .map(StateByte::new)
            .filter(|b| !likely_dependent.iter().flatten().contains(b))
            .map(|b| Goal::new(self.view, vec![b], self.state_gen.needs_adapt_from_bytes(&self.view, &[b])))
            .chain(likely_dependent.iter().map(|bytes| {
                Goal::new(
                    self.view,
                    bytes.clone(),
                    self.state_gen.needs_adapt_from_bytes(&self.view, bytes),
                )
            }))
            .collect::<Vec<_>>();

        info!("Goals: {:?}", goals);

        loop {
            let interesting = {
                // let t = Instant::now();
                let mut fuzzer = Fuzz::new(
                    &self.state_gen,
                    self.view,
                    &mut self.results,
                    &goals,
                    &self.interesting_states,
                );
                // fuzz_time += t.elapsed();

                fuzzer.fuzz(rng, oracle)?
            };

            if let Some(interesting) = interesting {
                let mut not_found = 0;
                loop {
                    let mut queue = VecDeque::new();

                    if not_found > 0
                        && let Some(minimal_interesting) = self.try_reduce_counterexample(rng, oracle, &interesting)
                    {
                        if let Some(b) = self.has_single_change(
                            minimal_interesting.a.from.as_system_state().as_ref(),
                            minimal_interesting.b.from.as_system_state().as_ref(),
                        ) {
                            let goal_index = goals.iter().position(|g| g.bytes.contains(&b)).unwrap();
                            debug!(
                                "Checking state with single change in {b:?}, contained in goal #{goal_index}: {:?}",
                                goals[goal_index]
                            );
                            self.check_states(
                                &mut goals,
                                goal_index,
                                Rc::clone(&minimal_interesting.a),
                                &minimal_interesting.b.from,
                                &minimal_interesting.b.to,
                                false,
                                rng,
                                &mut queue,
                            );
                        } else {
                            debug!("Multiple changes; Can't check state");
                        }

                        self.expand_from_interesting_state(&minimal_interesting, rng, &mut goals, &mut queue);
                    } else {
                        if let Some(b) = self.has_single_change(
                            interesting.a.from.as_system_state().as_ref(),
                            interesting.b.from.as_system_state().as_ref(),
                        ) {
                            let goal_index = goals.iter().position(|g| g.bytes.contains(&b)).unwrap();
                            debug!(
                                "Checking state with single change in {b:?}, contained in goal #{goal_index}: {:?}",
                                goals[goal_index]
                            );
                            self.check_states(
                                &mut goals,
                                goal_index,
                                Rc::clone(&interesting.a),
                                &interesting.b.from,
                                &interesting.b.to,
                                false,
                                rng,
                                &mut queue,
                            );
                        }

                        self.expand_from_interesting_state(&interesting, rng, &mut goals, &mut queue);
                    }

                    {
                        // TODO: More extensive double-checking of all interesting states
                        let double_check = oracle.batch_observe([&interesting.a.from, &interesting.b.from]);
                        if let [(_, Ok(out_a)), (_, Ok(out_b))] = double_check {
                            self.results
                                .check_unobservable_inputs(&interesting.a.from, &interesting.a.to, &out_a);
                            self.results
                                .check_unobservable_inputs(&interesting.b.from, &interesting.b.to, &out_b);
                        } else {
                            return Err(DataflowAnalysisError::Unreliable);
                        }
                    }

                    let mut stored_base: Option<(_, Rc<_>)> = None;
                    loop {
                        let mut check_dependent_bytes = Vec::new();
                        let mut new_queue = VecDeque::new();
                        // let mut obs_t = Instant::now();
                        for (entry, state_out) in oracle.batch_observe_iter(queue) {
                            // observe_time += obs_t.elapsed();
                            // num_observations += 1;
                            let original = &entry.original;
                            let generated_from_enumeration = entry.generated_from_enumeration;
                            let compare_with_stored = &entry.compare_with_stored;
                            let store = entry.store;
                            match state_out {
                                Ok(state_out) => {
                                    goals[original.goal.0].num_observed += 1;

                                    self.check_states(
                                        &mut goals,
                                        original.goal.0,
                                        original.base.clone(),
                                        &entry.state_in,
                                        &state_out,
                                        !generated_from_enumeration,
                                        rng,
                                        &mut new_queue,
                                    );

                                    if let Some((observation_id, goal_index)) = compare_with_stored {
                                        if let Some((stored_obs_id, stored_base)) = Option::take(&mut stored_base) {
                                            // Make sure we're comparing the right states.
                                            // If the observation that was supposed to store the base failed, this might contain the wrong stored base.
                                            if stored_obs_id == *observation_id {
                                                // let seed = &mut self.seeds[seed_id.0];

                                                // let original_goal_index = original.goal;

                                                // if &original_goal_index != goal_index {
                                                //     // False positive: we modified the byte that differed in the original observation;
                                                //     // If we make them identical in both cases, both states are identical as well.
                                                //     // Obviously we won't be able to infer any dataflows from identical states.
                                                //     // With the check above we made sure this is not the case.

                                                //     for index in (0..seed.fuzz_constraints.len()).rev() {
                                                //         let c = &mut seed.fuzz_constraints[index];
                                                //         if let Some(new) = c.new_found.check_and_split(self.view, &*stored_base, (entry.state_in.as_system_state().as_ref(), &state_out)) {
                                                //             debug!("{seed_id:?} needs to keep bytes {:?} identical", goals[original_goal_index.0].bytes);
                                                //             trace!("Because {:?} is proven, but {:?} is not proven from: {:?} {:?}", c.new_found, new, &*stored_base, (entry.state_in.as_system_state().as_ref(), &state_out));

                                                //             let new = FuzzConstraint {
                                                //                 new_found: new,
                                                //                 keep_bytes_identical: c.keep_bytes_identical.iter()
                                                //                     .chain(&goals[original_goal_index.0].bytes)
                                                //                     .copied()
                                                //                     .collect()
                                                //             };
                                                //             seed.fuzz_constraints.push(new);
                                                //         }
                                                //     }

                                                //     seed.fuzz_constraints.retain(|c| c.new_found.any());
                                                // }

                                                self.check_states(
                                                    &mut goals,
                                                    goal_index.0,
                                                    stored_base,
                                                    &entry.state_in,
                                                    &state_out,
                                                    !generated_from_enumeration,
                                                    rng,
                                                    &mut new_queue,
                                                );
                                            }
                                        }
                                    }

                                    if store {
                                        stored_base = Some((
                                            entry.observation_id,
                                            Rc::new(Base {
                                                // destinations: self.results.check_destinations(entry.state_in.as_system_state().as_ref(), &state_out),
                                                from: entry.state_in.clone(),
                                                to: state_out,
                                            }),
                                        ))
                                    }
                                },
                                Err(_) => {
                                    goals[original.goal.0].num_failed += 1;
                                    if store {
                                        stored_base = None;
                                    }

                                    if !generated_from_enumeration {
                                        check_dependent_bytes.push(entry);
                                    }
                                },
                            }

                            // obs_t = Instant::now();
                        }

                        while let Some(entry) = check_dependent_bytes.pop() {
                            let goal_index = entry.original.goal.0;
                            let goal = goals[goal_index].clone();
                            info!("Checking {:?}", goal);
                            let num_ok = {
                                let checks = {
                                    let mask = if goal.is_single_byte() {
                                        let (reg, index) = self.view.as_reg(goal.bytes[0]);
                                        if let Some(mask) = reg.mask() {
                                            (mask >> (index * 8)) as u8
                                        } else {
                                            0xff
                                        }
                                    } else {
                                        0xff
                                    };

                                    let base_state = entry.original.base.from.as_system_state();
                                    let base_state = base_state.as_ref();
                                    let base_value = self.view.get(base_state, goal.bytes[0]);
                                    SimpleJitState::build(
                                        &goal.bytes,
                                        &self.state_gen,
                                        self.view,
                                        base_state,
                                        |index, state| {
                                            let n = index as u8;

                                            // Skip all possibilities not matching the mask
                                            if n & !mask != 0 {
                                                return false;
                                            }

                                            trace!("{goal:?} = {n:02X}");
                                            if goal.is_single_byte() {
                                                if base_value == n {
                                                    // The state we will generate here will be identical to `base.from`
                                                    return false;
                                                }

                                                goal.modify_state(self.view, state, n);
                                            } else {
                                                let spec = goal.spec();
                                                modify_state_with_spec(rng, self.view, state, spec)
                                            }

                                            true
                                        },
                                        256,
                                    )
                                    .collect::<Vec<_>>()
                                };

                                let mut num_ok = 0;
                                for (state_in, state_out) in oracle.batch_observe_iter(checks) {
                                    match state_out {
                                        Ok(state_out) => {
                                            goals[goal_index].num_observed += 1;

                                            self.check_states(
                                                &mut goals,
                                                goal_index,
                                                entry.original.base.clone(),
                                                &state_in.into(),
                                                &state_out,
                                                false,
                                                rng,
                                                &mut new_queue,
                                            );
                                            num_ok += 1;
                                        },
                                        Err(_) => goals[goal_index].num_failed += 1,
                                    }
                                }

                                num_ok
                            };

                            if num_ok == 0 {
                                let base_state = entry.original.base.from.as_system_state();
                                let base_state = base_state.as_ref();
                                let dependent_bytes = self.find_dependent_bytes(rng, oracle, &goal.bytes, base_state)?;
                                info!(
                                    "Dependent bytes: we can't modify {:?}; Need dependent bytes: {:?}",
                                    goal, dependent_bytes
                                );

                                let mut combined_goals = Vec::new();
                                let mut removed_indices = Vec::new();

                                let mut min_observations: usize = usize::MAX;
                                for index in (0..goals.len()).rev() {
                                    let goal = &goals[index];
                                    let matched = goal.bytes.iter().any(|b| dependent_bytes.contains(b));

                                    if matched {
                                        min_observations = min_observations.min(goal.num_observed);
                                        combined_goals.push(goals.remove(index));
                                        removed_indices.push(index);
                                    }
                                }

                                new_queue.retain_mut(|entry| {
                                    let k = &mut entry.original.goal.0;

                                    if removed_indices.contains(k) {
                                        false
                                    } else {
                                        *k -= removed_indices.iter().filter(|&&i| i <= *k).count();

                                        if let Some((_, goal_index)) = &mut entry.compare_with_stored {
                                            if removed_indices.contains(&goal_index.0) {
                                                entry.compare_with_stored = None;
                                            } else {
                                                goal_index.0 -= removed_indices.iter().filter(|&&i| i <= goal_index.0).count();
                                            }
                                        }

                                        true
                                    }
                                });

                                check_dependent_bytes.retain_mut(|entry| {
                                    let k = &mut entry.original.goal.0;

                                    if removed_indices.contains(k) {
                                        false
                                    } else {
                                        *k -= removed_indices.iter().filter(|&&i| i <= *k).count();

                                        if let Some((_, goal_index)) = &mut entry.compare_with_stored {
                                            if removed_indices.contains(&goal_index.0) {
                                                entry.compare_with_stored = None;
                                            } else {
                                                goal_index.0 -= removed_indices.iter().filter(|&&i| i <= goal_index.0).count();
                                            }
                                        }

                                        true
                                    }
                                });

                                let bytes = combined_goals.iter().flat_map(|g| g.bytes.iter()).copied().collect();
                                let needs_adapt = combined_goals.iter().any(|g| g.needs_adapt);
                                let mut new_goal = Goal::new(self.view, bytes, needs_adapt);
                                new_goal.num_observed = min_observations;

                                info!("Created a new goal: {:?}", new_goal);
                                found_dependent_bytes = true;

                                goals.push(new_goal);
                            }
                        }

                        if new_queue.is_empty() {
                            break
                        } else {
                            queue = new_queue;
                        }
                    }

                    // info!("Proof pairs: {}", self.seeds.len());
                    let changed = compute_changed(
                        &self.view,
                        interesting.a.from.as_system_state().as_ref(),
                        interesting.b.from.as_system_state().as_ref(),
                    );
                    let ignorable = self.results.compute_ignorable_differences(&changed);
                    if self.results.observations_consistent(
                        (interesting.a.from.as_system_state().as_ref(), &interesting.a.to).into(),
                        (interesting.b.from.as_system_state().as_ref(), &interesting.b.to).into(),
                        &ignorable,
                    ) {
                        break
                    } else {
                        not_found += 1;
                        info!("Repeating with not_found={not_found}");
                        if not_found > 100 {
                            error!("Unable to find dataflow from inconsistency in: {interesting:#?}");
                            break
                        }
                    }
                }
            } else {
                break
            }
        }

        // info!("Proof pairs: {}", self.seeds.len());
        // debug!("Proof traces: {:?}", self.seeds.iter().enumerate().map(|(index, p)| (index, p.parent)).collect::<Vec<_>>());

        // let mut seen = vec![0; self.seeds.len()];
        // for (id, _proof) in self.seeds.iter().enumerate().rev() {
        //     if seen[id] == 0 {
        //         let mut path = Vec::new();
        //         path.push(SeedId(id));

        //         let mut id = id;
        //         while let Some(parent) = self.seeds[id].parent {
        //             path.push(parent);

        //             seen[parent.0] += 1;
        //             id = parent.0;
        //         }

        //         path.reverse();

        //         debug!("Path: {path:?}");
        //     }
        // }

        // let mut most_interesting = seen.iter()
        //     .copied()
        //     .enumerate()
        //     .filter(|&(_, num)| num > 0)
        //     .collect::<Vec<_>>();
        // most_interesting.sort_by_key(|(_, num)| usize::MAX - num);

        // info!("Most interesting proofs: {most_interesting:?}");

        info!("Goals: {:?}", goals);
        // TODO: println!("Analysis done in {}ms", start.elapsed().as_millis());
        // TODO: println!("Total accounted for: {}ms", (fuzz_time + self.enum_time + self.expand_time + observe_time + self.check_dataflow_time).as_millis());

        if goals.iter().any(|g| g.num_observed == 0) {
            error!("We did not observe all goals");
            return Err(DataflowAnalysisError::NotAllBytesAreIndependentlyModifyable)
        }

        // TODO: println!("Fuzzing took: {}ms", fuzz_time.as_millis());
        // TODO: println!("Enum took: {}ms", self.enum_time.as_millis());
        // TODO: println!("Expand took: {}ms", self.expand_time.as_millis());
        // TODO: println!("Observing took: {}ms for {num_observations} observations ({}ns/obs)", observe_time.as_millis(), observe_time.as_nanos() / num_observations);
        // TODO: println!("Checking dataflows took: {}ms in {} checks ({}ns / check)", self.check_dataflow_time.as_millis(), self.num_dataflow_checks, self.check_dataflow_time.as_nanos().checked_div(self.num_dataflow_checks as u128).unwrap_or(0));
        // TODO: println!("    Check diff: {}ms", self.check_diff_time.as_millis());
        // TODO: println!("    Check other: {}ms", self.check_other_time.as_millis());
        // TODO: println!("    Check weak: {}ms", self.check_weak_dests_time.as_millis());
        Ok(Dataflows {
            dataflows: self.results.collect_dataflows(),
            found_dependent_bytes,
        })
    }

    pub fn try_reduce_counterexample<'j, R: Rng, O: Oracle<A>>(
        &mut self, rng: &mut R, oracle: &mut O, interesting: &InterestingPair<'j, A>,
    ) -> Option<InterestingPair<'j, A>> {
        let mut state_in = interesting.a.from.as_system_state().as_ref().clone();
        let ref_in = interesting.b.from.as_system_state();
        let mut changes = compute_changed(&self.view, &state_in, ref_in.as_ref());
        let mut any = false;
        for _ in 0..1000 {
            for size in (1..changes.len()).rev() {
                changes.shuffle(rng);

                let to_change = &changes[..size];

                let old = to_change.iter().map(|&b| self.view.get(&state_in, b)).collect::<Vec<_>>();
                for &b in to_change.iter() {
                    self.view.set(&mut state_in, b, self.view.get(ref_in.as_ref(), b));
                    debug!("Setting {:?} / {:?}", b, self.view.as_reg(b));
                }

                if self.state_gen.adapt(&mut state_in, false) {
                    if let Ok(state_out) = oracle.observe(&state_in) {
                        let changed = compute_changed(&self.view, interesting.b.from.as_system_state().as_ref(), &state_in);
                        let ignorable = self.results.compute_ignorable_differences(&changed);
                        if self.results.observations_consistent(
                            (interesting.b.from.as_system_state().as_ref(), &interesting.b.to).into(),
                            (&state_in, &state_out).into(),
                            &ignorable,
                        ) {
                            debug!("Observations have become consistent");

                            for (&old, &b) in old.iter().zip(to_change.iter()) {
                                self.view.set(&mut state_in, b, old);
                            }

                            assert!(self.state_gen.adapt(&mut state_in, false));
                        } else {
                            debug!("Problem!");
                            changes.drain(..size).for_each(drop);
                            any = true;
                            break;
                        }
                    }
                } else {
                    debug!("Adapt failed");

                    for (&old, &b) in old.iter().zip(to_change.iter()) {
                        self.view.set(&mut state_in, b, old);
                    }

                    assert!(self.state_gen.adapt(&mut state_in, false));
                }
            }
        }

        info!("Reduced to {:?}, any={any}", changes);

        if any {
            let to = oracle.observe(&state_in).unwrap();
            debug!("Transition: {state_in:X?} => {to:X?}");
            Some(InterestingPair {
                goal_index: interesting.goal_index,
                a: Rc::new(Base {
                    // destinations: self.results.check_destinations(&state_in, &to),
                    from: state_in.into(),
                    to,
                }),
                b: interesting.b.clone(),
            })
        } else {
            None
        }
    }
}
