use std::cell::RefCell;
use std::iter::repeat_with;
use std::rc::Rc;
use std::time::Duration;

use itertools::Itertools;
use liblisa::arch::{Arch, CpuState};
use liblisa::oracle::{MappableArea, Oracle};
use liblisa::state::jit::{ComplexJitState, MaybeJitState};
use liblisa::state::random::StateGen;
use liblisa::state::{AsSystemState, StateByte, SystemState, SystemStateByteView};
use log::info;
use rand::seq::SliceRandom;
use rand::{Rng, SeedableRng};
use rand_xoshiro::{Xoroshiro128PlusPlus, Xoshiro256PlusPlus};

use super::analyzer::{Base, Goal, InterestingPair};
use super::results::{AnalysisResult, IgnorableDifferences};
use super::DataflowAnalysisError;
use crate::dataflow::analyzer::modify_state_with_spec_possibly_eq;
use crate::dataflow::results::compute_changed;
use crate::dataflow::spec::EquivalenceSpec;

pub struct Fuzz<'a, 'borrow, A: Arch, M: MappableArea> {
    state_gen: &'borrow StateGen<'a, A, M>,
    view: SystemStateByteView<'a, A>,
    results: &'borrow mut AnalysisResult<'a, A, M>,
    goals: &'borrow Vec<Goal<A>>,
    interesting_bases: &'borrow [Rc<Base<'a, A>>],
}

struct TestState<'j, A: Arch> {
    changed: Vec<StateByte>,
    ignorable_differences: Rc<IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask>>,
    state_in: MaybeJitState<'j, A>,
    base: &'j (SystemState<A>, SystemState<A>),
    can_check_weak_dataflows: bool,
}

impl<'j, A: Arch> AsSystemState<A> for TestState<'j, A> {
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

struct TestState2<'j, A: Arch> {
    ignorable_differences: Rc<IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask>>,
    state_in: MaybeJitState<'j, A>,
}

impl<'j, A: Arch> AsSystemState<A> for TestState2<'j, A> {
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

struct TestState3<'borrow, 'j, A: Arch> {
    base: &'borrow Rc<Base<'j, A>>,
    ignorable_differences: Rc<IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask>>,
    state_in: SystemState<A>,
}

impl<A: Arch> AsSystemState<A> for TestState3<'_, '_, A> {
    type Output<'a>
        = &'a SystemState<A>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        self.state_in.as_system_state()
    }

    fn num_memory_mappings(&self) -> usize {
        self.state_in.num_memory_mappings()
    }
}

impl<'a, 'borrow, A: Arch, M: MappableArea> Fuzz<'a, 'borrow, A, M> {
    pub fn new(
        state_gen: &'borrow StateGen<'a, A, M>, view: SystemStateByteView<'a, A>, results: &'borrow mut AnalysisResult<'a, A, M>,
        goals: &'borrow Vec<Goal<A>>, interesting_bases: &'borrow [Rc<Base<'a, A>>],
    ) -> Self {
        Fuzz {
            state_gen,
            view,
            results,
            goals,
            interesting_bases,
        }
    }

    fn generate_base_state<R: Rng>(state_gen: &StateGen<'a, A, M>, rng: &mut R) -> SystemState<A> {
        let mut state = state_gen.randomize_new(rng).unwrap();
        match rng.gen_range(0..10usize) {
            0 => {
                let filled_byte = rng.gen();
                state_gen.fill_with_byte(rng, &mut state, filled_byte);
            },
            1 => {
                if let Some(&addr_reg) = state_gen.address_registers().choose(rng) {
                    state_gen.fill_from_address_register(rng, &mut state, addr_reg);
                }
            },
            _ => (),
        }
        state
    }

    pub fn fuzz(
        &mut self, rng: &mut impl Rng, oracle: &mut impl Oracle<A>,
    ) -> Result<Option<InterestingPair<'a, A>>, DataflowAnalysisError<A>> {
        let state_gen = self.state_gen.clone();

        let _check_diff_time = Duration::ZERO;
        let _check_other_time = Duration::ZERO;

        let unmerged_dataflows = self.results.collect_unmerged_dataflows();
        let dataflows = self.results.collect_dataflows();

        let view = self.view;
        let results = self.results.clone();
        let results = &results;
        let unmerged_dataflows = &unmerged_dataflows;
        // These are the sources that we are filling in collect_dataflows().
        // For example, if we have regA[0] -> regB[0], regA[4] -> regB[0] and regA[2] -> regB[1], we produce a dataflow regA[0..4] -> regB[0..1].
        // We effectively treat regA[0] -> regB[1], regA[1] -> regB[1], regA[3] -> regB[1] as if they existed.
        // Here, we identify the sources for each destination that we don't actually have proof of, but fill in.
        // During fuzzing we will try to find states that also prove these dataflows.
        let full_filled_dataflows = dataflows
            .iter()
            .flat_map(|flow| {
                (flow.dest.start_byte..=flow.dest.end_byte).map(move |dest_byte| {
                    let dest = view.reg_to_byte(flow.dest.reg, dest_byte);

                    (
                        dest,
                        flow.sources
                            .iter()
                            .cloned()
                            .flat_map(move |source| {
                                (source.start_byte..=source.end_byte)
                                    .map(move |source_byte| view.reg_to_byte(source.reg, source_byte))
                            })
                            .filter(move |&source| {
                                !unmerged_dataflows
                                    .iter()
                                    .filter(|df| df.dest.contains(view, dest))
                                    .any(|df| df.sources.iter().any(|s| s.contains(view, source)))
                            })
                            .filter(move |source| source != &dest)
                            .collect::<Vec<_>>(),
                    )
                })
            })
            .filter(|(_, v)| !v.is_empty())
            .collect::<Vec<_>>();
        info!("Full filled dataflows: {:?}", full_filled_dataflows);

        let filled_dataflows = {
            let mut v = full_filled_dataflows.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>();
            v.sort();
            v.dedup();
            v
        };

        let goals_without_weak_dataflows = self
            .goals
            .iter()
            .enumerate()
            .filter(|(_, goal)| {
                !goal
                    .bytes
                    .iter()
                    .any(|b| self.results.weak_self_dataflows.contains(b.as_usize()))
            })
            .collect::<Vec<_>>();

        info!("Filled dataflows: {:?}", filled_dataflows);

        let unique_sources = {
            let mut v = dataflows
                .iter()
                .map(|f| f.sources.clone())
                .filter(|v| !v.is_empty())
                .collect::<Vec<_>>();
            v.sort();
            v.dedup();

            v
        };

        let flags = (0..self.view.size())
            .map(StateByte::new)
            .flat_map(|b| {
                let (reg, index) = self.view.as_reg(b);
                if reg.is_flags() {
                    Some((
                        b,
                        ((reg.mask().unwrap_or(u64::MAX)) >> (index * 8)) as u8,
                        Rc::new(self.results.compute_ignorable_differences(&[b])),
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        info!("Unique sources: {:?}", unique_sources);

        // We need to observe a large number of different random states to make sure we find all destinations.
        // This loop uses a randomized state very often.
        // Relevant instructions:
        //     - 480F03A400000406D4
        //     - C483FD080C05000F900842
        //     - C403FD098000B40E9BA2
        //     - C402052C0522000000
        let bases = oracle
            .batch_observe_iter(repeat_with(|| Self::generate_base_state(&state_gen, rng)))
            .take(50_000)
            .flat_map(|(state_in, state_out)| state_out.ok().map(|state_out| (state_in, state_out)))
            .take(5000)
            .collect::<Vec<_>>();

        if bases.len() < 2_000 {
            return Err(DataflowAnalysisError::InstructionKeepsFaulting);
        }

        let tests = bases.iter().enumerate().flat_map(|(k, base)| {
            let (a_in, _) = base;
            let builder = ComplexJitState::build(a_in.clone(), self.state_gen, self.view);

            // Strategy 1: check and make sure we've mapped all weak dataflows
            // for (_goal_index, goal) in goals_without_weak_dataflows.iter()
            let weak_dataflow_test = if !goals_without_weak_dataflows.is_empty() {
                let (_goal_index, goal) = &goals_without_weak_dataflows[k % goals_without_weak_dataflows.len()];
                let mut changed = Vec::new();
                builder
                    .create(&goal.bytes, |state| {
                        for &b in goal.bytes.iter() {
                            let old = self.view.get(a_in, b);
                            let (reg, index) = self.view.as_reg(b);
                            let mask = reg
                                .mask()
                                .unwrap_or(u64::MAX)
                                .checked_shr(index as u32 * 8)
                                .unwrap_or(u64::MAX) as u8;
                            let new = rng.gen::<u8>() & mask;
                            self.view.set(state, b, new);
                            if new != old {
                                changed.push(b);
                            }
                        }

                        true
                    })
                    .map(|state| TestState {
                        state_in: MaybeJitState::from(state),
                        can_check_weak_dataflows: true,
                        ignorable_differences: Rc::new(results.compute_ignorable_differences(&changed)),
                        changed,
                        base,
                    })
            } else {
                None
            };

            // Strategy 2: Flip all flags
            // for (flag, mask, ignorable) in flags.iter()
            let flag_test = if !flags.is_empty() {
                let (flag, mask, ignorable) = &flags[k % flags.len()];
                let flag = *flag;
                builder
                    .create(&[flag], |state| {
                        let new = self.view.get(state, flag) ^ mask;
                        self.view.set(state, flag, new);

                        true
                    })
                    .map(|state| TestState {
                        state_in: MaybeJitState::from(state),
                        can_check_weak_dataflows: true,
                        ignorable_differences: Rc::clone(ignorable),
                        changed: vec![flag],
                        base,
                    })
            } else {
                None
            };

            // Strategy 3: For each dataflow: change only the bytes that we are filling in (see above)
            // for sources in filled_dataflows.iter()
            let mut rng = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
            let view = self.view;
            let fill_in_test = filled_dataflows.iter().filter_map(move |sources| {
                let mut changed = Vec::new();
                builder
                    .create(sources, |state| {
                        for &b in sources.iter() {
                            let old = view.get(a_in, b);
                            let (reg, index) = view.as_reg(b);
                            let mask = reg
                                .mask()
                                .unwrap_or(u64::MAX)
                                .checked_shr(index as u32 * 8)
                                .unwrap_or(u64::MAX) as u8;
                            let new = rng.gen::<u8>() & mask;
                            view.set(state, b, new);

                            if new != old {
                                changed.push(b);
                            }
                        }

                        true
                    })
                    .map(|state| TestState {
                        state_in: MaybeJitState::from(state),
                        can_check_weak_dataflows: false,
                        ignorable_differences: Rc::new(results.compute_ignorable_differences(&changed)),
                        changed,
                        base,
                    })
            });

            fill_in_test.chain(weak_dataflow_test).chain(flag_test)
        });

        for (test, state_out) in oracle.batch_observe_iter(tests.into_iter()) {
            let (a_in, a_out) = test.base;
            if let Ok(state_out) = state_out {
                let state_in = test.as_system_state();
                let state_in = state_in.as_ref();
                if (test.can_check_weak_dataflows
                    && !self
                        .results
                        .verify_weak_self_dataflow_consistency(&test.changed, (a_in, a_out), (state_in, &state_out)))
                    || !self.results.observations_consistent(
                        (a_in, a_out).into(),
                        (state_in, &state_out).into(),
                        &test.ignorable_differences,
                    )
                {
                    let modified = Base {
                        from: state_in.clone().into(),
                        to: state_out,
                    };

                    info!("Found counter-example");
                    let a = Rc::new(Base {
                        from: a_in.clone().into(),
                        to: a_out.clone(),
                    });

                    return Ok(Some(InterestingPair {
                        goal_index: None,
                        a: Rc::clone(&a),
                        b: Rc::new(modified),
                    }));
                }
            }
        }

        // TODO: What instr benefits from this fuzzing?
        let view = self.view;
        let rng = RefCell::new(Xoroshiro128PlusPlus::seed_from_u64(rng.gen()));
        let rng = &rng;
        let unique_sources = &unique_sources;
        let state_gen = &self.state_gen;
        let results = self.results.clone();
        let results = &results;

        // Relevant instructions:
        //  - 4C0FD1048D04898031
        const NUM_ITERATIONS: usize = 400;
        const NUM_SAMPLES: usize = 50;

        let data = unique_sources
            .iter()
            .map(|sources| {
                let kept_same = sources
                    .iter()
                    .flat_map(|item| (item.start_byte..=item.end_byte).map(|b| view.reg_to_byte(item.reg, b)))
                    .collect::<Vec<_>>();

                let spec = EquivalenceSpec::from_neqs(view, kept_same.iter().copied());
                let kept_same_in_spec_order = spec.bytes(&view).collect::<Vec<_>>();

                (kept_same_in_spec_order, spec)
            })
            .collect::<Vec<_>>();
        let data = &data;

        let test_cases = (0..NUM_ITERATIONS).flat_map(move |_| {
            data.iter().flat_map(move |(kept_same, spec)| {
                let new_base = Self::generate_base_state(state_gen, &mut *rng.borrow_mut());
                let randomized_state = state_gen.randomize_new(&mut *rng.borrow_mut()).unwrap();

                let actually_changed = {
                    let mut v = compute_changed(&view, &new_base, &randomized_state);
                    v.retain(|b| !kept_same.contains(b));
                    v
                };

                let ignorable_differences = Rc::new(results.compute_ignorable_differences(&actually_changed));

                let base_builder = ComplexJitState::build(new_base, state_gen, view);
                let randomized_builder = ComplexJitState::build(randomized_state, state_gen, view);

                (0..1000)
                    .flat_map(move |_| {
                        let rng = &mut *rng.borrow_mut();
                        let b = base_builder.create(kept_same, |state| {
                            modify_state_with_spec_possibly_eq(rng, view, state, spec);

                            true
                        });

                        b.and_then(|new_base| {
                            let result = {
                                let copy_from = new_base.as_system_state();
                                let copy_from = copy_from.as_ref();
                                randomized_builder
                                    .create_with_change_list(kept_same, kept_same.iter().map(|&b| view.get(copy_from, b)))
                            };

                            result.map(|b_in| {
                                (
                                    TestState2 {
                                        state_in: new_base.into(),
                                        ignorable_differences: Rc::clone(&ignorable_differences),
                                    },
                                    TestState2 {
                                        state_in: b_in.into(),
                                        ignorable_differences: Rc::clone(&ignorable_differences),
                                    },
                                )
                            })
                        })
                    })
                    .take(NUM_SAMPLES)
                    .flat_map(|(a, b)| [a, b])
            })
        });

        for ((a_in, a_out), (b_in, b_out)) in oracle.batch_observe_iter(test_cases).tuples() {
            if let Ok(a_out) = a_out
                && let Ok(b_out) = b_out
            {
                let b_in_state = b_in.as_system_state();
                let b_in_state = b_in_state.as_ref();

                if !self.results.observations_consistent(
                    (a_in.as_system_state().as_ref(), &a_out).into(),
                    (b_in_state, &b_out).into(),
                    &b_in.ignorable_differences,
                ) {
                    let a = Rc::new(Base {
                        from: a_in.state_in,
                        to: a_out,
                    });
                    let modified = Base {
                        from: b_in_state.clone().into(),
                        to: b_out,
                    };

                    info!("Found counter example from fuzz");

                    return Ok(Some(InterestingPair {
                        goal_index: None,
                        a: Rc::clone(&a),
                        b: Rc::new(modified),
                    }));
                }
            }
        }

        // We check interesting bases for instructions like C403F961040503792A1F1F, where we can only see a dataflow if multiple other inputs have certain values.
        const NUM_INTERESTING_SAMPLES: usize = 10;
        let test_cases = self.interesting_bases.iter().flat_map(|base| {
            data.iter().flat_map(move |(kept_same, _)| {
                (0..NUM_INTERESTING_SAMPLES).flat_map(move |_| {
                    let mut randomized_state = state_gen.randomize_new(&mut *rng.borrow_mut()).unwrap();

                    let base_in = base.from.as_system_state();
                    for &b in kept_same.iter() {
                        view.set(&mut randomized_state, b, view.get(base_in.as_ref(), b));
                    }

                    if state_gen.adapt(&mut randomized_state, false) {
                        let actually_changed = compute_changed(&view, base_in.as_ref(), &randomized_state);
                        let ignorable_differences = Rc::new(results.compute_ignorable_differences(&actually_changed));

                        Some(TestState3 {
                            base,
                            state_in: randomized_state,
                            ignorable_differences: Rc::clone(&ignorable_differences),
                        })
                    } else {
                        None
                    }
                })
            })
        });

        for (test_case, b_out) in oracle.batch_observe_iter(test_cases) {
            if let Ok(b_out) = b_out {
                let a_in = test_case.base.from.as_system_state();
                let a_in = a_in.as_ref();
                let a_out = test_case.base.to.as_system_state();
                let b_in = test_case.state_in;
                if !self.results.observations_consistent(
                    (a_in.as_system_state(), a_out).into(),
                    (&b_in, &b_out).into(),
                    &test_case.ignorable_differences,
                ) {
                    let a = Rc::clone(test_case.base);
                    let modified = Base {
                        from: b_in.into(),
                        to: b_out,
                    };

                    info!("Found counter example from fuzz");

                    return Ok(Some(InterestingPair {
                        goal_index: None,
                        a: Rc::clone(&a),
                        b: Rc::new(modified),
                    }));
                }
            }
        }

        Ok(None)
    }
}
