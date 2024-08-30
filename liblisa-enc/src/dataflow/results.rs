use std::collections::HashMap;
use std::marker::PhantomData;

use itertools::Itertools;
use liblisa::arch::{Arch, CpuState};
use liblisa::oracle::MappableArea;
use liblisa::state::jit::MaybeJitState;
use liblisa::state::{AsSystemState, StateByte, SystemState, SystemStateByteView, SystemStateIoPair};
use liblisa::utils::bitmap::DenseSet;
use log::{debug, info};

use super::analyzer::{Base, Goal};
use super::flow::Dataflow;
use super::spec::IsDataflowSet;
use super::IsDataflow;
use crate::dataflow::flow::{merge_flowitems, FlowItem};

#[derive(Clone, Debug)]
pub struct DataflowCheckResult {
    dataflows: Vec<IsDataflow>,
    destinations: Vec<StateByte>,
}

impl DataflowCheckResult {
    pub fn any(&self) -> bool {
        !self.dataflows.is_empty() || !self.destinations.is_empty()
    }

    pub fn empty() -> Self {
        DataflowCheckResult {
            dataflows: Vec::new(),
            destinations: Vec::new(),
        }
    }
}

pub fn compute_changed<A: Arch>(view: &SystemStateByteView<A>, a: &SystemState<A>, b: &SystemState<A>) -> Vec<StateByte> {
    let mut changed = Vec::new();
    view.find_differences(a, b, &mut |b| changed.push(b));
    changed
}

#[derive(Clone, Debug)]
pub struct IgnorableDifferences<D> {
    ignored: DenseSet,
    diff_mask: D,
}

impl<D: Default> Default for IgnorableDifferences<D> {
    fn default() -> Self {
        Self {
            ignored: DenseSet::new(),
            diff_mask: D::default(),
        }
    }
}

#[derive(Clone)]
pub struct AnalysisResult<'a, A: Arch, M: MappableArea> {
    view: SystemStateByteView<'a, A>,
    pub(crate) destinations: DenseSet,
    destinations_diff_mask: <A::CpuState as CpuState<A>>::DiffMask,
    pub(crate) dataflows: IsDataflowSet,
    pub(crate) weak_self_dataflows: DenseSet,
    unobservable_inputs: DenseSet,
    _phantom: PhantomData<*const (A, M)>,
}

impl<'a, A: Arch, M: MappableArea> AnalysisResult<'a, A, M> {
    pub fn new(view: SystemStateByteView<'a, A>) -> AnalysisResult<'a, A, M> {
        Self {
            view,
            destinations: DenseSet::new(),
            destinations_diff_mask: Default::default(),
            dataflows: IsDataflowSet::new(),
            weak_self_dataflows: DenseSet::new(),
            unobservable_inputs: DenseSet::new(),
            _phantom: PhantomData,
        }
    }

    pub fn compute_ignorable_differences(
        &self, changed: &[StateByte],
    ) -> IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask> {
        let mut ignored_differences = self.unobservable_inputs.clone();
        for &change in changed.iter() {
            for dest in self.dataflows.dests_for_source(change) {
                ignored_differences.set(dest.as_usize());
            }
        }

        IgnorableDifferences {
            diff_mask: self
                .view
                .create_diff_mask(changed.iter().flat_map(|source| self.dataflows.dests_for_source(*source))),
            ignored: ignored_differences,
        }
    }

    // (a_in, a_out): (&SystemState<A>, &SystemState<A>)
    // base: &Base<A, V>
    pub fn observations_consistent(
        &mut self, a: SystemStateIoPair<A>, b: SystemStateIoPair<A>,
        ignorable_differences: &IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask>,
    ) -> bool {
        // let a_in = base.from.as_system_state();
        // let a_in = a_in.as_ref();
        // let a_out = &base.to;
        let mut consistent = true;
        let mut any_new = false;
        let view = self.view;
        // let t = Instant::now();
        view.find_dataflows_masked(
            b,
            a,
            &self.destinations_diff_mask,
            &ignorable_differences.diff_mask,
            &mut |dest| {
                if consistent && !ignorable_differences.ignored.contains(dest.as_usize()) {
                    if self.destinations.set(dest.as_usize()) {
                        consistent = false;

                        info!("Inconsistency: Destination {:?} | {:?}", dest, self.view.as_reg(dest));
                        debug!(
                            "    by: {:#X?} vs {:#X?}",
                            (a.state_in, a.state_out),
                            (b.state_in, b.state_out)
                        );
                        any_new = true;
                    }

                    if self.view.bytes_unequal(dest, a.state_out, b.state_out) {
                        info!(
                            "Inconsistency: {:?} changed, but no sources affecting the destination were modified",
                            dest
                        );
                        debug!(
                            "    by: {:#X?} vs {:#X?}",
                            (a.state_in, a.state_out),
                            (b.state_in, b.state_out)
                        );

                        consistent = false;
                    }
                }
            },
        );
        // *find_diff_time += t.elapsed();

        if any_new {
            self.destinations_diff_mask = self.view.create_diff_mask(self.destinations.iter().map(StateByte::new));
        }

        if !consistent {
            return false;
        }

        // let t = Instant::now();
        // for dest in base.destinations.iter().copied() {
        //     if !ignorable_differences.ignored.contains(dest.as_usize()) && self.view.bytes_unequal(dest, &base.to, b_out) {
        //         info!("Inconsistency: {:?} changed (rev), but no sources affecting the destination were modified", dest);
        //         debug!("    by: {:#X?} vs {:#X?}", base, (&b_in, &b_out));

        //         *check_other_dests_time += t.elapsed();

        //         return false;
        //     }
        // }
        // view.find_dataflows_masked(a_in, a_out, b_out, &self.destinations_diff_mask, &ignorable_differences.diff_mask, &mut |dest| {
        //     if consistent && !ignorable_differences.ignored.contains(dest.as_usize()) && self.view.bytes_unequal(dest, a_out, b_out) {
        //         info!("Inconsistency: {:?} changed, but no sources affecting the destination were modified", dest);
        //         debug!("    by: {:#X?} vs {:#X?}", (a_in, a_out), (&b_in, &b_out));

        //         consistent = false;
        //     }
        // });

        // *check_other_dests_time += t.elapsed();

        consistent
    }

    pub fn verify_weak_self_dataflow_consistency(
        &mut self, changed: &[StateByte], (a_in, a_out): (&SystemState<A>, &SystemState<A>),
        (b_in, b_out): (&SystemState<A>, &SystemState<A>),
    ) -> bool {
        let mut consistent = true;
        for &dest in changed.iter() {
            if self.view.bytes_unequal(dest, a_in, b_in)
                && self.view.bytes_unequal(dest, a_out, b_out)
                && self.view.bytes_equal(dest, a_in, a_out)
                && self.view.bytes_equal(dest, b_in, b_out)
                && self.weak_self_dataflows.set(dest.as_usize())
            {
                info!("Inconsistency: Weak destination for {dest:?} | {:?}", self.view.as_reg(dest));
                debug!(" -- based on: {:X?} vs {:X?}", (a_in, a_out), (&b_in, b_out));
                consistent = false;
            }
        }

        consistent
    }

    pub fn check_dataflows_with_ignorable_differences(
        &mut self, goal: &Goal<A>, ignorable_differences: &IgnorableDifferences<<A::CpuState as CpuState<A>>::DiffMask>,
        base: &Base<'_, A>, (b_in, b_out): (&SystemState<A>, &SystemState<A>),
    ) -> DataflowCheckResult {
        let mut new_found = DataflowCheckResult::empty();
        let mut any_new = false;

        self.view.find_dataflows_masked(
            (b_in, b_out).into(),
            (base.from.as_system_state().as_ref(), &base.to).into(),
            &self.destinations_diff_mask,
            &ignorable_differences.diff_mask,
            &mut |dest| {
                if !ignorable_differences.ignored.contains(dest.as_usize()) {
                    if self.destinations.set(dest.as_usize()) {
                        info!("DESTINATION: {:?} | {:?}", dest, self.view.as_reg(dest));
                        debug!("    by: {:#X?} {:#X?}", base, (&b_in, &b_out));

                        new_found.destinations.push(dest);
                        any_new = true;
                    }

                    if self.view.bytes_unequal(dest, &base.to, b_out) {
                        for source in goal.bytes.iter().cloned() {
                            let flow = IsDataflow(source, dest);
                            if !self.unobservable_inputs.contains(dest.as_usize()) && self.dataflows.push(flow) {
                                info!(
                                    "PROVEN: {:?} | {:?} -> {:?}",
                                    flow,
                                    self.view.as_reg(flow.0),
                                    self.view.as_reg(flow.1)
                                );
                                debug!("    by: {:#X?} {:#X?}", base, (&b_in, &b_out));

                                // If the dataflow is to a destination with unobservable inputs,
                                // this dataflow doesn't really exist and we should not treat this state as interesting.
                                new_found.dataflows.push(flow);
                            }
                        }
                    }
                }
            },
        );

        if any_new {
            self.destinations_diff_mask = self.view.create_diff_mask(self.destinations.iter().map(StateByte::new));
        }

        // let t = Instant::now();
        for &dest in goal.bytes.iter() {
            if !self.weak_self_dataflows.contains(dest.as_usize())
                && self.view.bytes_unequal(dest, &base.to, b_out)
                && self.view.bytes_equal(dest, b_in, b_out)
            {
                // as_system_state might not be (almost) zero-cost, so we avoid calling it unless we really need to.
                let system_state = base.from.as_system_state();
                let from = system_state.as_ref();
                if self.view.bytes_equal(dest, from, &base.to) && self.weak_self_dataflows.set(dest.as_usize()) {
                    info!("Weak destination for {dest:?} | {:?}", self.view.as_reg(dest));
                    debug!(" -- based on: {:X?} vs {:X?}", base, (&b_in, b_out));
                }
            }
        }

        new_found
    }

    pub fn collect_dataflows(&self) -> Vec<Dataflow<A::Reg>> {
        let mut dataflows = self.collect_unmerged_dataflows();

        // We check for sources that overlap, but are not equal.
        // An instruction like 0fc6c12b (shufps) might produce dataflows that look like this:
        //      A[0] <= B[8], A[1] <= B[9], A[2] <= B[10], A[3] <= B[11]
        //      A[4] <= B[8], A[5] <= B[9], A[6] <= B[10], A[7] <= B[11]
        //      ..
        //
        // Or:
        //      A[0] <= B[8], A[1] <= B[9], A[2] <= B[10], A[3] <= B[11]
        //      A[4] <= B[0], A[5] <= B[1], A[6] <= B[2], A[7] <= B[3]
        //      ..
        //
        //
        // From just those two dataflows, we have no reason to concude that regA[0..4] must be interdependent.
        // We would need to see all previous sources *and* something extra to conclude that it really is one computation.
        // For example:
        //
        //      regA[0] <= regB[8]
        //      regA[1] <= regB[8], regB[9]
        //
        // This might correspond to an increment.
        //
        // HOWEVER, just using the rule "merge unless equal" doesn't produce good results for things like addpd:
        // c5c958041d00060121: vaddpd xmm0,xmm6,XMMWORD PTR [rbx*1+0x21010600]
        //
        // This instruction produces dataflows of the form:
        //      regA[0] <= regB[0..7], regC[0..7]
        //      regA[1] <= regB[0..7], regC[0..7]
        //
        // These should clearly be grouped, as they represent a single addition. But even if we ignore that, it makes analysis fragile.
        // Sometimes a single byte might be missed which causes an entire chain to collapse.
        //
        // So, as a compromise between these two goals, the merge rule is:
        //      - If sources are equal, merge if targets are adjacent and both the same register
        //      - If sources overlap but are not equal, merge if targets are both the same register.
        // TODO: Is there anywhere where this reasoning doesn't produce good results? Please document.

        info!("Unmerged dataflows: {:#?}", dataflows);
        while let Some(((i1, i2), _)) = dataflows
            .iter()
            .enumerate()
            .flat_map(|(i1, a)| dataflows.iter().enumerate().skip(i1 + 1).map(move |b| ((i1, a), b)))
            .filter(|((_, dataflow), (_, other_dataflow))| {
                dataflow.dest.reg == other_dataflow.dest.reg
                    && ((dataflow.sources_overlap_but_not_equal(other_dataflow) || dataflow.destinations_overlap(other_dataflow))
                        || (dataflow.sources_equal(other_dataflow)
                            && dataflow.destinations_adjacent(other_dataflow)
                            && dataflow.num_source_bytes() > 1)
                        || dataflow.destination_flag_registers_match(other_dataflow))
                    && (!(dataflow.sources.is_empty() && other_dataflow.sources.is_empty())
                        || dataflow.destination_flag_registers_match(other_dataflow))
            })
            .map(|((i1, dataflow), (i2, other_dataflow))| {
                ((i1, i2), {
                    let dest_distance = if other_dataflow.dest.end_byte >= dataflow.dest.start_byte
                        && other_dataflow.dest.start_byte <= dataflow.dest.end_byte
                    {
                        0
                    } else if other_dataflow.dest.end_byte < dataflow.dest.start_byte {
                        1 + dataflow.dest.start_byte - other_dataflow.dest.end_byte
                    } else if other_dataflow.dest.start_byte > dataflow.dest.end_byte {
                        1 + other_dataflow.dest.start_byte - dataflow.dest.end_byte
                    } else {
                        unreachable!()
                    };

                    let source_differences = other_dataflow
                        .sources
                        .iter()
                        .filter(|s| !dataflow.sources.contains(s))
                        .count()
                        + dataflow
                            .sources
                            .iter()
                            .filter(|s| !other_dataflow.sources.contains(s))
                            .count();

                    (dest_distance, source_differences)
                })
            })
            .min_by_key(|(_, distance)| *distance)
        {
            let other_dataflow = dataflows.remove(i2);
            let dataflow = &mut dataflows[i1];
            debug!("Merging {dataflow:?} @ {i1} and {other_dataflow:?} @ {i2}");
            dataflow.merge(&other_dataflow);
            debug!("Merge result: {dataflow:?}");
        }

        // Make sure flag inputs use sources that are at least as large as the sources used for actual computations.
        let all_sources = dataflows.iter().flat_map(|d| d.sources.iter()).cloned().collect::<Vec<_>>();
        for dataflow in dataflows.iter_mut() {
            if dataflow.dest.reg.is_flags() {
                for source in dataflow.sources.iter_mut() {
                    for v in all_sources.iter() {
                        if !v.reg.is_flags() && v.reg == source.reg {
                            source.merge(v);
                        }
                    }
                }
            }
        }

        for dataflow in dataflows.iter_mut() {
            dataflow.sources.sort();
        }

        dataflows.sort_by_key(|flow| flow.dest.clone());
        dataflows
    }

    pub fn collect_unmerged_dataflows(&self) -> Vec<Dataflow<A::Reg>> {
        info!("Proven: {:?}", self.dataflows);
        info!("Destinations: {:?}", self.destinations);

        let mut dataflows = self.dataflows.clone();
        let mut destinations = self.destinations.clone();
        let expanded_flag_bytes = self
            .destinations
            .iter()
            .flat_map(|dest| {
                let dest = StateByte::new(dest);
                let (reg, _) = self.view.as_reg(dest);
                if reg.is_flags() {
                    Some((0..reg.byte_size()).map(move |index| self.view.reg_to_byte(reg, index)))
                } else {
                    None
                }
            })
            .flatten()
            .collect::<Vec<_>>();

        for expanded_byte in expanded_flag_bytes {
            destinations.set(expanded_byte.as_usize());
        }

        for dest in destinations.iter() {
            let dest = StateByte::new(dest);
            if self.weak_self_dataflows.contains(dest.as_usize()) && dataflows.push(IsDataflow(dest, dest)) {
                info!("Weak dataflows used: {:?} | {:?}", dest, self.view.as_reg(dest));
            }
        }

        let mut grouped = HashMap::new();
        for prop in dataflows.iter().copied() {
            info!("Dataflow: {:?} -> {:?}", self.view.as_reg(prop.0), self.view.as_reg(prop.1));
            grouped.entry(prop.1).or_insert_with(Vec::new).push(prop.0);
        }

        for destination in destinations.iter() {
            grouped.entry(StateByte::new(destination)).or_insert_with(Vec::new);
        }

        for group in grouped.values_mut() {
            group.sort();
        }

        info!("Grouped dataflows (destination <= [set of sources]): {:#?}", grouped);

        // If there are multiple outputs for a single register, inputs from the same register may not overlap
        let mut dataflows = Vec::new();
        for (key, value) in grouped {
            let (dest_reg, dest_byte) = self.view.as_reg(key);
            let (start_byte, end_byte) = if dest_reg.is_flags() {
                (0, dest_reg.byte_size() - 1)
            } else {
                (dest_byte, dest_byte)
            };
            info!(
                "Destination {:?} with sources {:?} = {}",
                (&dest_reg, (start_byte, end_byte)),
                value,
                value.iter().map(|b| format!("{:?}", self.view.as_reg(*b))).join(", ")
            );
            dataflows.push(Dataflow {
                dest: FlowItem {
                    reg: dest_reg,
                    start_byte,
                    end_byte,
                },
                unobservable_inputs: self.unobservable_inputs.contains(key.as_usize()),
                sources: merge_flowitems(value.into_iter().map(|b| self.view.as_reg(b)).map(|(reg, byte)| FlowItem {
                    reg,
                    start_byte: byte,
                    end_byte: byte,
                }))
                .collect(),
            })
        }

        dataflows
    }

    pub fn check_unobservable_inputs(&mut self, from: &MaybeJitState<A>, a: &SystemState<A>, b: &SystemState<A>) {
        self.view.find_differences(a, b, &mut |byte| {
            if self.unobservable_inputs.set(byte.as_usize()) {
                info!("Unobservable input: {byte:?} ({:?})", self.view.as_reg(byte));
                debug!("From {:?} to either {:?} or {:?}", from.as_system_state().as_ref(), a, b);
            }
        });
    }
}
