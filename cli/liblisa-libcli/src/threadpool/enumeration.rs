use std::collections::HashSet;
use std::iter::once;
use std::ops::Range;
use std::time::{Duration, Instant};

use liblisa::arch::{Arch, Scope};
use liblisa::encoding::Encoding;
use liblisa::instr::{FilterList, Instruction, InstructionCounter};
use liblisa::oracle::Oracle;
use liblisa::semantics::Computation;
use liblisa_enc::cache::EncodingAnalysisCache;
use liblisa_enc::AnalysisResult;
use log::{debug, info, trace};
use serde::{Deserialize, Serialize};

use crate::threadpool::work::Work;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Enumeration<S: Scope> {
    pub work: Vec<EnumWorkItem>,
    pub filters: FilterList,
    pub runtime_ms: u128,
    perfect_instrs_seen: HashSet<Instruction>,
    scope: S,
}

#[derive(Clone, Debug, Default)]
struct Stall {
    worker_index: usize,
    num: usize,
}

#[derive(Clone, Debug, Default)]
struct WorkItemStatus {
    stalled: bool,
    pending_or_done: bool,
    unstall: Vec<Stall>,
}

impl WorkItemStatus {
    pub fn can_run(&self, next_is_out_of_sequence: bool) -> bool {
        (!self.stalled || next_is_out_of_sequence) && !self.pending_or_done
    }

    pub fn compute_stalled(self_index: usize, status: &[WorkItemStatus]) -> Option<usize> {
        status
            .iter()
            .enumerate()
            .find(|(_, s)| s.unstall.iter().any(|item| item.worker_index == self_index))
            .map(|(index, _)| index)
    }
}

pub struct EnumerationRuntimeData {
    status: Vec<WorkItemStatus>,
    last_check: Instant,
    next_unstall: Instant,
}

impl EnumerationRuntimeData {
    pub fn from_enumeration<S: Scope>(enumeration: &Enumeration<S>) -> Self {
        EnumerationRuntimeData {
            status: (0..enumeration.work.len())
                .map(|_| WorkItemStatus {
                    stalled: false,
                    pending_or_done: false,
                    unstall: Vec::new(),
                })
                .collect(),
            last_check: Instant::now(),
            next_unstall: Instant::now(),
        }
    }
}

#[derive(Debug)]
pub struct AnalysisRequest<S: Scope> {
    worker_index: usize,
    at: Instant,
    counter: InstructionCounter,
    next_filtered_instruction: Option<Instruction>,
    scope: S,
}

impl<A: Arch, C: EncodingAnalysisCache<A> + Send + Sync, S: Scope> Work<A, C> for Enumeration<S> {
    type RuntimeData = EnumerationRuntimeData;
    type Request = AnalysisRequest<S>;
    type Result = AnalysisResult<A>;
    type Artifact = EnumerationArtifact<A, ()>;

    fn next(&mut self, data: &mut EnumerationRuntimeData) -> Option<AnalysisRequest<S>> {
        let now = Instant::now();
        if data.next_unstall < now {
            data.next_unstall = now + Duration::from_secs(100);

            // Clear `unstall` for any worker that's done
            for (status, work) in data.status.iter_mut().zip(self.work.iter()) {
                if work.done {
                    status.unstall.clear();
                    status.stalled = false;
                }
            }

            // Update stall information
            for (index, work) in self.work.iter_mut().enumerate() {
                let stalled_by = WorkItemStatus::compute_stalled(index, &data.status);
                data.status[index].stalled = stalled_by.is_some();
                work.stalled_by = stalled_by;
            }
        }

        let mut n = 0;
        loop {
            let next = self
                .work
                .iter_mut()
                .zip(data.status.iter_mut())
                .enumerate()
                .filter(|(_, (w, s))| !w.done && s.can_run(w.next_instr_is_out_of_sequence()))
                .min_by_key(|(_, (w, _))| w.virtual_runtime_ms)
                .and_then(|(index, (work, status))| {
                    println!("Checking work for worker_index={index}");

                    status.pending_or_done = true;
                    if let Some(counter) = work.next_instruction() {
                        Some(AnalysisRequest {
                            at: Instant::now(),
                            worker_index: index,
                            next_filtered_instruction: self.filters.next_matching_instruction(&counter.current()),
                            counter,
                            scope: self.scope.clone(),
                        })
                    } else {
                        None
                    }
                });

            if next.is_some() {
                return next;
            }

            if data
                .status
                .iter()
                .zip(self.work.iter())
                .all(|(s, w)| w.done || !s.can_run(w.next_instr_is_out_of_sequence()))
            {
                return None;
            }

            n += 1;
            if n > 10_000 {
                panic!("Endless loop detected");
            }
        }
    }

    fn complete(
        &mut self, data: &mut EnumerationRuntimeData, request: AnalysisRequest<S>, result: AnalysisResult<A>,
    ) -> Option<Self::Artifact> {
        if !data.status[request.worker_index].pending_or_done {
            panic!("Received a completion for work that is not pending!");
        }

        let ms_step = data.last_check.elapsed().as_millis();
        self.runtime_ms += ms_step;
        data.last_check = Instant::now();

        data.status[request.worker_index].pending_or_done = false;
        let ms_taken = request.at.elapsed().as_millis();
        self.work[request.worker_index].runtime_ms += ms_taken;

        println!("Received analysis from worker_index={}:", request.worker_index);

        let divide_over = data.status[request.worker_index].unstall.len() + 1;
        println!("Dividing {}s runtime over {} work items", ms_taken / 1000, divide_over);
        for index in data.status[request.worker_index]
            .unstall
            .iter()
            .map(|x| x.worker_index)
            .chain(once(request.worker_index))
        {
            self.work[index].virtual_runtime_ms += ms_taken / divide_over as u128;
        }

        let mut new_filters = FilterList::new();
        for filter in result.filters() {
            self.filters.add(filter.clone());
            new_filters.add(filter);
        }

        self.work[request.worker_index].apply_filters(&self.filters);
        let done = self.work[request.worker_index].done;

        if !new_filters.is_empty() || done || ms_taken >= 300_000 {
            let mut indexes_to_unstall = Vec::new();
            data.status[request.worker_index].unstall.retain_mut(|item| {
                if let Some(num) = item.num.checked_sub(1)
                    && !done
                {
                    println!("Work item #{} stalled for {num} more cycles", item.worker_index);
                    item.num = num;
                    true
                } else {
                    indexes_to_unstall.push(item.worker_index);
                    false
                }
            });

            let stalled_by = WorkItemStatus::compute_stalled(request.worker_index, &data.status);
            data.status[request.worker_index].stalled = stalled_by.is_some();
            self.work[request.worker_index].stalled_by = stalled_by;

            for item in indexes_to_unstall {
                let stalled_by = WorkItemStatus::compute_stalled(item, &data.status);
                data.status[item].stalled = stalled_by.is_some();
                self.work[item].stalled_by = stalled_by;
                println!(
                    "Updating stalled status to stalled={} for worker_index={item} ({:?}), because worker_index={} completed another item",
                    data.status[item].stalled,
                    self.work[item].counter.current(),
                    request.worker_index
                );
            }
        }

        let mut stall_updates = Vec::new();
        let mut new_unstall = Vec::new();
        if !data.status[request.worker_index].stalled {
            for (index, (work, status)) in self.work.iter_mut().zip(data.status.iter_mut()).enumerate() {
                if work.apply_filters(&new_filters) && index != request.worker_index {
                    work.apply_filters(&self.filters);
                    if work.done {
                        println!(
                            "worker_index={index} is done, because it matches a filter from worker_index={}; Unstalling all stalled items",
                            request.worker_index
                        );
                        for stall in status.unstall.drain(..) {
                            stall_updates.push(stall);
                        }
                    } else {
                        println!(
                            "Stalling worker_index={index}, because it matches a filter from worker_index={}",
                            request.worker_index
                        );

                        if !status.unstall.iter().any(|s| s.worker_index == request.worker_index) && !done {
                            work.stalled_by = Some(request.worker_index);
                            new_unstall.push(index);
                            status.stalled = true;

                            // We clear unstall, to prevent long dependency chains.
                            // If we have stalls A -> B -> C, it is possible that the encodings from A only match B and not C.
                            // So we need to clear the stalls from B when we stall it.
                            // If C does match encodings from A, it will be stalled directly by it.
                            stall_updates.append(&mut status.unstall);
                        } else {
                            println!("Not stalling, because that would create an infinite loop.");
                        }
                    }
                }
            }
        } else {
            println!("Worker was stalled while running, not updating stalls.")
        }

        let stalled_by = WorkItemStatus::compute_stalled(request.worker_index, &data.status);
        data.status[request.worker_index].stalled = stalled_by.is_some();
        self.work[request.worker_index].stalled_by = stalled_by;

        for item in stall_updates {
            let index = item.worker_index;
            let stalled_by = WorkItemStatus::compute_stalled(index, &data.status);
            data.status[index].stalled = stalled_by.is_some();
            self.work[index].stalled_by = stalled_by;
            println!(
                "Updating stalled status to stalled={} for worker_index={index} ({:?})",
                data.status[index].stalled,
                self.work[index].counter.current()
            );
        }

        let unstall = &mut data.status[request.worker_index].unstall;
        for index in new_unstall {
            if let Some(item) = unstall.iter_mut().find(|item| item.worker_index == index) {
                // Stalling an already stalled item makes it more likely we should keep it stalled
                item.num = 4;
            } else {
                unstall.push(Stall {
                    worker_index: index,
                    // We stall new items for the next 3 results
                    num: 3,
                });
            }
        }

        let artifact = self.work[request.worker_index].complete(
            request.counter.current(),
            &self.filters,
            &mut self.perfect_instrs_seen,
            result,
        );

        // TODO: Verify all stall dependencies, make sure we don't have an infinite loop

        artifact.map(|artifact| EnumerationArtifact {
            ms_taken,
            worker_index: request.worker_index,
            data: artifact,
        })
    }

    fn run<O: Oracle<A>>(oracle: &mut O, cache: &C, request: &Self::Request) -> Self::Result {
        request.run(request.worker_index, oracle, cache)
    }
}

impl<S: Scope> Enumeration<S> {
    pub fn create(num_work_items: usize, sampled_instrs: &[(Instruction, u128)], scope: S) -> Enumeration<S> {
        let total_weight: u128 = sampled_instrs.iter().map(|(_, w)| *w).sum();
        let mut work = Vec::new();

        let mut instrs = sampled_instrs;
        let mut weight_processed = 0;
        for index in 0..num_work_items {
            let goal_weight = if index >= num_work_items - 1 {
                total_weight
            } else {
                (total_weight * (index + 1) as u128) / (num_work_items as u128 + 1)
            };

            let from = &instrs[0].0;
            let mut item_weight = 0;
            let n = instrs
                .iter()
                .take_while(|(_, w)| {
                    item_weight += w;
                    item_weight + weight_processed < goal_weight
                })
                .count()
                .clamp(1, (instrs.len() - (num_work_items - index)).max(1));

            let to = if index >= num_work_items - 1 {
                None
            } else {
                instrs.get(n).map(|&(instr, _)| instr)
            };

            println!("[{index}] {from:X?}-{to:X?}: {n} (goal={goal_weight}/{total_weight})");

            work.push(EnumWorkItem::new(from, to));
            weight_processed += instrs[..n].iter().map(|(_, w)| w).sum::<u128>();
            instrs = if instrs.len() > n { &instrs[n..] } else { &[] };
        }

        Enumeration {
            work,
            filters: FilterList::new(),
            perfect_instrs_seen: HashSet::new(),
            runtime_ms: 0,
            scope,
        }
    }

    pub fn split_on_instr(&mut self, data: &mut EnumerationRuntimeData, instr: Instruction) -> Result<(), &'static str> {
        if let Some(index) = self
            .work
            .iter()
            .position(|work| instr >= work.from && work.to.as_ref().map(|to| &instr < to).unwrap_or(true))
        {
            let work = &mut self.work[index];
            if work.done {
                Err("corresponding work item is done")
            } else if work.counter.current() >= instr {
                Err("corresponding work item has already processed instruction")
            } else {
                let to = work.to;
                work.to = Some(instr);
                work.counter.set_end(Some(instr));

                let virtual_runtime_ms = self
                    .work
                    .iter()
                    .filter(|w| !w.done)
                    .map(|w| w.virtual_runtime_ms)
                    .min()
                    .unwrap();

                self.work.push(EnumWorkItem {
                    counter: InstructionCounter::range(&instr, to),
                    from: instr,
                    to,
                    unique_sequences: 0,
                    encodings_found: 0,
                    next: None,
                    fast_tunnel: false,
                    last_instructions: Vec::new(),
                    done: false,
                    num_errors: 0,
                    runtime_ms: 0,
                    virtual_runtime_ms,
                    stalled_by: None,
                });
                data.status.push(WorkItemStatus::default());

                Ok(())
            }
        } else {
            Err("instruction not found in work")
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EnumWorkItem {
    pub counter: InstructionCounter,
    from: Instruction,
    to: Option<Instruction>,
    pub unique_sequences: u128,
    pub encodings_found: u64,
    pub next: Option<Instruction>,
    pub fast_tunnel: bool,
    pub last_instructions: Vec<Instruction>,
    pub done: bool,
    pub num_errors: usize,
    pub runtime_ms: u128,
    pub virtual_runtime_ms: u128,

    /// The index of the work item that is stalling this work item.
    /// Use the EnumerationRuntimeData fields for computations.
    /// Only use this field for display purposes.
    pub stalled_by: Option<usize>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub enum EnumerationArtifactData<A: Arch, C: Computation> {
    Encoding(Encoding<A, C>),
    Failed(Instruction),
    Excluded(Instruction),
    InvalidInstructions(Range<Instruction>),
    MemoryErrorInstructions(Range<Instruction>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct EnumerationArtifact<A: Arch, C: Computation> {
    pub ms_taken: u128,
    pub data: EnumerationArtifactData<A, C>,

    #[serde(default)]
    pub worker_index: usize,
}

impl<S: Scope> AnalysisRequest<S> {
    pub fn new(
        worker_index: usize, counter: InstructionCounter, next_filtered_instruction: Option<Instruction>, scope: S,
    ) -> Self {
        AnalysisRequest {
            worker_index,
            counter,
            at: Instant::now(),
            next_filtered_instruction,
            scope,
        }
    }

    pub fn run<A: Arch, O: Oracle<A>>(
        &self, thread_id: usize, o: &mut O, cache: &impl EncodingAnalysisCache<A>,
    ) -> AnalysisResult<A> {
        info!("[{thread_id:02}]: analyzing {:X}", self.counter.current());
        AnalysisResult::run(&self.scope, o, cache, &self.counter, self.next_filtered_instruction)
    }
}

fn bust_single_bit_set_pattern(last_instructions: &[Instruction]) -> Option<Instruction> {
    if last_instructions.len() < 3 {
        None
    } else {
        let mut last_instructions = last_instructions.to_vec();
        last_instructions.sort();
        let mut last = None;
        let changed_bit_indices = last_instructions
            .windows(2)
            .map(|w| {
                if let &[before, after] = w {
                    trace!("{before:?} vs {after:?}");
                    if before.bit_len() == after.bit_len() {
                        (0..before.bit_len() - 1)
                            .fold(None, |acc, index| {
                                if before.nth_bit_from_right(index) == 1
                                    && after.nth_bit_from_right(index) == 0
                                    && before.nth_bit_from_right(index + 1) == 0
                                    && after.nth_bit_from_right(index + 1) == 1
                                {
                                    match acc {
                                        None => Some(Some(index)),
                                        Some(None) => Some(None),
                                        Some(Some(_)) => Some(None),
                                    }
                                } else {
                                    acc
                                }
                            })
                            .flatten()
                    } else {
                        None
                    }
                } else {
                    unreachable!()
                }
            })
            .rev()
            .take_while(|entry| match (entry, last) {
                (Some(index), None) => {
                    last = Some(*index);
                    true
                },
                (Some(index), Some(last_index)) if *index + 1 == last_index => {
                    last = Some(*index);
                    true
                },
                _ => false,
            })
            .flatten()
            .collect::<Vec<_>>();

        debug!("Changed bit indices: {changed_bit_indices:?}");

        if changed_bit_indices.len() >= 2 {
            let mut instr = *last_instructions.last().unwrap();
            for &index in changed_bit_indices.iter() {
                instr = instr.with_nth_bit_from_right(index, 1);
            }

            Some(instr)
        } else {
            None
        }
    }
}

impl EnumWorkItem {
    pub fn new(start: &Instruction, end: Option<Instruction>) -> Self {
        EnumWorkItem {
            from: *start,
            to: end,
            counter: InstructionCounter::range(start, end),
            unique_sequences: 0,
            encodings_found: 0,
            next: None,
            fast_tunnel: false,
            last_instructions: Vec::new(),
            done: false,
            num_errors: 0,
            runtime_ms: 0,
            virtual_runtime_ms: 0,
            stalled_by: None,
        }
    }

    pub fn from(&self) -> &Instruction {
        &self.from
    }

    pub fn to(&self) -> Option<&Instruction> {
        self.to.as_ref()
    }

    /// Applies the filters to the counter. Returns whether any filters were applicable.
    pub fn apply_filters(&mut self, filters: &FilterList) -> bool {
        if !self.done {
            let instr_before = self.counter.current();

            // Make sure we never change the end
            self.counter.set_end(self.to);

            if !self.counter.apply_filters_to_current(filters, false) {
                println!("Work item between {:?} and {:?} is done", self.from, self.to);
                self.done = true;
            }

            instr_before != self.counter.current()
        } else {
            false
        }
    }

    pub fn next_instr_is_out_of_sequence(&self) -> bool {
        self.next.is_some()
    }

    pub fn next_instruction(&self) -> Option<InstructionCounter> {
        if self.done {
            self.next.map(|instr| InstructionCounter::range(&instr, Some(instr)))
        } else {
            Some(if let Some(instr) = bust_single_bit_set_pattern(&self.last_instructions) {
                InstructionCounter::range(&instr, Some(instr))
            } else {
                self.next
                    .map(|instr| InstructionCounter::range(&instr, Some(instr)))
                    .unwrap_or_else(|| self.counter.clone())
            })
        }
    }

    pub fn complete<A: Arch>(
        &mut self, instruction: Instruction, filters: &FilterList, perfect_instrs_seen: &mut HashSet<Instruction>,
        result: AnalysisResult<A>,
    ) -> Option<EnumerationArtifactData<A, ()>> {
        self.last_instructions.push(instruction);
        if self.last_instructions.len() > 8 {
            self.last_instructions
                .drain(0..self.last_instructions.len() - 8)
                .for_each(drop);
        }

        let was_next = if self.next.as_ref().map(|next| next == &instruction).unwrap_or(false) {
            self.next = None;
            true
        } else {
            false
        };

        match &result {
            AnalysisResult::Ok(encoding) => println!("Completing {instruction:X} with {encoding}"),
            result => println!("Completing {instruction:X} with {result:X?}"),
        }

        match result {
            AnalysisResult::Ok(encoding) => {
                self.encodings_found += 1;

                if !was_next {
                    if let Some(perfect_instr) = encoding.best_instr() {
                        if !perfect_instrs_seen.contains(&perfect_instr) {
                            self.next = Some(perfect_instr);
                            perfect_instrs_seen.insert(perfect_instr);
                        }
                    }
                }

                for filter in encoding.filters() {
                    self.unique_sequences += 1 << filter.num_wildcard_bits();
                }

                self.done = !self.counter.apply_filters_to_current(filters, false);

                Some(EnumerationArtifactData::Encoding(encoding))
            },
            AnalysisResult::TooShort => {
                if !was_next {
                    self.done = !self.counter.extend(filters, self.fast_tunnel);
                }

                None
            },
            AnalysisResult::TooLong => {
                if !was_next {
                    self.done = !self.counter.reduce(filters, self.fast_tunnel);
                }

                None
            },
            AnalysisResult::SkipInvalidUntil {
                counter,
                done,
            } => {
                let next_instr = counter.current();
                self.num_errors = 0;
                self.fast_tunnel = false;

                if counter.end() == self.counter.end() {
                    self.counter = counter;

                    // Make sure we never change the end
                    self.counter.set_end(self.to);
                }

                self.done = done || !self.counter.apply_filters_to_current(filters, false);

                Some(EnumerationArtifactData::InvalidInstructions(instruction..next_instr))
            },
            AnalysisResult::SkipMemoryErrorUntil {
                counter,
                done,
            } => {
                let next_instr = counter.current();
                self.num_errors = 0;

                if counter.end() == self.counter.end() {
                    self.counter = counter;

                    // Make sure we never change the end
                    self.counter.set_end(self.to);
                }

                self.done = done || !self.counter.apply_filters_to_current(filters, false);

                Some(EnumerationArtifactData::MemoryErrorInstructions(instruction..next_instr))
            },
            AnalysisResult::SkipError => {
                self.num_errors += 1;

                self.fast_tunnel = true;
                if self.next.is_none() {
                    if self.num_errors >= 500_000 {
                        // If we have seen half a million errors, we might have a bad filter.
                        // Keep in mind that errors are encoding analysis failures, NOT excluded instructions or invalid instructions.
                        // To mitigate the bad filter, we just tunnel unconditionally until we find something that does not error.
                        self.done = !self.counter.tunnel_next_ignore_filters();
                    } else {
                        self.done = !self.counter.tunnel_next(filters, 200);
                    }
                } else {
                    self.next = None;
                }

                Some(EnumerationArtifactData::Failed(instruction))
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use liblisa::instr::Instruction;

    #[test]
    pub fn bust_single_bit_set_pattern_1() {
        let instrs = [
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x02, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x04, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x08, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x10, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x20, 0x00, 0x00, 0x00, 0xEE]),
        ];

        let bust = super::bust_single_bit_set_pattern(&instrs);
        assert_eq!(
            bust,
            Some(Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x3E, 0x00, 0x00, 0x00, 0xEE]))
        );
    }

    #[test]
    pub fn bust_single_bit_set_pattern_2() {
        let instrs = [
            Instruction::new(&[0xC5, 0xBF, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x00, 0xFF]),
            Instruction::new(&[0xC5, 0xBF, 0xC1]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x08, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x10, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x20, 0x00, 0x00, 0x00, 0xEE]),
        ];

        let bust = super::bust_single_bit_set_pattern(&instrs);
        assert_eq!(
            bust,
            Some(Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x38, 0x00, 0x00, 0x00, 0xEE]))
        );
    }

    #[test]
    pub fn bust_single_bit_set_pattern_3() {
        let instrs = [
            Instruction::new(&[0xC5, 0xBF, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x00, 0xFF]),
            Instruction::new(&[0xC5, 0xBF, 0xC1]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x08, 0x00, 0x00, 0x00, 0xEE]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x10, 0x00, 0x00, 0x00, 0xEF]),
            Instruction::new(&[0xC5, 0xBF, 0xC2, 0x0D, 0x20, 0x00, 0x00, 0x00, 0xF0]),
        ];

        let bust = super::bust_single_bit_set_pattern(&instrs);
        assert_eq!(bust, None);
    }

    #[test]
    pub fn bust_single_bit_set_pattern_4() {
        let instrs = [
            Instruction::new(&[0x40, 0x00, 0x05, 0x00, 0x00, 0x00, 0x80]),
            Instruction::new(&[0x40, 0x00, 0x15, 0x00, 0x00, 0x00, 0x80]),
            Instruction::new(&[0x40, 0x00, 0x05, 0x00, 0x00, 0x01, 0x00]),
            Instruction::new(&[0x40, 0x00, 0x15, 0x00, 0x00, 0x01, 0x00]),
            Instruction::new(&[0x40, 0x00, 0x05, 0x00, 0x00, 0x02, 0x00]),
            Instruction::new(&[0x40, 0x00, 0x15, 0x00, 0x00, 0x02, 0x00]),
            Instruction::new(&[0x40, 0x00, 0x05, 0x00, 0x00, 0x04, 0x00]),
            Instruction::new(&[0x40, 0x00, 0x15, 0x00, 0x00, 0x04, 0x00]),
        ];

        let bust = super::bust_single_bit_set_pattern(&instrs);
        assert_eq!(bust, Some(Instruction::new(&[0x40, 0x00, 0x15, 0x00, 0x00, 0x07, 0x80])));
    }

    #[test]
    pub fn bust_single_bit_set_pattern_perfect_instr_interference() {
        let instrs = [
            Instruction::new(&[0x00, 0x04, 0x01]),
            Instruction::new(&[0x00, 0x14, 0x01]),
            Instruction::new(&[0x00, 0x04, 0x02]),
            Instruction::new(&[0x00, 0x14, 0x02]),
            Instruction::new(&[0x00, 0x04, 0x04]),
            Instruction::new(&[0x00, 0x14, 0x04]),
        ];

        let bust = super::bust_single_bit_set_pattern(&instrs);
        assert_eq!(bust, Some(Instruction::new(&[0x00, 0x14, 0x07])));
    }
}
