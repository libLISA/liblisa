use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::iter::once;
use std::marker::PhantomData;
use std::time::Instant;

use liblisa::arch::{Arch, CpuState, Register};
use liblisa::encoding::dataflows::{
    AccessKind, AddrTerm, AddressComputation, Dest, Inputs, MemoryAccess, MemoryAccesses, Size, Source,
};
use liblisa::instr::Instruction;
use liblisa::oracle::{MappableArea, Oracle, OracleError};
use liblisa::semantics::{Computation, ARG_NAMES};
use liblisa::state::random::{RandomizationError, StateGen};
use liblisa::state::{Addr, Location, MemoryState, Permissions, SystemState};
use liblisa::value::Value;
use log::{debug, error, info, trace};
use rand::Rng;
use rand_xoshiro::rand_core::SeedableRng;
use rand_xoshiro::Xoshiro256PlusPlus;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::accesses::computation::{InferComputation, InferredComputation};

mod computation;

/// Error returned when [`MemoryAccessAnalysis`] fails.
#[derive(Error, Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub enum AccessAnalysisError<A: Arch> {
    #[error("Phantom")]
    #[serde(skip)]
    Phantom(PhantomData<A>),

    #[error("Unable to randomize: {}", .0)]
    Randomization(RandomizationError),

    #[error("Oracle gave an error: {}", .0)]
    OracleError(OracleError),

    #[error("Finding an input for memory access #{} failed: {}", .0, .1)]
    FindInputFailed(usize, FindInputError),

    #[error("Memory access #{} accesses unaccessable memory", .0)]
    UnaccessibleMemoryAccess(usize),

    #[error("Memory access #{} always overlaps with another memory access", .0)]
    OverlappingMemory(usize),

    #[error("Memory access #{} is not analyzable", .0)]
    AccessNotAnalyzable(usize),

    #[error("The instruction keeps causing CPU faults, no matter the inputs")]
    InstructionKeepsFaulting,

    #[error("Encountered a page fault on a page that is already readable and writeable")]
    MemoryErrorOnWritableRegion,

    #[error("Invalid instruction")]
    InvalidInstruction,

    #[error("Observation timeout")]
    ObservationTimeout,

    #[error("Instruction is emulated")]
    InstructionIsEmulated,

    #[error("This instruction accesses memory areas larger than 64 bytes")]
    MemoryAccessTooBig,

    #[error("Address calculation uses non-gpregs")]
    NonGpRegAccess,
}

impl<A: Arch> From<RandomizationError> for AccessAnalysisError<A> {
    fn from(e: RandomizationError) -> Self {
        AccessAnalysisError::Randomization(e)
    }
}

impl<A: Arch> From<OracleError> for AccessAnalysisError<A> {
    fn from(e: OracleError) -> Self {
        AccessAnalysisError::OracleError(e)
    }
}

/// Error returned in an [`AccessAnalysisError`] when no input registers can be found for an address calculation of a memory access.
#[derive(Debug, Error, Clone, Serialize, Deserialize)]
pub enum FindInputError {
    #[error("has_change failed: {}", .0)]
    HasInputFailed(OracleError),

    #[error("Modification failed: {}", .0)]
    RandomizationFailed(RandomizationError),

    #[error("Generic oracle error: {}", .0)]
    OracleError(OracleError),

    #[error("This instruction receives external inputs that we cannot observe")]
    UnobservableExternalInputs,
}

impl From<OracleError> for FindInputError {
    fn from(e: OracleError) -> Self {
        FindInputError::OracleError(e)
    }
}

impl From<RandomizationError> for FindInputError {
    fn from(e: RandomizationError) -> Self {
        FindInputError::RandomizationFailed(e)
    }
}

/// Infers the [`MemoryAccesses`](liblisa::encoding::dataflows::MemoryAccesses) for an [`Instruction`].
pub struct MemoryAccessAnalysis;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum SizeKind {
    After(u64),
}

#[derive(Debug, Copy, Clone)]
enum CheckSizeResult {
    Impossible,
    Failed,
    Increase,
    Ok,
}

trait OwnWhenNeeded<T>: AsRef<T> {
    fn into_owned(self) -> T;
}

impl<A: Arch> OwnWhenNeeded<SystemState<A>> for SystemState<A> {
    fn into_owned(self) -> SystemState<A> {
        self
    }
}

impl<A: Arch> OwnWhenNeeded<SystemState<A>> for &SystemState<A> {
    fn into_owned(self) -> SystemState<A> {
        self.clone()
    }
}

struct BaseGenerator<'a, A: Arch, M: MappableArea> {
    state_gen: &'a StateGen<'a, A, M>,
    bases: Vec<(SystemState<A>, Addr)>,
    oks: Vec<SystemState<A>>,
    unaddressable: Vec<SystemState<A>>,
    ignored: usize,
    ignored_overlapping: usize,
    directly_after_other_mapping: usize,
    other_mapping: Option<usize>,
    distinct_values: HashMap<A::GpReg, HashSet<u64>>,
    max_memory_spacing: i64,
    abort: bool,
    needs_trap_flag: bool,
}

impl<'a, A: Arch, M: MappableArea> BaseGenerator<'a, A, M> {
    pub fn new(state_gen: &'a StateGen<'a, A, M>) -> Self {
        BaseGenerator {
            state_gen,
            bases: Vec::new(),
            unaddressable: Vec::new(),
            oks: Vec::new(),
            ignored: 0,
            ignored_overlapping: 0,
            directly_after_other_mapping: 0,
            other_mapping: None,
            distinct_values: HashMap::new(),
            max_memory_spacing: 0,
            abort: false,
            needs_trap_flag: false,
        }
    }

    fn consider_base(
        &mut self, base_own: impl OwnWhenNeeded<SystemState<A>>, base_result: Result<SystemState<A>, OracleError>,
    ) -> bool {
        let base = base_own.as_ref();
        if let Ok(base_result) = &base_result {
            if base
                .cpu()
                .gpreg(A::PC)
                .wrapping_add(self.state_gen.accesses.instr.byte_len() as u64)
                != base_result.cpu().gpreg(A::PC)
            {
                self.needs_trap_flag = true;
            }
        }

        match base_result {
            Err(OracleError::MemoryAccess(addr)) => {
                // If the memory access occurs just past the end of a mapped page, the address is likely not the base address.
                // The first few bytes on the mapped page would not have caused a page fault.
                // We also ignore memory errors on already mapped pages, since those are ignored during early synthesis.
                // TODO: If access is located directly after another access we will completely ignore it now.
                if base.memory().areas().any(|area| {
                    ((area.start_addr().page::<A>() + 1).start_addr() == addr || addr.page::<A>() == area.start_addr().page())
                        && area.first_address_after() != area.start_addr().page::<A>().first_address_after_page()
                }) {
                    if self.ignored < 100 {
                        debug!("Ignoring access to 0x{addr:X} from: {base:?}");
                    }
                    self.ignored += 1;

                    if base.memory().areas().any(|area| addr.page::<A>() == area.start_addr().page()) {
                        self.ignored_overlapping += 1;
                    }

                    false
                } else {
                    if let Some(index) = base
                        .memory()
                        .areas()
                        .position(|area| area.first_address_after() == area.start_addr().page::<A>().first_address_after_page())
                    {
                        if self.other_mapping == Some(index) {
                            self.directly_after_other_mapping += 1;
                        } else {
                            self.directly_after_other_mapping = 1;
                            self.other_mapping = Some(index);
                        }
                    }

                    for reg in A::iter_gpregs() {
                        self.distinct_values.entry(reg).or_default().insert(base.cpu().gpreg(reg));
                    }

                    let spacing = base
                        .memory()
                        .iter()
                        .enumerate()
                        .flat_map(|(index, (existing_addr, ..))| {
                            base.memory()
                                .iter()
                                .skip(index + 1)
                                .map(|&(addr2, ..)| ((*existing_addr - addr2) as i64).checked_abs().unwrap_or(i64::MAX))
                                .min()
                        })
                        .chain(
                            base.memory()
                                .iter()
                                .map(|&(existing_addr, ..)| ((existing_addr - addr) as i64).checked_abs().unwrap_or(i64::MAX)),
                        )
                        .min()
                        .unwrap_or(0);

                    self.max_memory_spacing = spacing.max(self.max_memory_spacing);

                    self.bases.push((base_own.into_owned(), addr));
                    true
                }
            },
            Err(OracleError::GeneralFault) => {
                // We cannot increment `ignored` here, because UnaddressableMemory might be caused by alignment issues.
                // This means that we can see this error even if we have correctly mapped all memory accesses.
                // We should therefore rely on actual page faults to detect memory accesses.
                // If an instruction is *only* accessing unadressable memory, we won't increment `self.oks` and MA analysis will still fail.

                self.unaddressable.push(base_own.into_owned());
                false
            },
            Err(OracleError::Timeout) => {
                self.abort = true;
                false
            },
            Err(OracleError::MultipleInstructionsExecuted) => {
                self.needs_trap_flag = true;
                false
            },
            _ => {
                self.oks.push(base_own.into_owned());
                true
            },
        }
    }

    pub fn gen<O: Oracle<A>, R: Rng>(&mut self, oracle: &mut O, rng: &mut R) -> Result<(), AccessAnalysisError<A>> {
        let ps = oracle.page_size();
        #[derive(Debug)]
        struct MemoryGroup {
            fronts: Vec<usize>,
            backs: Vec<usize>,
        }

        let mut by_input = HashMap::new();
        for (index, access) in self.state_gen.accesses.iter().enumerate() {
            let c = access.calculation;
            by_input
                .entry(&access.inputs)
                .or_insert_with(HashMap::new)
                .entry(c.terms)
                .or_insert_with(Vec::new)
                .push((index, access));
        }

        let mut memory_groups = Vec::new();
        for (_, mut input_group) in by_input.drain() {
            let mut fronts = Vec::new();
            let mut backs = Vec::new();

            for (_, mut group) in input_group.drain() {
                group.sort_by_key(|(_, access)| access.calculation.offset);

                let mut lowest = i64::MIN;
                for (index, access) in group.iter() {
                    let v = access.calculation.offset;
                    if lowest + (ps as i64) < v {
                        fronts.push(*index);
                        lowest = v;
                    }
                }

                let mut highest = i64::MAX;
                for (index, access) in group.iter().rev() {
                    let v = access.calculation.offset;
                    if v < highest - ps as i64 {
                        backs.push(*index);
                        highest = v;
                    }
                }
            }

            memory_groups.push(MemoryGroup {
                fronts,
                backs,
            });
        }

        let relocators = self
            .state_gen
            .accesses
            .iter()
            .map(|access| Relocatable::new(self.state_gen, access.alignment, &access.inputs, &access.calculation))
            .collect::<Vec<_>>();

        let mut needs_sanity_check = 10;
        let state_gen = self.state_gen.clone();

        let new_bases = (0..100).flat_map(|_| state_gen.randomize_new(rng).ok());
        for (base, result) in oracle.batch_observe_iter(new_bases.into_iter()) {
            self.consider_base(&base, result);
        }

        self.sanity_check(rng, &mut needs_sanity_check, oracle)?;

        info!("Memory groups: {:?}", memory_groups);
        let mut unsatisfiable = 0;
        for n in 0..400 {
            debug!(
                "Generated {} bases so far ({} iterations)... (max_memory_spacing={})",
                self.bases.len(),
                n,
                self.max_memory_spacing
            );

            // Batch generation in sets of 2000, to use the oracle more efficiently
            // TODO: Do this on the fly once we remove the oracle access during random state generation
            let mut return_error = None;
            let mut unsatisfiable_index = None;
            let state_gen = self.state_gen.clone();
            let new_bases = (0..2000).flat_map(|_| match state_gen.randomize_new(rng) {
                Ok(base) => Some(base),
                Err(RandomizationError::UnmappableFixedOffset(index)) => {
                    return_error = Some(Err(AccessAnalysisError::UnaccessibleMemoryAccess(index)));
                    None
                },
                Err(RandomizationError::Unsatisfiable(index)) => {
                    debug!("Base generation failed: access {} is unsatisfiable", index);
                    unsatisfiable += 1;
                    unsatisfiable_index = Some(index);

                    None
                },
                Err(e) => {
                    debug!("Base generation failed: {:?}", e);
                    None
                },
            });

            #[allow(clippy::needless_collect)]
            let bases_considered = oracle
                .batch_observe_iter(new_bases.into_iter())
                .map(|(base, result)| {
                    let considered = self.consider_base(&base, result);
                    (base, considered)
                })
                .filter(|(_, considered)| *considered)
                .collect::<Vec<_>>();

            if let Some(index) = unsatisfiable_index {
                if unsatisfiable >= 10_000
                    && self.oks.is_empty()
                    && self.bases.is_empty()
                    && self.ignored == 0
                    && self.unaddressable.is_empty()
                {
                    return Err(AccessAnalysisError::Randomization(RandomizationError::Unsatisfiable(index)));
                }
            }

            if let Some(err) = return_error {
                return err;
            }

            if self.abort {
                return Err(AccessAnalysisError::ObservationTimeout);
            }

            if needs_sanity_check > 0 && self.bases.len() >= 50 {
                self.sanity_check(rng, &mut needs_sanity_check, oracle)?;
            }

            let mut extra_bases_to_consider = Vec::new();

            let mut fronts_generated = 0;
            let mut backs_generated = 0;
            let mut fronts_by_group = vec![0; memory_groups.len()];
            let mut backs_by_group = vec![0; memory_groups.len()];
            for (mut state, _) in bases_considered.into_iter() {
                // Now we try to generate a state where accesses are placed at the start (1/3) or the end of a page (1/3).
                trace!("");
                for (group_index, group) in memory_groups.iter().enumerate() {
                    match rng.gen_range(0u8..3) {
                        // Leave the memory access alone
                        0 => (),
                        // Relocate a front to the start of a page
                        1 => {
                            let index = rng.gen_range(0..group.fronts.len());
                            let index = group.fronts[index];
                            let relocator = &relocators[index];

                            // Put this memory at the start of the page
                            let addr = state.memory().addr(index);
                            let target = addr.align_to_page_start(A::PAGE_BITS);
                            if addr != target {
                                if let Some(new_state) = relocator.relocate(&state, addr, target)? {
                                    fronts_generated += 1;
                                    fronts_by_group[group_index] += 1;
                                    extra_bases_to_consider.push(new_state.clone());
                                    state = new_state
                                }
                            }
                        },
                        // Relocate a back to the end of the page
                        2 => {
                            let index = rng.gen_range(0..group.backs.len());
                            let index = group.backs[index];
                            let access = &self.state_gen.accesses[index];
                            let relocator = &relocators[index];

                            // Put this memory at the end of the page
                            let addr = state.memory().addr(index);
                            let target = addr.page::<A>().first_address_after_page() - access.size.end;
                            if addr != target {
                                if let Some(new_state) = relocator.relocate(&state, addr, target)? {
                                    backs_generated += 1;
                                    backs_by_group[group_index] += 1;
                                    extra_bases_to_consider.push(new_state.clone());
                                    state = new_state;
                                }
                            }
                        },
                        _ => unreachable!(),
                    }
                }
            }

            let len = self.bases.len();
            for (base, result) in oracle.batch_observe_iter(extra_bases_to_consider.iter()) {
                self.consider_base(base, result);

                if self.abort {
                    return Err(AccessAnalysisError::ObservationTimeout);
                }
            }

            let num_considered = self.bases.len() - len;
            debug!(
                "Fronts generated: {fronts_generated} in {fronts_by_group:?}; Backs generated: {backs_generated} in {backs_by_group:?}; Considered: {num_considered}; Groups: {memory_groups:?}"
            );

            if needs_sanity_check > 0 && self.bases.len() >= 50 {
                self.sanity_check(rng, &mut needs_sanity_check, oracle)?;
            }

            // If memory accesses are closer together, we need more bases.
            // It is harder to generate useful states when the next memory access is close to an existing memory access.
            // Therefore, if we have found some memory access that is really close to an existing memory access,
            // we should do more work to make sure there is no memory access between the one we found and the existing one.
            let bases_needed = match self.max_memory_spacing {
                x if x < 32 => 10_000,
                x if x < 64 => 5000,
                x if x < 2 * ps as i64 => 3000,
                _ => 2000,
            } + self.directly_after_other_mapping / 2;
            // TODO: above was self.directly_after_other_mapping * 2. Can we leave the / 2? If not, please document which instructions need it.

            // We need to get a good selection of randomized states.
            // Most importantly, we need to have cases with many different values for registers.
            // This is necessary to be able to correctly synthesize the address expression.
            let enough_oks = self.ignored == 0 && self.oks.len() >= 2500 && self.bases.is_empty();
            let enough_bases = self.bases.len() >= bases_needed
                && A::iter_gpregs()
                    .all(|reg| reg.is_flags() || self.distinct_values.get(&reg).map(|set| set.len() > 500).unwrap_or(false));
            let enough_unaddressable = self.unaddressable.len() >= (self.oks.len() * 1000).max(10_000) && self.ignored == 0;
            // If less than one in 50k observations produces a useful memory access, we just give up.
            let enough_ignored = self.bases.is_empty() && self.oks.is_empty() && self.ignored >= 50_000;
            if enough_oks || enough_bases || enough_unaddressable || enough_ignored {
                break;
            }
        }

        info!(
            "{} bases generated, {} ok, {} ignored",
            self.bases.len(),
            self.oks.len(),
            self.ignored
        );

        Ok(())
    }

    fn sanity_check<O: Oracle<A>, R: Rng>(
        &mut self, rng: &mut R, needs_sanity_check: &mut usize, oracle: &mut O,
    ) -> Result<(), AccessAnalysisError<A>> {
        let sanity_checks = self
            .bases
            .iter()
            .flat_map(|(base, addr)| {
                let mut new_base = self.state_gen.randomize_new(rng).unwrap();
                for reg in A::iter_gpregs().map(A::reg) {
                    new_base.set_reg(reg, base.cpu().reg(reg));
                }

                if self.state_gen.adapt(&mut new_base, false) {
                    Some((new_base, addr))
                } else {
                    None
                }
            })
            .skip(10 - *needs_sanity_check)
            .take(*needs_sanity_check);
        for ((state_in, addr), state_out) in oracle.batch_observe_iter(sanity_checks) {
            *needs_sanity_check -= 1;
            match state_out {
                Err(OracleError::MemoryAccess(new_addr)) if &new_addr == addr => (),
                _ => {
                    debug!("Sanity check failed: {state_out:X?} vs expected addr {addr:X?} state_in={state_in:X?}");
                    return Err(AccessAnalysisError::NonGpRegAccess);
                },
            }
        }
        info!("Sanity check OK");
        // Check a few bases to make sure accesses don't change when altering non-gpreg registers

        Ok(())
    }
}

struct Relocatable<'a, A: Arch, M: MappableArea> {
    state_gen: &'a StateGen<'a, A, M>,
    alignment: usize,
    inputs: &'a Inputs<A>,
    calculation: &'a AddressComputation,
    relocation_loc: Option<Location<A>>,
    shift: AddrTerm,
}

impl<'a, A: Arch, M: MappableArea> Relocatable<'a, A, M> {
    pub fn new(
        state_gen: &'a StateGen<'a, A, M>, alignment: usize, inputs: &'a Inputs<A>, calculation: &'a AddressComputation,
    ) -> Self {
        let (relocation_loc, shift) = if inputs.is_empty() {
            (None, AddrTerm::default())
        } else {
            // We choose a single input to alter.
            // If possible, we choose an input with a scale of 1.
            // If there are multiple inputs with a scale of 1, we choose the input that occurs the least in other memory accesses.
            // If there is no input with a scale of 1, there is only 1 input. We must choose that input.
            let (relocation_loc, relocation_shift) = inputs
                .iter()
                .zip(calculation.terms.iter())
                .min_by_key(|(source, &shift)| {
                    if shift.minimum_step_size() == 1 {
                        state_gen.accesses.iter().filter(|a| a.inputs.contains(source)).count()
                    } else {
                        usize::MAX
                    }
                })
                .unwrap();

            let relocation_loc = Location::from((*relocation_loc).unwrap_dest());
            (Some(relocation_loc), *relocation_shift)
        };

        Relocatable {
            state_gen,
            alignment,
            inputs,
            calculation,
            relocation_loc,
            shift,
        }
    }

    pub fn can_relocate(&self) -> bool {
        self.relocation_loc.is_some()
    }

    pub fn can_relocate_with_offset_before_page(&self, offset: u64) -> bool {
        if offset % self.alignment as u64 != 0 {
            return false;
        }

        for access in self.state_gen.accesses.iter() {
            if self.inputs == &access.inputs {
                if let Some(const_offset) = access.calculation.constant_offset_with(self.calculation) {
                    let relocate_to = Addr::new((123 << A::PAGE_BITS) - offset);
                    let addr = relocate_to + const_offset as u64;
                    if addr.into_area(access.size.end).crosses_page_bounds(A::PAGE_BITS)
                        || addr.as_u64() % access.alignment as u64 != 0
                    {
                        return false;
                    }
                }
            }
        }

        true
    }

    pub fn relocate(
        &self, state: &SystemState<A>, current_addr: Addr, target_addr: Addr,
    ) -> Result<Option<SystemState<A>>, AccessAnalysisError<A>> {
        if let Some(relocation_loc) = &self.relocation_loc {
            let mut state = state.clone();
            let base_value = if let Value::Num(n) = state.get_location(relocation_loc).unwrap() {
                n
            } else {
                panic!("General-purpose register does not contain a number?");
            };

            if let Some(new_value) = self
                .shift
                .compute_relocation(base_value, current_addr.as_u64(), target_addr.as_u64())
            {
                state.set_location(relocation_loc, Value::Num(new_value));

                trace!("Adapting state: {:?}", state);
                Ok(if self.state_gen.adapt(&mut state, false) {
                    Some(state)
                } else {
                    trace!("Failed to adapt {state:?}");
                    None
                })
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }
}

impl MemoryAccessAnalysis {
    /// Finds a base state where there is at least 1 page between this memory access and any other memory access
    fn find_size_base<A: Arch, O: Oracle<A>, R: Rng>(
        rng: &mut R, o: &mut O, state_gen: &StateGen<'_, A, O::MappableArea>, inputs: &Inputs<A>,
        calculation: &AddressComputation, before: bool,
    ) -> Result<Option<(SystemState<A>, Addr)>, RandomizationError> {
        let ps = o.page_size();
        let mappable = o.mappable_area();
        let mut num_observations = 0;
        let start = Instant::now();
        for _ in 0..10_000 {
            let state = state_gen.randomize_new(rng)?;
            let expected = Addr::new(calculation.compute(inputs, &state));

            if expected >= Addr::new(4u64 << 12) // TODO: Why exactly this value?
                && mappable.can_map(expected)
                && (mappable.can_map((expected.page::<A>() + 1).start_addr()) || before)
                && (mappable.can_map(expected - ps) || !before)
                && state.memory().iter().all(|(addr, _, _)| {
                    let p_mapped = addr.page::<A>();
                    let p_new = expected.page();

                    p_mapped != p_new && if before {
                        (p_new - 1) != p_mapped
                    } else {
                        (p_new + 1) != p_mapped
                    }
                })
            {
                let s = SystemState::new(
                    state.cpu().clone(),
                    MemoryState::new(state.memory().iter().cloned().chain(once((
                        expected.align_to_page_start(A::PAGE_BITS),
                        Permissions::ReadWrite,
                        vec![0],
                    )))),
                );

                let [(_, result), (_, second_result)] = o.batch_observe([&state, &s]);

                num_observations += 1;
                match result {
                    Err(OracleError::MemoryAccess(new_addr)) if new_addr == expected => match second_result {
                        Ok(_)
                        | Err(OracleError::MemoryAccess(_))
                        | Err(OracleError::ComputationError)
                        | Err(OracleError::InvalidInstruction) => {
                            debug!(
                                "Needed {} observations to check in {}us / {}ns per observation",
                                num_observations,
                                start.elapsed().as_micros(),
                                start.elapsed().as_nanos() / num_observations
                            );
                            return Ok(Some((state, new_addr)));
                        },
                        _ => {},
                    },
                    Err(e @ (OracleError::MultipleInstructionsExecuted | OracleError::Timeout)) => {
                        return Err(RandomizationError::OracleError(e))
                    },
                    _ => {},
                }
            }
        }

        debug!("Unable to find size check base in {num_observations} observations");

        Ok(None)
    }

    fn check_size<A: Arch, O: Oracle<A>>(
        o: &mut O, base: SystemState<A>, base_addr: Addr, relocator: &Relocatable<'_, A, O::MappableArea>, size: SizeKind,
    ) -> Result<CheckSizeResult, AccessAnalysisError<A>> {
        if relocator.inputs.is_empty() {
            return Ok(CheckSizeResult::Impossible);
        }

        debug!("Choosing 0x{:X} as base address to check size", base_addr);
        let page = base_addr.page::<A>();
        let page_start = page.start_addr();
        let page_end = page.first_address_after_page();

        debug!("Page start: 0x{page_start:X}; Page end: 0x{page_end:X}");

        let (target_addr, expected_access) = match size {
            SizeKind::After(n) => (page_end - n, page_end),
        };

        debug!("Checking offset={size:?} at target address 0x{target_addr:X}; expected access: {expected_access:X}");
        Ok(if let Some(relocated) = relocator.relocate(&base, base_addr, target_addr)? {
            // TODO: Should we make sure we're not creating overlapping mappings?
            // if relocated.memory().iter().any(|(addr, _, _)| addr.page() == page) {
            //     // We cannot double-map the page
            //     debug!("Relocation will map multiple items to the same page");
            //     return Ok(CheckSizeResult::Failed);
            // }

            // Map the page on which the access is occurring
            // TODO: What if this wraps around?
            let (area_start, area_size) = match size {
                SizeKind::After(n) => (page_end - n, usize::try_from(n).unwrap()),
                // let area_start = target_addr.min(expected_access);
                // let area_end = target_addr.max(expected_access);
                // assert!(area_end >= area_start);

                // (area_start, (area_end - area_start) as usize)
            };

            debug!("Area: 0x{area_start:X}:+{area_size}");
            let mem = MemoryState::new(relocated.memory().iter().cloned().chain(once((
                area_start,
                Permissions::ReadWrite,
                vec![0; area_size],
            ))));
            let relocated = relocated.with_new_memory(base.memory().len() + 1, 1, mem);

            // We cannot map ReadWrite & executable on the same page
            let (ex_addr, _, ex_data) = relocated.memory().get(0);
            if ex_addr.page::<A>() == page || (*ex_addr + ex_data.len() as u64).page::<A>() == page {
                return Ok(CheckSizeResult::Failed);
            }

            debug!("Final state that we're observing: {:?}", relocated);
            let result = o.observe(&relocated);
            debug!("Observation result: {result:X?}");

            match result {
                // Memory access at the end of the page, the memory is bigger
                Err(OracleError::MemoryAccess(addr)) if addr == expected_access => CheckSizeResult::Increase,

                // No memory error, we must have reached the max
                Ok(_) | Err(OracleError::ComputationError) | Err(OracleError::MemoryAccess(_)) => CheckSizeResult::Ok,

                // May be alignment instead of negative memory, so we can't return Ok/Increase
                Err(OracleError::GeneralFault) => CheckSizeResult::Failed,
                Err(e @ (OracleError::MultipleInstructionsExecuted | OracleError::Timeout)) => {
                    return Err(AccessAnalysisError::Randomization(RandomizationError::OracleError(e)))
                },

                Err(err) => {
                    // TODO: Handle alignment?
                    error!("Unexpected oracle error: {}", err);
                    CheckSizeResult::Impossible
                },
            }
        } else {
            debug!("Unable to relocate");
            CheckSizeResult::Failed
        })
    }

    fn infer_alignment<A: Arch, O: Oracle<A>>(
        o: &mut O, inputs: &Inputs<A>, calculation: &AddressComputation, bases: &[(SystemState<A>, Addr)],
        unaddressable: &[SystemState<A>], max_memory_size: u64,
    ) -> usize {
        let mut alignments_ok: u128 = 0;
        let mut alignments_nok: u128 = 0;
        let mappable = o.mappable_area();

        for (_, addr) in bases.iter() {
            let alignment = addr.trailing_zeros();
            alignments_ok |= 1 << alignment;
        }

        for base in unaddressable.iter() {
            let addr = Addr::new(calculation.compute(inputs, base));

            // TODO: Check exact memory size
            if mappable.can_map(addr) && mappable.can_map(addr + max_memory_size) {
                trace!("Nok = {:X} for {:X?}", addr, base);
                let alignment = addr.trailing_zeros();
                alignments_nok |= 1 << alignment;
            }
        }

        let alignments_ok = alignments_ok & 0xff;

        // alignments_nok will overapproximate:
        // It is assumed that all general faults are caused by alignment issues.
        // That's obviously not necessarily true.
        // So we might have more bits that are considered NOK.
        // To correct for this, we restrict the NOK bits to bits that we haven't confirmed OK.
        let mut alignments_nok = alignments_nok & 0xff & !alignments_ok;

        // Handle cases where we might not be able to observe all addresses.
        // For example, if the computation is x*2+20 we will never see (alignments_ok & 0b1) == 1.
        if inputs.len() == 1 && calculation.terms[0].offset_is_valid(calculation.offset) {
            let minimum_forced_alignment = calculation.terms[0].minimum_step_size();
            let mask = (1u128 << (minimum_forced_alignment - 1)) - 1;

            // We don't want to insert NOKs where none are to be found.
            // Only extend if there are already bits set outside the mask.
            if alignments_nok & !mask != 0 {
                debug!("Extending alignment_nok={alignments_nok:08b} with: {:08b}", mask & 0xff);
                alignments_nok |= mask;
            }
        }

        debug!("alignment  ok: {:08b}", alignments_ok & 0xff);
        debug!("alignment nok: {:08b}", alignments_nok & 0xff);

        match (alignments_ok & 0xff, alignments_nok & 0xff) {
            (0b11111110, 0b00000001) => 2,
            (0b11111100, 0b00000011) => 4,
            (0b11111000, 0b00000111) => 8,
            (0b11110000, 0b00001111) => 16,
            (0b11100000, 0b00011111) => 32,
            (0b11000000, 0b00111111) => 64,
            (0b10000000, 0b01111111) => 128,
            _ => 1,
        }
    }

    pub fn infer_quick<A: Arch, O: Oracle<A>>(
        o: &mut O, instr: &Instruction,
    ) -> Result<MemoryAccesses<A>, AccessAnalysisError<A>> {
        info!("Inferring accesses for {instr:X}");
        let mappable = o.mappable_area();
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let mut accesses: MemoryAccesses<A> = MemoryAccesses {
            instr: *instr,
            memory: vec![MemoryAccess {
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(A::reg(A::PC), Size::qword()))]),
                kind: AccessKind::Executable,
                size: instr.byte_len() as u64..instr.byte_len() as u64,
                calculation: AddressComputation::unscaled_sum(1),
                alignment: 1,
            }],
            use_trap_flag: true,
        };

        let mut needs_trap_flag = {
            let var = std::env::var("LIBLISA_FORCE_TRAP_FLAG").unwrap_or(String::from("0"));
            var != "0" && var != "no" && var != "off" && var != "false"
        };

        let skip_careful_observe = {
            let var = std::env::var("LIBLISA_SKIP_CAREFUL_OBSERVE").unwrap_or(String::from("0"));
            var != "0" && var != "no" && var != "off" && var != "false"
        };

        // First we use page faults to find most (if not all) memory accesses, because page faults are relatively fast
        loop {
            let start = Instant::now();
            info!("Generating bases...");
            info!("Accesses: {}", accesses);

            let state_gen = StateGen::new(&accesses, &mappable)?;
            let mut base_gen = BaseGenerator::new(&state_gen);
            base_gen.gen(o, &mut rng)?;
            let bases = base_gen.bases;
            let oks = base_gen.oks;
            let unaddressable = base_gen.unaddressable;
            info!(
                "{} bases generated in {}ms, {} ok, {} ignored, {} unaddressable",
                bases.len(),
                start.elapsed().as_millis(),
                oks.len(),
                base_gen.ignored,
                unaddressable.len()
            );

            needs_trap_flag |= base_gen.needs_trap_flag;
            info!("needs_trap_flag |= {} (= {needs_trap_flag})", base_gen.needs_trap_flag);

            if bases.is_empty() {
                // TODO: Add explanation as to why we're not able to break when we ignored one or more memory accesses
                if oks.len() >= 1_000 && base_gen.ignored == 0 {
                    break;
                } else {
                    error!(
                        "No useful bases encountered: {} bases generated, {} ignored, {} unaddressable; Accesses: {:X?}",
                        oks.len(),
                        base_gen.ignored,
                        unaddressable.len(),
                        accesses
                    );
                    return Err(AccessAnalysisError::Randomization(RandomizationError::Unsatisfiable(
                        if base_gen.ignored == 0 && unaddressable.is_empty() {
                            // In this case we were not able to generate any state, so we were not able to see any memory access.
                            // We have an unsatisfiable state because of the last memory access, not a new one.
                            accesses.len() - 1
                        } else {
                            accesses.len()
                        },
                    )));
                }
            } else {
                info!("Memory access found");
                for (base, addr) in bases.iter().take(3) {
                    debug!("EXAMPLE -- accesses 0x{:X}: {:X?}", addr, base);
                }

                // Check a few bases to make sure accesses don't change when altering non-gpreg registers
                let sanity_checks = bases
                    .iter()
                    .flat_map(|(base, addr)| {
                        let mut new_base = state_gen.randomize_new(&mut rng).unwrap();
                        for reg in A::iter_gpregs().map(A::reg) {
                            new_base.set_reg(reg, base.cpu().reg(reg));
                        }

                        if state_gen.adapt(&mut new_base, false) {
                            Some((new_base, addr))
                        } else {
                            None
                        }
                    })
                    .take(10);

                for ((state_in, addr), state_out) in o.batch_observe_iter(sanity_checks) {
                    match state_out {
                        Err(OracleError::MemoryAccess(new_addr)) if &new_addr == addr => (),
                        _ => {
                            debug!("Sanity check failed: {state_out:X?} vs expected addr {addr:X?} state_in={state_in:X?}");
                            return Err(AccessAnalysisError::NonGpRegAccess);
                        },
                    }
                }

                debug!(
                    "directly_after_other_mapping = {}, len = {}",
                    base_gen.directly_after_other_mapping,
                    bases.len()
                );
                let size_increase = if accesses.len() > 1 {
                    bases
                        .iter()
                        .map(|(base, addr)| *addr - base.memory().get(base.memory().len() - 1).0)
                        .max()
                } else {
                    None
                };

                let mappable = o.mappable_area();
                let more_memory_accesses_expected = o.batch_observe_iter(bases.iter().filter(|(_, addr)| mappable.can_map(*addr)).take(100).map(|(base, addr)| {
                    let state = SystemState::new(
                        base.cpu().clone(),
                        MemoryState::new(base.memory().iter().cloned()
                            .chain(once((*addr, Permissions::Read, vec! [ 0 ]))))
                    );
                    (state, *addr)
                })).any(|((_, addr), state_out)| matches!(state_out, Err(OracleError::MemoryAccess(other_addr)) if other_addr != addr));

                info!("More memory accesses expected: {more_memory_accesses_expected:?}");

                let infer = InferComputation {
                    directly_after_other_mapping: base_gen.directly_after_other_mapping,
                    other_mapping: base_gen.other_mapping,
                    bases,
                    accesses: &accesses,
                    state_gen: &state_gen,
                    oks,
                    more_memory_accesses_expected,
                };

                let InferredComputation {
                    inputs,
                    calculation,
                    bases,
                } = match infer.infer_computation(o, &mut rng) {
                    Ok(v) => v,
                    err => {
                        if let Some(size_increase) = size_increase {
                            info!("size_increase = {:X?}", size_increase);
                            if size_increase < 0x800 {
                                info!(
                                    "Found no memory access: {:?} -- but we can fix this by increasing the size of the last memory access by 0x{:X}",
                                    err, size_increase
                                );
                                let access = &mut accesses.memory.last_mut().unwrap();
                                let size = &mut access.size;
                                let new_size = size.end + size_increase;
                                let new_size = if new_size % access.alignment as u64 != 0 {
                                    (new_size | (access.alignment as u64 - 1)) + 1
                                } else {
                                    new_size
                                };

                                size.end = new_size;
                                size.start = new_size;
                                continue;
                            }
                        }

                        err?
                    },
                };

                info!("Identified inputs as: {:?}", inputs);
                info!(
                    "Identified calculation as: {}",
                    calculation.display(&ARG_NAMES[..inputs.len()])
                );

                let max_limit = accesses
                    .memory
                    .iter()
                    .filter(|access| access.inputs == inputs)
                    .flat_map(|access| calculation.constant_offset_with(&access.calculation))
                    .filter(|&n| n > 0)
                    .min()
                    .unwrap_or(256)
                    .min(256) as u64;

                info!("Size limit is {}", max_limit);

                let alignment = Self::infer_alignment(o, &inputs, &calculation, &bases, &unaddressable, max_limit);
                info!("Alignment: {}", alignment);

                let s = Instant::now();
                let (min_size, max_size) = if inputs.len() == 1 && calculation.terms[0].minimum_step_size() != 1 {
                    // We cannot increment / decrement the memory access in single-byte increments
                    info!("The only available input has a scale factor");
                    (1, max_limit)
                } else {
                    let mut num_fails = 0;
                    let mut max_size = 1;
                    let mut min_size = 1;
                    let relocator = Relocatable::new(&state_gen, alignment, &inputs, &calculation);
                    let mut bases: Vec<(SystemState<A>, Addr)> = Vec::new();
                    if relocator.can_relocate() {
                        loop {
                            let size = SizeKind::After(max_size);
                            let base = if let Some(base) = bases.get(num_fails) {
                                Some(base.clone())
                            } else if let Some((base, base_addr)) = Self::find_size_base(
                                &mut rng,
                                o,
                                relocator.state_gen,
                                relocator.inputs,
                                relocator.calculation,
                                false,
                            )? {
                                bases.push((base.clone(), base_addr));
                                Some((base, base_addr))
                            } else {
                                None
                            };

                            let result = if let Some((base, base_addr)) = base {
                                Self::check_size(o, base, base_addr, &relocator, size)?
                            } else {
                                CheckSizeResult::Impossible
                            };

                            debug!("Size check result: {:?}", result);
                            match result {
                                CheckSizeResult::Impossible => {
                                    max_size = max_limit;
                                    break;
                                },
                                CheckSizeResult::Failed => {
                                    if num_fails == 0 && !relocator.can_relocate_with_offset_before_page(max_size) {
                                        debug!("We won't be able to ever observe allocations at PAGE-{max_size}, skipping");
                                        max_size += 1;
                                    } else {
                                        // Try again
                                        num_fails += 1;
                                        if num_fails >= 300 {
                                            num_fails = 0;
                                            max_size += 1;

                                            if max_size >= max_limit {
                                                // We will determine the actual size during careful observation
                                                break;
                                            }
                                        }
                                    }
                                },
                                CheckSizeResult::Increase => {
                                    num_fails = 0;
                                    max_size += 1;
                                    min_size = max_size;
                                },
                                CheckSizeResult::Ok => break,
                            }
                        }
                    } else {
                        max_size = max_limit;
                    }

                    (min_size, max_size)
                };

                info!("Found size in {}ms", s.elapsed().as_millis());

                if inputs.is_empty() {
                    let addr = Addr::new(calculation.compute(&inputs, &bases[0].0));
                    let can_map = o.mappable_area().can_map(addr);
                    info!(
                        "Memory location is fixed, checking if we can map 0x{:X} = {:?}",
                        addr, can_map
                    );
                    if !can_map {
                        // The memory access maps to a fixed location that we cannot map.
                        return Err(AccessAnalysisError::UnaccessibleMemoryAccess(accesses.memory.len()));
                    }
                }

                // Early exit if we already know the memory size will be too big
                if max_size >= o.page_size() || min_size > liblisa::state::MAX_MEMORY_SIZE as u64 {
                    return Err(AccessAnalysisError::MemoryAccessTooBig);
                }

                let access = MemoryAccess {
                    kind: if true {
                        // TODO: should we still try to use Self::is_written(o, &bases, &inputs, &calculation)?
                        AccessKind::InputOutput
                    } else {
                        AccessKind::Input
                    },
                    inputs,
                    size: min_size..max_size,
                    calculation,
                    alignment,
                };

                info!("New access added in {}ms: {:?}", start.elapsed().as_millis(), access);
                accesses.memory.push(access);
            }
        }

        if !needs_trap_flag {
            accesses.use_trap_flag = false;
        }

        info!("Accesses for careful checks: {:#X?}", accesses);

        // Now, we use careful observations to make sure we did not miss any memory accesses.
        // NOTE: We have already found all memory accesses with independent variables. (i.e., they use at least 1 different register)
        // Therefore, every memory access that we find here can be computed by adding a static offset to one of the other memory accesses.
        let mut oks = 0;
        let mut n = 0;
        let mut randomization_errs = 0;
        if !skip_careful_observe {
            loop {
                info!("Doing careful checks for {:X} (oks={})", accesses.instr, oks);
                let state_gen = StateGen::new(&accesses, &mappable)?;
                let base = match state_gen.randomize_new(&mut rng) {
                    Ok(result) => result,
                    Err(err) => {
                        info!("Saw error from randomize_new: {err}");
                        randomization_errs += 1;
                        if randomization_errs >= 1_000_000 {
                            return Err(AccessAnalysisError::Randomization(err));
                        } else {
                            continue;
                        }
                    },
                };

                n += 1;
                if n > 5000 {
                    error!("Unable to perform careful checks for {:X}", accesses.instr);
                    return Err(AccessAnalysisError::InstructionKeepsFaulting);
                }

                let base_result = o.observe(&base);
                debug!("Base with result {:X?}: {:X?}", base_result, base);

                // We don't expect memory accesses here, since we should have identified all memory accesses that we can observe with page faults!
                // randomize_new always produces a state where all pages are mappable
                match base_result {
                    Err(OracleError::MemoryAccess(addr)) => {
                        // Make sure we're not seeing this error because we incorrectly estimated the size of the memory
                        if base
                            .memory()
                            .areas()
                            .any(|area| (area.start_addr().page::<A>() + 1).start_addr() == addr)
                        {
                            continue
                        }

                        panic!("This memory access should have been caught in the loop above");
                    },
                    Err(OracleError::GeneralFault) => {
                        // This memory access might be caused by an alignment, so we cannot panic here.
                        // If it is impossible to generate valid states, we would have returned an error already.
                        // Therefore, we can just retry until we eventually get an OK state.
                        continue
                    },
                    Err(OracleError::MultipleInstructionsExecuted) if !accesses.use_trap_flag => {
                        accesses.use_trap_flag = true;
                        continue
                    },
                    Err(e @ (OracleError::MultipleInstructionsExecuted | OracleError::Timeout)) => {
                        return Err(AccessAnalysisError::Randomization(RandomizationError::OracleError(e)))
                    },
                    Err(_) => continue,
                    _ => (),
                }

                // println!("Base {base:?} results in {base_result:?}");
                let mut found = match o.scan_memory_accesses(&base) {
                    Ok(found) => found,
                    Err(e) => {
                        // println!("ERROR while scanning memory accesses: {}", e);
                        // o.debug_dump();
                        Err(e)?
                    },
                };
                found.sort();
                found.retain(|&found_addr| {
                    base.memory().areas().zip(accesses.memory.iter()).all(
                        |(area, access)| !area.start_addr().into_area(access.size.start).contains(found_addr), // found_addr < *mapped_addr || found_addr >= mapped_addr + access.size.start as u64
                    )
                });
                debug!("Found: {:X?}", found);
                if found.is_empty() {
                    oks += 1;
                    if oks >= 5 {
                        for access in accesses.memory.iter_mut() {
                            access.size.end = access.size.start;
                        }

                        break;
                    }
                } else {
                    oks = 0;

                    loop {
                        let mut changed = false;
                        found.retain(|&addr| {
                            for (access, &(mapped_addr, ..)) in accesses.memory.iter_mut().zip(base.memory().iter()) {
                                if addr == mapped_addr + access.size.start {
                                    access.size.start += 1;
                                    access.size.end = access.size.start.max(access.size.end);

                                    changed = true;
                                    return false;
                                }
                            }

                            true
                        });

                        if !changed {
                            break;
                        }
                    }

                    if let Some(addr) = found.first() {
                        // We found a new memory access that will always overlap with another access on the same page.
                        // This cannot be handled correctly, so we fail.
                        error!("New memory access that we cannot map: {:X?} {:X?}", addr, base);
                        return Err(AccessAnalysisError::Randomization(RandomizationError::Unsatisfiable(
                            accesses.len(),
                        )));
                    }
                }
            }
        }

        Ok(accesses)
    }

    pub fn infer<A: Arch, O: Oracle<A>>(o: &mut O, instr: &Instruction) -> Result<MemoryAccesses<A>, AccessAnalysisError<A>> {
        let r = Self::infer_quick(o, instr)?;
        if r.memory.iter().any(|access| access.size.start > liblisa::state::MAX_MEMORY_SIZE as u64/* || access.size.end > liblisa::MAX_MEMORY_SIZE as u64 * 4*/) {
            return Err(AccessAnalysisError::MemoryAccessTooBig);
        }

        let instr_mem = &r.memory[0];
        if let Some(access_index) = r.memory.iter().skip(1).position(|access| {
            access.inputs == instr_mem.inputs
                && instr_mem
                    .calculation
                    .constant_offset_with(&access.calculation)
                    .map(|offset| offset >= -(access.size.end as i64) && offset <= instr_mem.size.end as i64)
                    .unwrap_or(false)
        }) {
            // TODO: Separate error
            return Err(AccessAnalysisError::UnaccessibleMemoryAccess(access_index + 1));
        }

        Ok(r)
    }
}
