//! Random state generation.

use std::cmp::Ordering;
use std::fmt::Debug;
use std::sync::atomic::{self, AtomicU64};

use log::*;
use rand::prelude::SliceRandom;
use rand::Rng;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::arch::{Arch, CpuState, NumberedRegister, Register};
use crate::encoding::dataflows::{AccessKind, AddrTerm, Dest, IntoDestWithSize, MemoryAccess, MemoryAccesses, Size, Source};
use crate::oracle::{MappableArea, OracleError};
use crate::state::{Addr, Location, MemoryState, Permissions, StateByte, SystemState};
use crate::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};
use crate::value::{MutValue, Value};

mod value;
pub use value::*;

use super::SystemStateByteView;

/// Error that can occur while generating a randomized CPU input state.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Error, Debug, Clone, Serialize, Deserialize)]
pub enum RandomizationError {
    /// Modifying the values of one of the storage locations was not possible.
    #[error("Modifying values failed")]
    ModifyingValuesFailed,

    /// No valid randomized state could be found
    #[error("Unable to synthesize a valid random state")]
    RandomStateSynthesisFailed,

    /// An oracle error occurred.
    #[error("Oracle error: {}", .0)]
    OracleError(OracleError),

    /// Encountered an unmappable fixed offset for a memory access
    #[error("Encountered an unmappable fixed offset for access {}", .0)]
    UnmappableFixedOffset(usize),

    /// No acceptable values for the inputs for a memory access could be found.
    #[error("We could not find acceptable values for inputs to memory access #{}", .0)]
    Unsatisfiable(usize),
}

/// Error that can be returned by [`StateGen::remap`].
#[derive(Error, Debug)]
pub enum RemapError<A: Arch> {
    #[doc(hidden)]
    #[error("Phantom")]
    Phantom(A),

    /// The remapping causes a memory mapping to be mapped on to two separate pages
    #[error("The remapping causes memory #{} to be mapped on to two separate pages", .0)]
    MemoryMappingCrossesPageBounds(usize),

    /// The remapping causes a memory mapping to unmappable
    #[error("The remapping causes memory #{} to unmappable", .0)]
    CannotMapMemory(usize),

    /// Adapting the state with [`StateGen::adapt`] failed.
    #[error("Adapting to the new memory accesses failed")]
    AdaptFailed,

    /// An error occurred while randomizing part of the state.
    #[error("Randomization error: {}", .0)]
    RandomizationError(RandomizationError),
}

impl<A: Arch> From<RandomizationError> for RemapError<A> {
    fn from(e: RandomizationError) -> Self {
        RemapError::RandomizationError(e)
    }
}

#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
enum Constraint {
    None,
    Impossible,
    PageRegion { min_offset: u64, max_offset: u64 },
}

/// Generates random [`SystemState`]s consistent with a set of [`MemoryAccesses`].
pub struct StateGen<'a, A: Arch, M: MappableArea> {
    /// The memory accesses to which all generated [`SystemState`]s must adhere.
    pub accesses: &'a MemoryAccesses<A>,
    mappable: &'a M,
    constraints: Vec<Constraint>,
    address_registers: Vec<A::GpReg>,
    address_register_map: FixedBitmapU64<2>,
    num_failures: AtomicU64,
}

impl<'a, A: Arch, M: MappableArea> Clone for StateGen<'a, A, M> {
    fn clone(&self) -> Self {
        Self {
            accesses: self.accesses,
            mappable: self.mappable,
            constraints: self.constraints.clone(),
            address_register_map: self.address_register_map.clone(),
            address_registers: self.address_registers.clone(),
            num_failures: AtomicU64::new(self.num_failures.load(atomic::Ordering::Relaxed)),
        }
    }
}

impl<'a, A: Arch, M: MappableArea> StateGen<'a, A, M> {
    /// Creates a new randomized state generator.
    /// This function builds memory access constraints for the random state generation.
    /// If it is not possible to generate a state of non-overlapping memory mappings, this function will return an error.
    pub fn new(accesses: &'a MemoryAccesses<A>, mappable: &'a M) -> Result<Self, RandomizationError> {
        info!("Determining constraints for {accesses}");
        let ps = 1 << A::PAGE_BITS;
        let pm = ps - 1;
        let constraints = accesses
            .memory
            .iter()
            .enumerate()
            .map(|(index, m)| {
                if m.inputs.is_empty() && !mappable.can_map(Addr::new(m.calculation.offset as u64)) {
                    return Constraint::Impossible;
                }

                let mut min_offset = 0;
                let mut max_offset = ps - m.size.end;

                // Will some memory area always overlap?
                for (other_index, other) in accesses.memory.iter().enumerate() {
                    if other_index != index {
                        if let Some(offset) =
                            other
                                .calculation
                                .constant_offset_considering_inputs(&other.inputs, &m.calculation, &m.inputs)
                        {
                            let overlapping = match offset.cmp(&0) {
                                // offset == 0 => the two memory accesses always overlap completely
                                Ordering::Equal => true,

                                // offset < 0  => m_addr = other_addr + offset, so -offset must be >= m_size; accesses are overlapping otherwise
                                Ordering::Less => {
                                    let abs_offset = (-offset) as u64;
                                    let page_offset = abs_offset & pm;
                                    // Constraints because executable mappings must always be on a separate page
                                    match abs_offset.cmp(&ps) {
                                        Ordering::Less => {
                                            if m.kind == AccessKind::Executable || other.kind == AccessKind::Executable {
                                                min_offset = ps.wrapping_sub(page_offset);
                                            }
                                        },
                                        Ordering::Equal => {
                                            max_offset = ps - m.size.end.max(other.size.end);
                                        },
                                        Ordering::Greater => (),
                                    }

                                    offset + m.size.end as i64 > 0
                                },

                                // offset > 0  => m_addr = other_addr + offset, so offset must be >= other_size; accesses are overlapping otherwise
                                Ordering::Greater => {
                                    let abs_offset = offset as u64;
                                    let page_offset = offset as u64 & pm;

                                    // Constraints because executable mappings must always be on a separate page
                                    match abs_offset.cmp(&ps) {
                                        Ordering::Less => {
                                            if m.kind == AccessKind::Executable || other.kind == AccessKind::Executable {
                                                max_offset = page_offset.wrapping_sub(other.size.end) & pm;
                                            }
                                        },
                                        Ordering::Equal => {
                                            max_offset = ps - m.size.end.max(other.size.end);
                                        },
                                        Ordering::Greater => (),
                                    }

                                    (offset as u64) < other.size.end
                                },
                            };

                            if overlapping {
                                info!("Access {:?} is impossible in: {:?}", m, accesses);
                                return Constraint::Impossible;
                            }
                        }
                    }
                }

                assert!(
                    min_offset <= max_offset,
                    "min_offset={min_offset}, max_offset={max_offset}; {accesses:?}"
                );
                assert!(
                    max_offset <= 4096,
                    "min_offset={min_offset}, max_offset={max_offset}; {accesses:?}"
                );

                debug!("offset in {min_offset}..{max_offset}");
                if min_offset > ps - m.size.end {
                    Constraint::Impossible
                } else {
                    Constraint::PageRegion {
                        min_offset,
                        max_offset,
                    }
                }
            })
            .collect::<Vec<_>>();
        debug!("Constraints = {:X?}", constraints);

        if let Some(index) = constraints.iter().position(|c| matches!(c, Constraint::Impossible)) {
            warn!("StateGen::new failed with impossible constraint");
            return Err(RandomizationError::Unsatisfiable(index));
        }

        if let Some((index, access)) = accesses.iter().enumerate().find(|(_, access)| {
            access.has_fixed_addr()
                && access
                    .compute_fixed_addr()
                    .into_area(access.size.end)
                    .crosses_page_bounds(A::PAGE_BITS)
        }) {
            info!("Access always crosses page bounds: {:X?}", access);
            return Err(RandomizationError::Unsatisfiable(index));
        }

        let mut address_registers = accesses
            .memory
            .iter()
            .flat_map(|m| m.inputs.iter())
            .flat_map(|input| match input {
                Source::Dest(Dest::Reg(reg, _)) => Some(*reg),
                Source::Const {
                    ..
                }
                | Source::Imm(_) => None,
                _ => panic!("Cannot generate state for encoding with parts: {accesses:?}"),
            })
            .filter(|reg| !reg.is_zero())
            // ARCHITECTURE ASSUMPTION: Only GpRegs are used for memory addresses
            .map(|reg| A::try_reg_to_gpreg(reg).unwrap())
            .chain(A::iter_gpregs().filter(|reg| reg.is_addr_reg()))
            .collect::<Vec<_>>();
        address_registers.sort();
        address_registers.dedup();

        Ok(Self {
            accesses,
            mappable,
            constraints,
            address_register_map: {
                let mut b = FixedBitmapU64::<2>::new_all_zeros(128);
                for reg in address_registers.iter() {
                    debug_assert!(reg.as_num() < 128);
                    b.set(reg.as_num());
                }

                b
            },
            address_registers,
            num_failures: AtomicU64::new(0),
        })
    }

    /// Returns true if any of the bytes in `bytes_modified` are used in a memory mapping.
    /// If they are, this means that you need to call [`StateGen::adapt`] after modifying one of these bytes.
    pub fn needs_adapt_from_bytes(&self, view: &SystemStateByteView<'_, A>, bytes_modified: &[StateByte]) -> bool {
        bytes_modified.iter().any(|&byte| {
            let (reg, _) = view.as_reg(byte);
            let gpreg = view.try_reg_to_gpreg(reg);

            gpreg.map(|reg| self.address_register_map.get(reg.as_num())).unwrap_or(false)
            // self.address_registers().iter().any(|&addr_reg| view.arch_reg_to_reg(A::reg(addr_reg)) == reg)
        })
    }

    /// Returns true if any of the general purpose registers in `gpregs` are used in a memory mapping.
    /// If they are, this means that you need to call [`StateGen::adapt`] after modifying one of these registers.
    pub fn needs_adapt_from_gpregs(&self, gpregs: &[A::GpReg]) -> bool {
        gpregs.iter().any(|&reg| self.address_register_map.get(reg.as_num()))
    }

    fn perms_compatible(left: Permissions, right: Permissions) -> bool {
        matches!(
            (left, right),
            (Permissions::Read, Permissions::Read)
                | (Permissions::Execute, Permissions::Read)
                | (Permissions::Read, Permissions::Execute)
                | (Permissions::ReadWrite, Permissions::ReadWrite)
                | (Permissions::Execute, Permissions::Execute)
        )
    }

    fn is_always_bad_addr(
        &self, memory: impl Iterator<Item = &'a (Addr, Permissions, Vec<u8>)>, accesses: &[MemoryAccess<A>],
        access: &MemoryAccess<A>, addr: Addr, perms: Permissions,
    ) -> bool {
        if !self.mappable.can_map(addr) {
            true
        } else {
            let area = addr.into_area(access.size.end);
            if area.crosses_page_bounds(A::PAGE_BITS) {
                true
            } else {
                // If the address was observed, we need a margin to account for when we observe an incorrect start offset.
                // We might observe an incorrect start offset if the page before page_addr is already mapped.
                // The first few bytes of this memory access might have occurred on the page before it, which we cannot observe.
                // If the address was computed, we are 100% sure about the start offset and don't need any padding.
                let padded_area = area;
                !memory.zip(accesses.iter()).all(|((other_addr, other_perms, _), other)| {
                    !other.has_fixed_addr()
                        || if Self::perms_compatible(perms, *other_perms) {
                            // We are able to compute the exact locations of both accesses, and they have the same permissions.
                            // We can let them occur on the same page. We just make sure they don't overlap
                            !padded_area.overlaps_with(&other_addr.into_area(other.size.end))
                        } else {
                            // We either obtain the address by observation, or there is a permission mismatch.
                            // In such a case, the memory accesses may not occur on the same page.
                            !padded_area.shares_page_with::<A>(&other_addr.into_area(other.size.end))
                        }
                })
            }
        }
    }

    fn good_addr(
        &self, memory: impl Iterator<Item = &'a (Addr, Permissions, Vec<u8>)>,
        accesses: impl Iterator<Item = &'a MemoryAccess<A>>, access: &MemoryAccess<A>, addr: Addr, perms: Permissions,
    ) -> bool {
        if !self.mappable.can_map(addr) {
            false
        } else {
            let area = addr.into_area(access.size.end);
            if area.crosses_page_bounds(A::PAGE_BITS) {
                false
            } else {
                // If the address was observed, we need a margin to account for when we observe an incorrect start offset.
                // We might observe an incorrect start offset if the page before page_addr is already mapped.
                // The first few bytes of this memory access might have occurred on the page before it, which we cannot observe.
                // If the address was computed, we are 100% sure about the start offset and don't need any padding.
                let padded_area = area;

                for ((other_addr, other_perms, _), other) in memory.zip(accesses) {
                    if Self::perms_compatible(perms, *other_perms) {
                        // We are able to compute the exact locations of both accesses, and they have the same permissions.
                        // We can let them occur on the same page. We just make sure they don't overlap
                        if padded_area.overlaps_with(&other_addr.into_area(other.size.end)) {
                            return false;
                        }
                    } else {
                        // We either obtain the address by observation, or there is a permission mismatch.
                        // In such a case, the memory accesses may not occur on the same page.
                        if padded_area.shares_page_with::<A>(&other_addr.into_area(other.size.end)) {
                            return false;
                        }
                    }
                }

                true
            }
        }
    }

    // TODO: Can we require that the old state must be valid as well?
    fn adapt_up_to_len(&self, s: &mut SystemState<A>, changed_instr: bool, len: usize) -> bool {
        for reg in A::iter_gpregs().filter(Register::is_addr_reg) {
            if !self.mappable.can_map(Addr::new(s.cpu().gpreg(reg))) {
                return false;
            }
        }

        let mut all_eq = s.contains_valid_addrs && !changed_instr;
        trace!("====== Begin adapt() ======");
        for (access_index, access) in self.accesses.memory.iter().enumerate().take(len) {
            trace!("Checking access {}: {:X?}", access_index, access);

            let new_addr = access.compute_address(s);
            trace!("Address = {:X?}", new_addr);

            let old_addr = s.memory().addr(access_index);
            if (all_eq && new_addr == old_addr)
                || self.good_addr(
                    s.memory().iter().enumerate().take(access_index).map(|(_, x)| x),
                    self.accesses.memory.iter().enumerate().take(access_index).map(|(_, x)| x),
                    access,
                    new_addr,
                    s.memory().get(access_index).1,
                )
            {
                if old_addr != new_addr {
                    trace!("Changing memory #{} from {:X?} to {:X?}", access_index, old_addr, new_addr);
                    s.memory_mut().get_mut(access_index).set_addr(new_addr);
                    all_eq = false;
                }

                if new_addr.as_u64() % access.alignment as u64 != 0 {
                    return false;
                }

                if access_index != 0 {
                    // Trim memory data if we have some slices that are bigger than what we would expect from the accesses.
                    // This can occur when we're adapting from another instruction.
                    // Normally, this doesn't happen.
                    // TODO: Eliminate these or move to separate function for adapting to a different instruction.
                    let max_len = access.size.end as usize;
                    s.memory_mut().get_mut(access_index).crop_data(max_len);
                }
            } else {
                s.contains_valid_addrs = false;
                return false;
            }
        }

        // Trim memory data if we have some slices that are bigger than what we would expect from the accesses (this can occur when we're adapting from another instruction)
        for (access_index, access) in self.accesses.memory.iter().enumerate().take(len) {
            if access_index != 0 {
                let max_len = access.size.end as usize;
                s.memory_mut().get_mut(access_index).crop_data(max_len);
            }
        }

        // Ensure that each memory allocation is on a separate page
        // TODO: Make sure accesses with different permissions or without calculations are on a separate page
        #[cfg(debug_assertions)]
        for (index, (a1, _, d1)) in s.memory().iter().enumerate().take(len) {
            if let Some(overlapping) = s
                .memory()
                .iter()
                .take(len)
                .skip(index + 1)
                .find(|(a2, _, d2)| a1.into_area(d1.len() as u64).overlaps_with(&a2.into_area(d2.len() as u64)))
            {
                panic!("Memory accesses may not overlap: {s:X?}; Overlapping: {a1:X?} with {overlapping:X?}");
            }
        }

        debug!("Adapted state: {:X?}", s);

        trace!("====== Successfully completed adapt() ======");
        if len == s.memory().len() {
            s.contains_valid_addrs = true;
        }

        assert!(
            s.memory().iter().take(len).all(|(addr, ..)| self.mappable.can_map(*addr)),
            "State contains unmappable addresses: {s:X?}"
        );

        true
    }

    /// Adapts the memory mappings to the current CPU state in `s.cpu()`.
    /// This only changes `s.memory`.
    /// If it is impossible to map the memory to the new CPU state, false is returned.
    /// If false is returned, the memory mappings in state `s` may be in a partially modified state.
    /// Another successful call to this function is needed before the state is valid.
    pub fn adapt(&self, s: &mut SystemState<A>, changed_instr: bool) -> bool {
        if self.accesses.use_trap_flag {
            s.use_trap_flag = true;
        }

        self.adapt_up_to_len(s, changed_instr, s.memory().len())
    }

    fn fill_state<R: Rng>(&self, rng: &mut R, state: &mut SystemState<A>) -> Result<FillResult, RandomizationError> {
        for (access_index, access) in self.accesses.memory.iter().enumerate() {
            let mut n = 0;
            loop {
                trace!("Current fill state: {:X?}", state);
                n += 1;
                if n > 10 {
                    return Ok(FillResult::Unsatisfiable(access_index));
                }

                let addr = access.compute_address(state);
                state.memory_mut().get_mut(access_index).set_addr(addr);
                let &(_, perms, _) = state.memory().get(access_index);

                let align_ok = addr.as_u64() % access.alignment as u64 == 0;

                trace!("Address = {:X?}", addr);
                if align_ok
                    && self.good_addr(
                        state.memory().iter().take(access_index),
                        self.accesses.memory.iter(),
                        access,
                        addr,
                        perms,
                    )
                {
                    // We have found acceptable values for this memory access!

                    debug!("OK: {:X?} (index={}) @ address {:X}", access, access_index, addr);

                    break;
                } else if state
                    .memory()
                    .iter()
                    .take(access_index)
                    .any(|(other_addr, ..)| *other_addr == addr)
                {
                    // We have exactly this address already mapped, which means that this must be a write to a read-only page.
                    // Assuming we have identified the memory accesses correctly, this means that we are double-mapping some
                    // memory.
                    return Ok(FillResult::DoubleMappedMemory(access_index));
                } else {
                    // The memory access from this combination of registers is not acceptable, so we randomize and retry
                    // If there is nothing we can do to modify the address that is accessed, just give up immediately.
                    if access.has_fixed_addr() {
                        debug!(
                            "Potentially unmappable address: 0x{:X} in {:?} {:?}",
                            addr, state, self.accesses
                        );
                        if access.has_fixed_addr()
                            && self.is_always_bad_addr(
                                state.memory().iter().take(access_index),
                                &self.accesses.memory,
                                access,
                                addr,
                                perms,
                            )
                        {
                            debug!("Unmappable fixed offset for {:?} = {:?}", state, addr);
                            return Ok(FillResult::UnmappableFixedOffset(access_index));
                        }
                    }

                    let mut n = 0;
                    loop {
                        let mut any_changed = false;
                        let mut tries = 0;
                        'fix_loop: loop {
                            trace!("Modifying: {:?}", access.inputs);
                            for reg in access.inputs.iter() {
                                match reg {
                                    Source::Dest(Dest::Reg(reg, _)) => {
                                        if !reg.is_zero() {
                                            state.set_reg(*reg, Value::Num(self.randomize_register(rng, *reg)));
                                            any_changed = true;
                                        }
                                    },
                                    Source::Dest(Dest::Mem(index, _)) => {
                                        state
                                            .memory_mut()
                                            .get_mut(*index)
                                            .modify_data(|buf| value::randomized_bytes_into_buffer(rng, buf));
                                    },
                                    Source::Imm(_)
                                    | Source::Const {
                                        ..
                                    } => {},
                                }
                            }

                            // If we have a constraint, we should check the constraint to make sure we are adhering to it.
                            // If we are not adhering to a constraint, fill_state is guaranteed to fail.
                            let c = &self.constraints[access_index];
                            let calculation = access.calculation;
                            let new_addr = Addr::new(calculation.compute(&access.inputs, state));
                            if self.good_addr(
                                state.memory().iter().take(access_index),
                                self.accesses.memory.iter(),
                                access,
                                new_addr,
                                perms,
                            ) {
                                debug!("Found good addr: {:X?} with state: {:?}", new_addr, state);
                                let page_offset = new_addr - new_addr.page::<A>().start_addr();
                                let delta = match c {
                                    Constraint::Impossible => return Ok(FillResult::Unsatisfiable(access_index)),
                                    Constraint::None => break,
                                    Constraint::PageRegion {
                                        min_offset,
                                        max_offset,
                                    } => {
                                        if page_offset >= *min_offset && page_offset <= *max_offset {
                                            debug!("Constraint OK");
                                            break
                                        } else {
                                            let fixed_offset = if min_offset == max_offset {
                                                *min_offset
                                            } else {
                                                rng.gen_range(*min_offset..*max_offset)
                                            };
                                            let fixed_addr = new_addr.align_to_page_start(A::PAGE_BITS) + fixed_offset;

                                            fixed_addr - new_addr
                                        }
                                    },
                                };

                                trace!(
                                    "Trying to fix randomization because a constraint is not valid: {:X?} on page offset {:X} (address = {:X}) (all constraints = {:X?}) in state: {:X?} (tries={})",
                                    c, page_offset, new_addr, self.constraints, state, tries
                                );

                                for (index, reg) in access.inputs.iter().enumerate() {
                                    if calculation.terms[index] == AddrTerm::identity() {
                                        match reg {
                                            Source::Dest(Dest::Reg(reg, _)) if !reg.is_zero() => {
                                                let reg = A::try_reg_to_gpreg(*reg).unwrap();
                                                let value = state.cpu().gpreg(reg).wrapping_add(delta);
                                                state.cpu_mut().set_gpreg(reg, value);
                                                any_changed = true;
                                                trace!("Fixed state: {:X?}", state);

                                                trace!(
                                                    "New memory location: {:X?} ({:X?})",
                                                    calculation.compute(&access.inputs, state),
                                                    access
                                                );
                                                break 'fix_loop;
                                            },
                                            _ => {},
                                        }
                                    }
                                }
                            }

                            tries += 1;
                            if tries > 10_000 {
                                return Ok(FillResult::Unsatisfiable(access_index));
                            }
                        }

                        if !any_changed {
                            // This is a fixed address so we cannot change it.
                            // We have to restart from the beginning
                            warn!("Found an unmappable fixed offset (any_changed=false): {:X?}", addr);

                            // Returning just Unsatisfiable here because it's possible to recover from this
                            return Ok(FillResult::Unsatisfiable(access_index));
                        }

                        if self.adapt_up_to_len(state, false, access_index) {
                            break;
                        } else {
                            n += 1;
                            if n > 50 {
                                warn!("adapt_up_to_len failed 50 times for instruction {:X}", self.accesses.instr);
                                return Ok(FillResult::Unsatisfiable(access_index));
                            }
                        }
                    }
                }
            }
        }

        trace!("Fill state complete: {:?}", state);

        Ok(FillResult::Ok)
    }

    /// Returns a randomized value for the register `reg`.
    /// The random value is masked to [`Register::mask`], if any.
    ///
    /// If the register is the program counter, a random address where the full instruction can be mapped is returned.
    /// If the register is an address register (such as the FS/GS base registers), a random valid mappable address is returned.
    pub fn randomize_register<R: Rng>(&self, rng: &mut R, reg: A::Reg) -> u64 {
        if let Some(mask) = reg.mask() {
            rng.gen::<u64>() & mask
        } else if reg.is_pc() {
            loop {
                let page = {
                    let mut page = Addr::new(randomized_value(rng)).page::<A>();
                    while !self.mappable.can_map(page.start_addr()) || !self.mappable.can_map(page.last_address_of_page()) {
                        page = Addr::new(randomized_value(rng)).page::<A>();
                    }

                    page
                };

                // It is tempting to just always put the PC near the end or the start of a page.
                // This reduces the differences in PC that we will see.
                // If there are some instructions that use the PC as part of a computation, we will never observe the full input space.
                // This is a problem, for example because we won't be able to infer alignment for memory accesses of the form (pc + 0x....)
                // Therefore we add a small offset of up to 128. We ensure that lower offsets occur more often.
                let v = rng.gen::<u16>();
                let val = v as u64 & 0x7f | 0x80;
                let shift = ((v >> 7) & 0b1111) % 9;
                let at_start = v > u16::MAX / 2;
                let pc_offset = val >> shift;

                // Ensure that the offset is a multiple of A::INSTRUCTION_ALIGNMENT
                let pc_offset = pc_offset & !(A::INSTRUCTION_ALIGNMENT as u64 - 1);
                let addr = if at_start {
                    page.start_addr() + pc_offset
                } else {
                    page.first_address_after_page() - self.accesses.instr.byte_len() as u64 - pc_offset
                }
                .as_u64();

                if self.mappable.can_map(Addr::new(addr)) {
                    return addr;
                }
            }
        } else if reg.is_addr_reg() {
            loop {
                let v = randomized_value(rng);
                if self.mappable.can_map(Addr::new(v)) {
                    return v;
                }
            }
        } else {
            randomized_value(rng)
        }
    }

    /// Generates a new random CPU state with valid memory mappings.
    pub fn randomize_new<R: Rng>(&self, rng: &mut R) -> Result<SystemState<A>, RandomizationError> {
        let mut last_result = FillResult::Ok;
        let mut error_counter = 0;

        let mut state = SystemState::<A>::new(
            {
                A::CpuState::create(|reg, value| match value {
                    MutValue::Num(n) => *n = self.randomize_register(rng, reg),
                    MutValue::Bytes(buf) => value::randomized_bytes_into_buffer(rng, buf),
                })
            },
            MemoryState::new(self.accesses.iter().map(|access| {
                (
                    Addr::new(0),
                    match access.kind {
                        AccessKind::Input | AccessKind::InputOutput => Permissions::ReadWrite,
                        AccessKind::Executable => Permissions::Execute,
                    },
                    if access.kind == AccessKind::Executable {
                        self.accesses.instr.bytes().to_vec()
                    } else {
                        value::randomized_bytes(rng, access.size.end as usize)
                    },
                )
            })),
        );

        state.use_trap_flag = self.accesses.use_trap_flag;

        for _ in 0..5_000 {
            // Try to fill the state. If this fails, one of the filled constraints caused an overlap.
            // When that happens, we retry from the start with different values by looping again.
            let result = self.fill_state(rng, &mut state)?;

            if let FillResult::Ok = result {
                self.num_failures.store(0, atomic::Ordering::Relaxed);

                assert!(
                    state.memory().iter().all(|(addr, ..)| self.mappable.can_map(*addr)),
                    "State contains unmappable addresses: {state:X?} with accesses={:X?}",
                    self.accesses
                );

                return Ok(state);
            } else {
                let num_failures = self.num_failures.fetch_add(1, atomic::Ordering::Relaxed);
                if num_failures >= 25_000 {
                    // We've already seen 25k failures without any success.
                    // There is probably no input state that would be satisfactory.
                    // Abort early and return the last error.
                    break
                }

                if let FillResult::UnmappableFixedOffset(access_index) = result {
                    let access = &self.accesses.memory[access_index];
                    if access.has_fixed_addr() {
                        return Err(RandomizationError::UnmappableFixedOffset(access_index));
                    }
                }

                if last_result == result {
                    error_counter += 1;
                } else {
                    error_counter = 1;
                    last_result = result;
                }
            }

            // Randomize the part of the CPU state that affects memory accesses
            // ARCHITECTURE ASSUMPTION: Memory access addresses only depend on GPRegs
            for &gpreg in self.address_registers.iter() {
                let reg = A::reg(gpreg);
                state.cpu_mut().set_gpreg(gpreg, self.randomize_register(rng, reg));
            }
        }

        if error_counter >= 50 {
            match last_result {
                FillResult::Ok => unreachable!(),
                FillResult::UnmappableFixedOffset(index) => Err(RandomizationError::UnmappableFixedOffset(index)),
                FillResult::Unsatisfiable(index) => Err(RandomizationError::Unsatisfiable(index)),
                FillResult::DoubleMappedMemory(index) => Err(RandomizationError::Unsatisfiable(index - 1)),
            }
        } else {
            Err(RandomizationError::RandomStateSynthesisFailed)
        }
    }

    /// Randomizes the state, but only guarantees to change values in `locations`. Other values *may* be copied from `base` as an optimization, or may be randomized.
    pub fn randomize_new_with_locations<R: Rng>(
        &self, base: &SystemState<A>, locations: &[Location<A>], rng: &mut R,
    ) -> Result<SystemState<A>, RandomizationError> {
        let mut last_result = FillResult::Ok;
        let mut error_counter = 0;

        let mut state = base.clone();
        for loc in locations {
            state.modify_dest(
                &(*loc).into_dest_with_size(match loc {
                    Location::Reg(reg) => Size::new(0, reg.byte_size() - 1),
                    Location::Memory(index) => Size::new(0, self.accesses.memory[*index].size.end as usize - 1),
                }),
                |val| match val {
                    MutValue::Num(n) => {
                        *n = match loc {
                            Location::Reg(reg) => self.randomize_register(rng, *reg),
                            Location::Memory(_) => unreachable!(),
                        }
                    },
                    MutValue::Bytes(buf) => value::randomized_bytes_into_buffer(rng, buf),
                },
            );
        }

        state.use_trap_flag = self.accesses.use_trap_flag;

        for _ in 0..5_000 {
            // Try to fill the state. If this fails, one of the filled constraints caused an overlap.
            // When that happens, we retry from the start with different values by looping again.
            let result = self.fill_state(rng, &mut state)?;

            if let FillResult::Ok = result {
                self.num_failures.store(0, atomic::Ordering::Relaxed);

                assert!(
                    state.memory().iter().all(|(addr, ..)| self.mappable.can_map(*addr)),
                    "State contains unmappable addresses: {state:X?} with accesses={:X?}",
                    self.accesses
                );

                return Ok(state);
            } else {
                let num_failures = self.num_failures.fetch_add(1, atomic::Ordering::Relaxed);
                if num_failures >= 25_000 {
                    // We've already seen 25k failures without any success.
                    // There is probably no input state that would be satisfactory.
                    // Abort early and return the last error.
                    break
                }

                if let FillResult::UnmappableFixedOffset(access_index) = result {
                    let access = &self.accesses.memory[access_index];
                    if access.has_fixed_addr() {
                        return Err(RandomizationError::UnmappableFixedOffset(access_index));
                    }
                }

                if last_result == result {
                    error_counter += 1;
                } else {
                    error_counter = 1;
                    last_result = result;
                }
            }

            // Randomize the part of the CPU state that affects memory accesses
            // ARCHITECTURE ASSUMPTION: Memory access addresses only depend on GPRegs
            for &gpreg in self.address_registers.iter() {
                let reg = A::reg(gpreg);
                state.cpu_mut().set_gpreg(gpreg, self.randomize_register(rng, reg));
            }
        }

        if error_counter >= 50 {
            match last_result {
                FillResult::Ok => unreachable!(),
                FillResult::UnmappableFixedOffset(index) => Err(RandomizationError::UnmappableFixedOffset(index)),
                FillResult::Unsatisfiable(index) => Err(RandomizationError::Unsatisfiable(index)),
                FillResult::DoubleMappedMemory(index) => Err(RandomizationError::Unsatisfiable(index - 1)),
            }
        } else {
            Err(RandomizationError::RandomStateSynthesisFailed)
        }
    }

    /// Fills as many storage locations with the byte `b`.
    pub fn fill_with_byte<R: Rng>(&self, rng: &mut R, state: &mut SystemState<A>, b: u8) {
        let u64_val = b as u64;
        let u64_val = u64_val | (u64_val << 8);
        let u64_val = u64_val | (u64_val << 16);
        let u64_val = u64_val | (u64_val << 32);

        for reg in A::iter_regs() {
            if let Some(mask) = reg.mask() {
                state.cpu_mut().modify_reg(reg, |v| match v {
                    MutValue::Num(n) => *n = u64_val & mask,
                    _ => unimplemented!(),
                });
            } else if !self.address_registers.iter().any(|&r| A::reg(r) == reg) {
                state.cpu_mut().modify_reg(reg, |v| match v {
                    MutValue::Num(n) => *n = u64_val,
                    MutValue::Bytes(bytes) => bytes.fill(b),
                });
            }
        }

        for mem_index in 1..state.memory().len() {
            let mut mem = state.memory_mut().get_mut(mem_index);
            mem.modify_data(|bytes| bytes.fill(b));
        }

        debug_assert!(self.adapt(state, false), "State could not be adapted: {state:?}");

        let mut registers_to_fill = self.address_registers.clone();
        registers_to_fill.shuffle(rng);

        // We don't need to adapt so far, because we haven't modified any address registers.

        let mut last_adapt_failed = false;
        for reg in registers_to_fill {
            for fill_size in 0..8 {
                let original_value = state.cpu().gpreg(reg);
                let fill_mask = u64::MAX >> (56 - fill_size * 8);
                let fill_value = (original_value & !fill_mask) | (u64_val & fill_mask);
                state.cpu_mut().set_gpreg(reg, fill_value);
                last_adapt_failed = false;
                if !self.adapt(state, false) {
                    state.cpu_mut().set_gpreg(reg, original_value);
                    last_adapt_failed = true;
                    break;
                }
            }
        }

        // Correct the last adapt if it failed
        if last_adapt_failed {
            let _result = self.adapt(state, false);
            assert!(_result);
        }

        debug_assert!(self.adapt(state, false));
    }

    /// Fills as many storage locations as possible with the value of the register `reg`.
    pub fn fill_from_address_register<R: Rng>(&self, rng: &mut R, state: &mut SystemState<A>, reg: A::GpReg) {
        let fill_value = state.cpu().gpreg(reg);
        // TODO: Randomize between LE and BE bytes
        let fill_bytes = if rng.gen() {
            fill_value.to_le_bytes()
        } else {
            fill_value.to_be_bytes()
        };

        for reg in A::iter_regs() {
            if let Some(mask) = reg.mask() {
                state.cpu_mut().modify_reg(reg, |v| match v {
                    MutValue::Num(n) => *n = fill_value & mask,
                    _ => unimplemented!(),
                });
            } else if !self.address_registers.iter().any(|&r| A::reg(r) == reg) {
                state.cpu_mut().modify_reg(reg, |v| match v {
                    MutValue::Num(n) => *n = fill_value,
                    MutValue::Bytes(bytes) => {
                        for chunk in bytes.chunks_mut(8) {
                            chunk.copy_from_slice(&fill_bytes[..chunk.len()]);
                        }
                    },
                });
            }
        }

        for mem_index in 1..state.memory().len() {
            let mut mem = state.memory_mut().get_mut(mem_index);
            mem.modify_data(|bytes| {
                for chunk in bytes.chunks_mut(8) {
                    chunk.copy_from_slice(&fill_bytes[..chunk.len()]);
                }
            });
        }

        debug_assert!(self.adapt(state, false));

        let mut registers_to_fill = self.address_registers.iter().filter(|&&r| r != reg).collect::<Vec<_>>();
        registers_to_fill.shuffle(rng);

        // We don't need to adapt so far, because we haven't modified any address registers.

        let mut last_adapt_failed = false;
        for &reg in registers_to_fill {
            let original_value = state.cpu().gpreg(reg);
            state.cpu_mut().set_gpreg(reg, fill_value);
            last_adapt_failed = false;
            if !self.adapt(state, false) {
                state.cpu_mut().set_gpreg(reg, original_value);
                last_adapt_failed = true;
            }
        }

        // Correct the last adapt if it failed
        if last_adapt_failed {
            let _result = self.adapt(state, false);
            assert!(_result);
        }

        debug_assert!(self.adapt(state, false));
    }

    /// Remaps a provide system state from other memory accesses to the memory accesses belonging to this [`StateGen`].
    pub fn remap(&self, cs: &SystemState<A>) -> Result<SystemState<A>, RemapError<A>> {
        let new_instr = self.accesses.instr;

        let mut cs = cs.clone();
        let pc = Addr::new(cs.cpu().gpreg(A::PC));
        if pc.into_area(new_instr.byte_len() as u64).crosses_page_bounds(A::PAGE_BITS) {
            return Err(RemapError::MemoryMappingCrossesPageBounds(0));
        }

        if !self.mappable.can_map(pc) {
            return Err(RemapError::CannotMapMemory(0));
        }

        let mut item = cs.memory_mut().get_mut(0);
        item.set_addr(pc);
        item.set_data(new_instr.bytes());

        if self.adapt(&mut cs, true) {
            Ok(cs)
        } else {
            Err(RemapError::AdaptFailed)
        }
    }

    /// Randomizes the storage location `location` while keeping a byte at position N in the location unchanged if `bytes_to_keep_unchanged[N]` is true.
    pub fn randomize_location<R: Rng>(
        &self, location: &Location<A>, state: &mut SystemState<A>, rng: &mut R, bytes_to_keep_unchanged: &[bool],
    ) {
        match location {
            Location::Reg(reg) => {
                state.cpu_mut().modify_reg(*reg, |dst| match dst {
                    MutValue::Num(n) => loop {
                        let old = *n;
                        let new = self.randomize_register(rng, *reg);
                        let mask = bytes_to_keep_unchanged
                            .iter()
                            .rev()
                            .map(|&b| if b { 0xff } else { 0u64 })
                            .fold(0, |acc, b| (acc << 8) | b);
                        let new = (old & mask) | (new & !mask);
                        if new != old {
                            *n = new;
                            break;
                        }
                    },
                    MutValue::Bytes(old) => loop {
                        let mut new = randomized_bytes(rng, old.len());
                        for (index, _) in bytes_to_keep_unchanged.iter().enumerate().filter(|(_, keep)| **keep) {
                            new[index] = old[index];
                        }

                        if new != old {
                            old.copy_from_slice(&new);
                            break;
                        }
                    },
                });
            },
            Location::Memory(index) => loop {
                let old = &state.memory().get(*index).2;
                let mut new = randomized_bytes(rng, self.accesses.memory[*index].size.end as usize);
                for (index, _) in bytes_to_keep_unchanged.iter().enumerate().filter(|(_, keep)| **keep) {
                    new[index] = old[index];
                }

                if &new != old {
                    state.memory_mut().get_mut(*index).set_data(&new);
                    break;
                }
            },
        }
    }

    /// Returns all address registers involved in the address computations of memory mappings.
    pub fn address_registers(&self) -> &[A::GpReg] {
        &self.address_registers
    }
}

/// Updates the memory mappings to the correct locations according to `accesses` without checking for overlapping mappings or mappings that cross page boundaries.
pub fn update_memory_addresses_unchecked<A: Arch>(accesses: &MemoryAccesses<A>, state: &mut SystemState<A>) {
    for (index, access) in accesses.iter().enumerate() {
        let new_address = access.compute_address(state);
        state.memory_mut().get_mut(index).set_addr(new_address);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum FillResult {
    Ok,
    UnmappableFixedOffset(usize),
    Unsatisfiable(usize),
    DoubleMappedMemory(usize),
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::Constraint;
    use crate::arch::fake::{AnyArea, FakeArch, FakeReg};
    use crate::arch::CpuState;
    use crate::encoding::dataflows::{AccessKind, AddressComputation, Dest, Inputs, MemoryAccess, MemoryAccesses, Size, Source};
    use crate::instr::Instruction;
    use crate::state::random::StateGen;

    #[test]
    pub fn constraints_have_correct_offsets() {
        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x00, 0x00]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(3),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };
        let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();

        assert_eq!(
            state_gen.constraints,
            vec![
                Constraint::PageRegion {
                    min_offset: 0xFFD,
                    max_offset: 0xFFD
                },
                Constraint::PageRegion {
                    min_offset: 0,
                    max_offset: 0,
                },
            ]
        );

        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x00, 0x00]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(16),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };
        let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();
        assert_eq!(
            state_gen.constraints,
            vec![
                Constraint::PageRegion {
                    min_offset: 0xFF0,
                    max_offset: 0xFFD
                },
                Constraint::PageRegion {
                    min_offset: 0x000,
                    max_offset: 0x00D,
                },
            ]
        );

        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x00, 0x00]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(-12),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };
        let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();
        assert_eq!(
            state_gen.constraints,
            vec![
                Constraint::PageRegion {
                    min_offset: 0x000,
                    max_offset: 0x009,
                },
                Constraint::PageRegion {
                    min_offset: 0xFF4,
                    max_offset: 0xFFD,
                },
            ]
        );

        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x00, 0x00]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(-4108),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };
        let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();
        assert_eq!(
            state_gen.constraints,
            vec![
                Constraint::PageRegion {
                    min_offset: 0x000,
                    max_offset: 0xFFD,
                },
                Constraint::PageRegion {
                    min_offset: 0x000,
                    max_offset: 0xFFD,
                },
            ]
        );

        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x00, 0x00]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 8..8,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(4096),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };
        let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();
        assert_eq!(
            state_gen.constraints,
            vec![
                Constraint::PageRegion {
                    min_offset: 0x000,
                    max_offset: 0xFF8,
                },
                Constraint::PageRegion {
                    min_offset: 0x000,
                    max_offset: 0xFF8,
                },
            ]
        );
    }

    #[test]
    pub fn generate_random_state() {
        let _accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x12, 0x34, 0x56]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R1, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(-8),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };
    }

    #[test]
    pub fn adapt_overlapping_locations() {
        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x12, 0x34, 0x56]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R1, Size::qword()))]),
                    size: 8..8,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(-8),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    size: 8..8,
                    calculation: AddressComputation::unscaled_sum(1).with_offset(-8),
                    alignment: 1,
                },
                // MemoryAccess {
                //     kind: AccessKind::InputOutput,
                //     inputs: Inputs::sorted(vec![ Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())) ]),
                //     size: 8..8,
                //     calculation: AddressComputation::unscaled_sum(1).with_offset(-16),
                //     alignment: 1,
                // },
                // MemoryAccess {
                //     kind: AccessKind::InputOutput,
                //     inputs: Inputs::sorted(vec![ Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())) ]),
                //     size: 8..8,
                //     calculation: AddressComputation::unscaled_sum(1).with_offset(-16),
                //     alignment: 1,
                // },
            ],
            use_trap_flag: false,
        };

        let sg = StateGen::new(&accesses, &AnyArea).unwrap();

        let mut state = sg.randomize_new(&mut rand::thread_rng()).unwrap();

        state.cpu_mut().set_gpreg(FakeReg::R0, 0x1234);
        state.cpu_mut().set_gpreg(FakeReg::R1, 0x000037005FFFFFFF); // 'RSP'
        state.cpu_mut().set_gpreg(FakeReg::R2, 0x000000000000001E); // 'RBP'
        assert!(sg.adapt(&mut state, false), "Adapt should succeed: {state:#X?}");

        state.cpu_mut().set_gpreg(FakeReg::R0, 0x2); // 'RIP'

        println!("State before: {state:#X?}");

        assert!(
            !sg.adapt(&mut state, false),
            "Adapt should fail when mapping RW and X on the same page: {state:#X?}"
        );

        println!("State after: {state:#X?}");
    }

    #[test]
    pub fn offsets_ok() {
        let accesses = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[0x12, 0x34, 0x56, 0x00, 0x00, 0x00, 0x00]),
            memory: vec![
                MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 7..7,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                },
                MemoryAccess {
                    kind: AccessKind::InputOutput,
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                        Source::Const {
                            value: 0,
                            num_bits: 32,
                        },
                    ]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(2).with_offset(7),
                    alignment: 1,
                },
            ],
            use_trap_flag: false,
        };

        let sg = StateGen::new(&accesses, &AnyArea).unwrap();

        assert_eq!(
            sg.constraints,
            vec![
                Constraint::PageRegion {
                    min_offset: 4089,
                    max_offset: 4089,
                },
                Constraint::PageRegion {
                    min_offset: 0,
                    max_offset: 0,
                },
            ]
        );
    }
}
