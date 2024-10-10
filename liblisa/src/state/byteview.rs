use std::hash::Hash;
use std::iter::Fuse;

use super::{SystemState, SystemStateIoPair};
use crate::arch::{Arch, CpuState, Register};
use crate::encoding::dataflows::MemoryAccesses;
use crate::state::Location;
use crate::value::{MutValue, Value, ValueType};

/// A byte in a CPU state.
/// Used in the [`SystemStateByteView`] to reference specific bytes in the system state.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct StateByte(u32);

impl std::fmt::Debug for StateByte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.0)
    }
}

impl StateByte {
    /// Creates a new state byte from `num`.
    ///
    /// Does not check whether `num` corresponds to a valid state byte.
    #[inline(always)]
    pub fn new(num: usize) -> Self {
        debug_assert!(num < u32::MAX as usize);
        Self(num as u32)
    }

    /// Converts the state byte to a `usize`.
    #[inline(always)]
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// A bytewise view of a system state.
/// Allows the state to be read and written as if it were a contiguous block of bytes.
#[derive(Copy, Clone, Debug)]
pub struct SystemStateByteView<'a, A: Arch> {
    memory_accesses: &'a MemoryAccesses<A>,
}

/// A register in the [`SystemStateByteView`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SystemStateByteViewReg<R> {
    /// A register
    Reg(R),

    /// A memory area
    Memory {
        /// The index of the memory access
        access_index: usize,

        /// The size of the memory access
        size: usize,
    },
}

impl<R: Register> SystemStateByteViewReg<R> {
    /// Returns the size (in bytes) of the register.
    pub fn byte_size(&self) -> usize {
        match self {
            SystemStateByteViewReg::Reg(reg) => reg.byte_size(),
            SystemStateByteViewReg::Memory {
                size, ..
            } => *size,
        }
    }

    /// Returns true if the register is a flags register.
    pub fn is_flags(&self) -> bool {
        match self {
            SystemStateByteViewReg::Reg(reg) => reg.is_flags(),
            _ => false,
        }
    }

    /// Returns the mask ([Register::mask]) of the register, if there is any.
    pub fn mask(&self) -> Option<u64> {
        match self {
            SystemStateByteViewReg::Reg(reg) => reg.mask(),
            _ => None,
        }
    }
}

impl<'a, A: Arch> SystemStateByteView<'a, A> {
    /// Creates a new byte view for system states consistent with `memory_accesses`.
    #[inline]
    pub fn new(memory_accesses: &'a MemoryAccesses<A>) -> Self {
        Self {
            memory_accesses,
        }
    }

    /// Returns the size, in bytes, of the system state.
    #[inline]
    pub fn size(&self) -> usize {
        A::CpuState::size()
            + self
                .memory_accesses
                .iter()
                .skip(1)
                .map(|access| access.size.end as usize)
                .sum::<usize>()
    }

    /// Returns `byte` in the system state `state`.
    #[inline]
    pub fn get(&self, state: &SystemState<A>, byte: StateByte) -> u8 {
        let (reg, offset) = self.as_reg(byte);
        match reg {
            SystemStateByteViewReg::Memory {
                access_index, ..
            } => state.memory().get(access_index).2[offset],
            SystemStateByteViewReg::Reg(_) => state.cpu().get_state_byte(byte),
        }
    }

    /// Writes `byte` in the system state `state`.
    #[inline]
    pub fn set(&self, state: &mut SystemState<A>, byte: StateByte, value: u8) {
        if byte.as_usize() < A::CpuState::size() {
            state.cpu_mut().set_state_byte(byte, value);
        } else {
            let (reg, byte_index) = self.as_reg(byte);
            match reg {
                SystemStateByteViewReg::Memory {
                    access_index, ..
                } => state
                    .memory_mut()
                    .get_mut(access_index)
                    .modify_data(|bytes| bytes[byte_index] = value),
                _ => unreachable!(),
            }
        }
    }

    /// Returns true if byte `dest` has the same value in both `a` and `b`.
    #[inline]
    pub fn bytes_equal(&self, dest: StateByte, a: &SystemState<A>, b: &SystemState<A>) -> bool {
        !self.bytes_unequal(dest, a, b)
    }

    /// Returns true if byte `dest` have different values in both `a` and `b`.
    #[inline]
    pub fn bytes_unequal(&self, dest: StateByte, a: &SystemState<A>, b: &SystemState<A>) -> bool {
        if dest.as_usize() < A::CpuState::size() {
            a.cpu().state_bytes_unequal(dest, b.cpu())
        } else {
            self.get(a, dest) != self.get(b, dest)
        }
    }

    /// Converts the byte to a [`SystemStateByteViewReg`] and index.
    pub fn as_reg(&self, byte: StateByte) -> (SystemStateByteViewReg<A::Reg>, usize) {
        if let Some(memory_index) = byte.as_usize().checked_sub(A::CpuState::size()) {
            let mut offset = 0;
            for (access_index, access) in self.memory_accesses.iter().enumerate().skip(1) {
                if access.size.end as usize + offset > memory_index {
                    return (
                        SystemStateByteViewReg::Memory {
                            access_index,
                            size: access.size.end as usize,
                        },
                        memory_index - offset,
                    );
                }

                offset += access.size.end as usize;
            }

            panic!(
                "byte {:?} is not a valid state byte (state size is {} bytes)",
                byte,
                self.size()
            )
        } else {
            let (reg, index) = A::CpuState::state_byte_to_reg(byte);
            (SystemStateByteViewReg::Reg(reg), index)
        }
    }

    /// Converts `reg` and the corresponding byte index `byte` to a [`StateByte`].
    #[inline]
    pub fn reg_to_byte(&self, reg: SystemStateByteViewReg<A::Reg>, byte: usize) -> StateByte {
        match reg {
            SystemStateByteViewReg::Reg(reg) => A::CpuState::reg_to_state_byte(reg, byte),
            SystemStateByteViewReg::Memory {
                access_index, ..
            } => StateByte::new(
                A::CpuState::size()
                    + byte
                    + self
                        .memory_accesses
                        .iter()
                        .take(access_index)
                        .skip(1)
                        .map(|access| access.size.end as usize)
                        .sum::<usize>(),
            ),
        }
    }

    /// Converts a [`Register`] to the corresponding [`SystemStateByteViewReg`].
    #[inline]
    pub fn arch_reg_to_reg(&self, reg: <A as Arch>::Reg) -> SystemStateByteViewReg<A::Reg> {
        SystemStateByteViewReg::Reg(reg)
    }

    /// Returns the value of the register `reg` in `state`.
    #[inline]
    pub fn get_reg<'v>(&self, state: &'v SystemState<A>, reg: &SystemStateByteViewReg<A::Reg>) -> Value<'v> {
        match reg {
            SystemStateByteViewReg::Reg(reg) => state.cpu().reg(*reg),
            SystemStateByteViewReg::Memory {
                access_index, ..
            } => Value::Bytes(&state.memory().get(*access_index).2),
        }
    }

    /// Writes the value of the register `reg` in `state`.
    pub fn set_reg(&self, state: &mut SystemState<A>, reg: &SystemStateByteViewReg<A::Reg>, value: Value) {
        match reg {
            SystemStateByteViewReg::Reg(reg) => state.set_reg(*reg, value),
            SystemStateByteViewReg::Memory {
                access_index, ..
            } => match value {
                Value::Bytes(bytes) => {
                    debug_assert_eq!(bytes.len(), state.memory().get(*access_index).2.len());
                    state.memory_mut().get_mut(*access_index).set_data(bytes);
                },
                _ => unimplemented!(),
            },
        }
    }

    /// Writes the value of the register `reg` in `state`.
    pub fn modify_reg(&self, state: &mut SystemState<A>, reg: &SystemStateByteViewReg<A::Reg>, mut modify: impl FnMut(MutValue)) {
        match reg {
            SystemStateByteViewReg::Reg(reg) => state.cpu_mut().modify_reg(*reg, modify),
            SystemStateByteViewReg::Memory {
                access_index, ..
            } => state
                .memory_mut()
                .get_mut(*access_index)
                .modify_data(|b| modify(MutValue::Bytes(b))),
        }
    }

    /// Converts `reg` to a [`Location`].
    #[inline]
    pub fn to_location(&self, reg: SystemStateByteViewReg<A::Reg>) -> Location<A> {
        match reg {
            SystemStateByteViewReg::Reg(reg) => Location::Reg(reg),
            SystemStateByteViewReg::Memory {
                access_index, ..
            } => Location::Memory(access_index),
        }
    }

    /// Calls `found` for each byte which does not have the same value in `left` and `right`.
    pub fn find_differences<F: FnMut(StateByte)>(&self, left: &SystemState<A>, right: &SystemState<A>, found: &mut F) {
        left.cpu().find_differences(right.cpu(), found);

        let mut offset = 0;
        for (left, right) in left.memory().iter().zip(right.memory().iter()).skip(1) {
            debug_assert_eq!(left.2.len(), right.2.len());
            for (byte_index, _) in left.2.iter().zip(right.2.iter()).enumerate().filter(|(_, (l, r))| l != r) {
                found(StateByte::new(A::CpuState::size() + offset + byte_index));
            }

            offset += left.2.len();
        }
    }

    /// Iterates over all registers.
    #[inline]
    pub fn all_regs(&self) -> impl Iterator<Item = SystemStateByteViewReg<A::Reg>> + '_ {
        AllRegsIter {
            arch_iter: A::iter_regs().fuse(),
            memory_accesses: self.memory_accesses,
            current_index: 1,
        }
    }

    /// Returns the [`ValueType`] of `reg`.
    #[inline]
    pub fn reg_type(&self, reg: &SystemStateByteViewReg<A::Reg>) -> ValueType {
        match reg {
            SystemStateByteViewReg::Reg(r) => r.reg_type(),
            SystemStateByteViewReg::Memory {
                size, ..
            } => ValueType::Bytes(*size),
        }
    }

    /// Creates a mask for [`Self::find_dataflows_masked`] that covers all bytes in `iter`.
    pub fn create_diff_mask<I: Iterator<Item = StateByte>>(&self, iter: I) -> <A::CpuState as CpuState<A>>::DiffMask {
        A::CpuState::create_diff_mask(iter.filter(|b| b.as_usize() < A::CpuState::size()))
    }

    /// Calls `found` for all state bytes SB where `a_in[SB] != a_out[SB]` or `b_in[SB] != b_out[SB]`.
    ///
    /// The function is allowed to ignore any masked bytes in `dest_diff_mask`, but is not required to do so.
    pub fn find_dataflows_masked<F: FnMut(StateByte)>(
        &self, b: SystemStateIoPair<A>, a: SystemStateIoPair<A>, dest_diff_mask: &<A::CpuState as CpuState<A>>::DiffMask,
        diff_mask: &<A::CpuState as CpuState<A>>::DiffMask, found: &mut F,
    ) {
        A::CpuState::find_dataflows_masked(b, a, dest_diff_mask, diff_mask, found);

        let mut offset = 0;
        for ((a_in, a_out), (b_in, b_out)) in a
            .state_in
            .memory()
            .iter()
            .zip(a.state_out.memory().iter())
            .skip(1)
            .zip(b.state_in.memory().iter().zip(b.state_out.memory().iter()).skip(1))
        {
            debug_assert_eq!(b_in.2.len(), b_out.2.len());
            for (byte_index, _) in a_in
                .2
                .iter()
                .zip(a_out.2.iter())
                .zip(b_in.2.iter().zip(b_out.2.iter()))
                .enumerate()
                .filter(|(_, ((a_in, a_out), (b_in, b_out)))| a_in != a_out || b_in != b_out)
            {
                found(StateByte::new(A::CpuState::size() + offset + byte_index));
            }

            offset += b_in.2.len();
        }
    }

    /// Tries to convert `reg` to a general-purpose register.
    pub fn try_reg_to_gpreg(&self, reg: SystemStateByteViewReg<A::Reg>) -> Option<<A as Arch>::GpReg> {
        match reg {
            SystemStateByteViewReg::Reg(r) => A::try_reg_to_gpreg(r),
            SystemStateByteViewReg::Memory {
                ..
            } => None,
        }
    }
}

struct AllRegsIter<'a, A: Arch, I> {
    arch_iter: Fuse<I>,
    memory_accesses: &'a MemoryAccesses<A>,
    current_index: usize,
}

impl<A: Arch, I: Iterator<Item = A::Reg>> Iterator for AllRegsIter<'_, A, I> {
    type Item = SystemStateByteViewReg<A::Reg>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.arch_iter.next() {
            Some(SystemStateByteViewReg::Reg(item))
        } else {
            let result = self
                .memory_accesses
                .memory
                .get(self.current_index)
                .map(|access| SystemStateByteViewReg::Memory {
                    access_index: self.current_index,
                    size: access.size.end as usize,
                });
            self.current_index += 1;
            result
        }
    }
}
