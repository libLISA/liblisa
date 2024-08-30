//! All traits needed to define an architecture.
//!
//! In order to implement an architecture, you should define a struct that implements the [`Arch`] trait.
//! Additionally, you will need to define types that implement [`Register`] and [`Flag`], and reference these from the [`Arch`] trait.
//!
//! An example of a minimal implementation can be found in the [`fake`] module.
//! It implements a fake architecture that is used in some tests.
//!
//! In addition, you can inspect the source code of the various existing architecture implementation crates, such as `liblisa-x64`.

use std::fmt::{Debug, Display};
use std::hash::Hash;

use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::state::{StateByte, SystemStateIoPair};
use crate::value::{MutValue, Value, ValueType};

pub mod fake;
mod scope;
pub mod undef;
pub mod x64;

pub use scope::*;

/// Represents a CPU architecture.
pub trait Arch: Copy + Clone + Debug + PartialEq + Eq + Hash + Default + PartialOrd + Ord + Send + Sync + 'static
where
    Self: Sized,
{
    /// The CPU state representation.
    type CpuState: CpuState<Self> + Clone + PartialEq + Eq + Send + Sync + Debug + Display;

    /// The register representation.
    type Reg: Register
        + Copy
        + Clone
        + Debug
        + Display
        + Eq
        + Hash
        + PartialOrd
        + Ord
        + Serialize
        + DeserializeOwned
        + Send
        + Sync;

    /// The general-purpose register representation.
    /// This should be equal to [`Self::Reg`], or be a subset.
    /// General-purpose registers must be integers (see [`crate::value::ValueType`]).
    ///
    /// These are the only registers that are used in address computations.
    type GpReg: Register
        + NumberedRegister
        + Clone
        + Debug
        + Display
        + Eq
        + Hash
        + PartialOrd
        + Ord
        + Serialize
        + DeserializeOwned
        + Send
        + Sync;

    /// The flag representation.
    ///
    /// A flag should always be part of a flag register.
    ///
    /// See also [`Arch::flagreg_to_flags`].
    type Flag: Flag
        + Clone
        + Debug
        + Display
        + PartialEq
        + Eq
        + Hash
        + PartialOrd
        + Ord
        + Serialize
        + DeserializeOwned
        + Send
        + Sync;

    /// The number of bits that are used in a page.
    /// The page size is `2**PAGE_BITS`.
    /// For example, for a page size of 4096 bytes `PAGE_BITS` would be `12`.
    const PAGE_BITS: usize;

    /// The program counter register.
    const PC: Self::GpReg;

    /// The zero register.
    /// If the architecture does not explicitly list a zero register, you can invent one.
    const ZERO: Self::GpReg;

    /// The alignment of the instructions. Must be a multiple of 2.
    const INSTRUCTION_ALIGNMENT: usize = 1;

    /// Converts a general-purpose register into a generic register.
    /// This must always succeed.
    fn reg(reg: Self::GpReg) -> Self::Reg;

    /// Converts a generic register into a general-purpose register.
    /// If the generic register is not a general-purpose register, `None` is returned.
    fn try_reg_to_gpreg(reg: Self::Reg) -> Option<Self::GpReg>;

    /// Returns the flags associated with the byte range in the flags register.
    /// By convention, a flag register should contain one flag per byte.
    fn flagreg_to_flags(reg: Self::Reg, start_byte: usize, end_byte: usize) -> &'static [Self::Flag];

    /// Returns an iterator that iterates over all general-purpose registers.
    /// The zero register must not be included, as it is not a real register.
    fn iter_gpregs() -> impl Iterator<Item = Self::GpReg>;

    /// Returns an iterator that iterates over all registers.
    /// The zero register must not be included, as it is not a real register.
    fn iter_regs() -> impl Iterator<Item = Self::Reg>;
}

/// Represents a CPU state.
pub trait CpuState<A: Arch>: Default {
    /// The type of the difference mask used in [`CpuState::find_dataflows_masked`].
    ///
    /// An optional optimization. Set to `()` if not used.
    type DiffMask: Clone + Default + Debug;

    /// Returns the value of `reg`.
    fn gpreg(&self, reg: A::GpReg) -> u64;

    /// Sets the value of `reg`.
    fn set_gpreg(&mut self, reg: A::GpReg, value: u64);

    /// Returns the value of `reg`.
    fn reg(&self, reg: A::Reg) -> Value<'_>;

    /// Modifies the value of `reg` using update function `update`.
    ///
    /// The update function receives a [`crate::value::MutValue`], which can be used to update the value of the register.
    fn modify_reg<F: FnOnce(MutValue)>(&mut self, reg: A::Reg, update: F);

    /// Returns the value of `flag`.
    fn flag(&self, flag: A::Flag) -> bool;

    /// Sets the value of `flag`.
    fn set_flag(&mut self, flag: A::Flag, value: bool);

    /// Creates a new CPU state using `regval` to determine the values of the registers.
    ///
    /// Implementation is optional.
    /// The default implementation calls [`CpuState::modify_reg`] on each register to initialize them.
    #[inline(always)]
    fn create<R: FnMut(A::Reg, MutValue)>(mut regval: R) -> Self {
        let mut state = Self::default();
        for reg in A::iter_regs() {
            CpuState::modify_reg(&mut state, reg, |val| regval(reg, val));
        }

        state
    }

    /// Creates a default state with the program counter set to `pc`.
    fn default_with_pc(pc: u64) -> Self {
        let mut state = Self::default();
        state.set_gpreg(A::PC, pc);
        state
    }

    /// Returns the size (in bytes) of the CPU state.
    fn size() -> usize;

    /// Returns the value of the byte `byte` in the CPU state.
    #[inline]
    fn get_state_byte(&self, byte: StateByte) -> u8 {
        let (reg, index) = Self::state_byte_to_reg(byte);
        self.reg(reg).select_byte(index)
    }

    /// Sets the value of the byte `byte` in the CPU state.
    fn set_state_byte(&mut self, byte: StateByte, value: u8) {
        let (reg, index) = Self::state_byte_to_reg(byte);
        self.modify_reg(reg, |v| match v {
            MutValue::Num(n) => {
                let shift = index * 8;
                let mask = 0xff << shift;

                #[cfg(debug_assertions)]
                {
                    let (reg, index) = Self::state_byte_to_reg(byte);
                    let mask = if let Some(mask) = reg.mask() {
                        (mask >> (index * 8)) as u8
                    } else {
                        0xff
                    };
                    debug_assert_eq!(value & !mask, 0, "State byte {byte:?} ({reg:?} byte {index}) is masked (0b{mask:b}, tried to set value 0b{value:b}) and should not have bits set outside its mask");
                }

                *n = (*n & !mask) | ((value as u64) << shift);
            },
            MutValue::Bytes(b) => {
                b[index] = value;
            },
        })
    }

    /// Returns true if the value of the specified state byte in `self` is not equal to the value in `other`.
    #[inline]
    fn state_bytes_unequal(&self, dest: StateByte, other: &Self) -> bool {
        self.get_state_byte(dest) != other.get_state_byte(dest)
    }

    /// Returns true if the value of the specified state byte in `self` is equal to the value in `other`.
    #[inline]
    fn state_bytes_equal(&self, dest: StateByte, other: &Self) -> bool {
        !self.state_bytes_unequal(dest, other)
    }

    /// Converts a state byte to a register.
    /// Inverse of [`CpuState::reg_to_state_byte`].
    fn state_byte_to_reg(byte: StateByte) -> (A::Reg, usize);

    /// Converts a (register, byte index) tuple to a state byte.
    /// Inverse of [`CpuState::state_byte_to_reg`].
    fn reg_to_state_byte(reg: A::Reg, byte: usize) -> StateByte;

    /// Enumerates over all differences between the two state pairs.
    /// Calls `found` for each state byte that differs between `self` and `other`.
    /// The call order is unspecified.
    fn find_differences<F: FnMut(StateByte)>(&self, other: &Self, found: &mut F) {
        for b in (0..Self::size()).map(StateByte::new) {
            if self.get_state_byte(b) != other.get_state_byte(b) {
                found(b);
            }
        }
    }

    /// Creates a mask of state bytes whose differences can be ignored.
    fn create_diff_mask<I: Iterator<Item = StateByte>>(items: I) -> Self::DiffMask;

    /// Enumerates over all differences between the two state pairs.
    /// Calls `found` for each state byte that differs between `self` and `other`.
    /// `diff_mask` is a *hint* of differences that can be ignored.
    /// Therefore, this function may call `found` even for state bytes that can be ignored according to `diff_mask`.
    #[allow(unused)]
    fn find_dataflows_masked<F: FnMut(StateByte)>(
        b: SystemStateIoPair<A>, a: SystemStateIoPair<A>, dest_diff_mask: &Self::DiffMask, diff_mask: &Self::DiffMask,
        found: &mut F,
    ) {
        a.state_in.cpu().find_differences(a.state_out.cpu(), found);
        b.state_in.cpu().find_differences(b.state_out.cpu(), found);
    }
}

/// Represents a register.
pub trait Register: Copy + Sized + PartialOrd + Ord + PartialEq {
    /// Returns whether this register is the program counter.
    fn is_pc(&self) -> bool;

    /// Returns whether this register is the zero register.
    fn is_zero(&self) -> bool;

    /// Returns whether this register is a flags register.
    fn is_flags(&self) -> bool;

    /// Indicates which bits may be set. Any bit '1' in the mask may be set, any bit '0' MUST always be set to '0'.
    /// Returns `None` when the register is a [`crate::value::ValueType::Bytes`].
    /// Returns `None` when all bits may be set (this is equivalent to returning `Some(0xffffffff_ffffffff)`)
    fn mask(&self) -> Option<u64>;

    /// Returns true if the register should always contain a valid memory address.
    fn is_addr_reg(&self) -> bool;

    /// Returns true if this register should be avoided if possible.
    /// This is used by enumeration to determine which instruction would be best to analyze.
    ///
    /// This is a *hint*, and can be ignored if needed.
    fn should_avoid(&self) -> bool {
        false
    }

    /// Returns the number of bytes the register uses.
    /// It must be possible to modify at least one bit in each byte.
    fn byte_size(&self) -> usize;

    /// Returns the value type of the register.
    fn reg_type(self) -> ValueType;
}

/// Implements conversion to and from `usize`.
/// This is required for general purpose registers, and is used as an optimization in some code.
pub trait NumberedRegister {
    /// Converts the register to a `usize`.
    /// Inverse of [`NumberedRegister::from_num`].
    fn as_num(&self) -> usize;

    /// Converts the `usize` to a register.
    /// Inverse of [`NumberedRegister::as_num`].
    ///
    /// # Panics
    /// This function will panic if the `usize` does not refer to a valid register.
    fn from_num(num: usize) -> Self;
}

/// Represents a flag.
pub trait Flag: Copy + Sized + PartialOrd + Ord {
    /// Returns an iterator that iterates over all flags.
    fn iter() -> impl Iterator<Item = Self>;
}
