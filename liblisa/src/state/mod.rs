//! CPU state representation, efficient representations of modifications to CPU state, and CPU state randomization.

use std::cell::Ref;
use std::fmt::{Debug, Display};

use crate::arch::{Arch, CpuState};
use crate::encoding::dataflows::Dest;
use crate::value::{MutValue, Value};

mod addr;
mod byteview;
pub mod jit;
mod locs;
mod memory;
pub mod random;

pub use addr::{Addr, Area, Page};
pub use byteview::*;
pub use locs::*;
pub use memory::*;

/// The maximum number of bytes that a single memory mapping can be.
pub const MAX_MEMORY_SIZE: usize = 128;

/// An input-output pair of [`SystemState`]s.
#[derive(Copy, Clone, Debug)]
pub struct SystemStateIoPair<'a, A: Arch> {
    /// The input state
    pub state_in: &'a SystemState<A>,

    /// The observed output state after executing an instruction in `state_in`.
    pub state_out: &'a SystemState<A>,
}

impl<'a, A: Arch> From<(&'a SystemState<A>, &'a SystemState<A>)> for SystemStateIoPair<'a, A> {
    fn from((state_in, state_out): (&'a SystemState<A>, &'a SystemState<A>)) -> Self {
        Self {
            state_in,
            state_out,
        }
    }
}

/// A CPU state consisting of the architecture-specific state part and memory mappings.
#[derive(Clone, PartialEq, Eq)]
pub struct SystemState<A: Arch> {
    cpu: Box<A::CpuState>,
    memory: MemoryState,

    /// True if the trap flag should be used to observe this system state.
    pub use_trap_flag: bool,

    /// True if the state's memory mapping contains valid addresses.
    pub contains_valid_addrs: bool,
}

impl<A: Arch> AsRef<SystemState<A>> for SystemState<A> {
    fn as_ref(&self) -> &SystemState<A> {
        self
    }
}

impl<A: Arch> AsSystemState<A> for SystemState<A> {
    type Output<'a> = &'a SystemState<A>;

    fn as_system_state(&self) -> Self::Output<'_> {
        self
    }
}

impl<'s, A: Arch> AsSystemState<A> for &'s SystemState<A> {
    type Output<'a> = &'a SystemState<A>
        where Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        self
    }
}

impl<A: Arch> AsSystemState<A> for Box<SystemState<A>> {
    type Output<'a> = &'a SystemState<A>;

    fn as_system_state(&self) -> Self::Output<'_> {
        self.as_ref()
    }
}

impl<A: Arch> AsRef<SystemState<A>> for Ref<'_, SystemState<A>> {
    fn as_ref(&self) -> &SystemState<A> {
        SystemState::as_ref(self)
    }
}

impl<A: Arch> Debug for SystemState<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.cpu(), f)?;
        Display::fmt(self.memory(), f)?;

        Ok(())
    }
}

impl<A: Arch> Default for SystemState<A> {
    fn default() -> Self {
        Self::new_without_memory(Default::default())
    }
}

impl<A: Arch> SystemState<A> {
    /// Returns the CPU state
    #[inline(always)]
    pub fn cpu(&self) -> &A::CpuState {
        &self.cpu
    }

    /// Returns the memory mappings
    #[inline(always)]
    pub fn memory(&self) -> &MemoryState {
        &self.memory
    }

    /// Returns a mutable reference to the CPU state
    #[inline(always)]
    pub fn cpu_mut(&mut self) -> &mut A::CpuState {
        &mut self.cpu
    }

    /// Returns a mutable reference to the memory mappings
    #[inline(always)]
    pub fn memory_mut(&mut self) -> &mut MemoryState {
        &mut self.memory
    }

    /// Creates a new [`SystemState`].
    ///
    /// Sets `use_trap_flag` and `contains_valid_addrs` to true.
    #[inline]
    pub fn new(cpu: A::CpuState, memory: MemoryState) -> SystemState<A> {
        SystemState {
            cpu: Box::new(cpu),
            memory,
            use_trap_flag: true,
            contains_valid_addrs: true,
        }
    }

    /// Creates a new [`SystemState`] without any memory mappings.
    ///
    /// Sets `use_trap_flag` and `contains_valid_addrs` to true.
    #[inline]
    pub fn new_without_memory(cpu: A::CpuState) -> SystemState<A> {
        Self::new(cpu, MemoryState::default())
    }

    /// Returns a new [`SystemState`] with all memory mappings replaced by `memory`.
    ///
    /// Sets `use_trap_flag` and `contains_valid_addrs` to true.
    #[inline]
    pub fn with_new_memory(self, _num_memory: usize, _num_bytes: usize, memory: MemoryState) -> SystemState<A> {
        Self::new(self.cpu().clone(), memory)
    }

    /// Returns a new [`SystemState`] with storage location `loc` set to `value`.
    #[inline]
    pub fn with_location(&self, loc: &Location<A>, value: Value) -> Self {
        let mut result = self.clone();
        result.set_location(loc, value);
        result
    }

    /// Returns the value of `dest`.
    pub fn get_dest(&self, dest: &Dest<A>) -> Value<'_> {
        let loc = Location::from(dest);
        let value = self.location(&loc);
        let size = dest.size();

        let sliced = value.slice(size);

        sliced
    }

    /// Writes the value of `dest`.
    pub fn set_dest(&mut self, dest: &Dest<A>, new_value: &Value<'_>) {
        let loc = Location::from(dest);
        let new_bytes;
        let size = dest.size();
        let current_value = self.location(&loc);
        let sliced = {
            match (current_value, new_value) {
                (Value::Num(current), Value::Num(new)) => {
                    let w = (size.end_byte - size.start_byte + 1) * 8;
                    let mask = if w == 64 { 0xffff_ffff_ffff_ffff } else { (1 << w) - 1 } << (size.start_byte * 8);
                    Value::Num((current & !mask) | ((new << (size.start_byte * 8)) & mask))
                },
                (Value::Bytes(current), Value::Bytes(new)) => {
                    new_bytes = current
                        .iter()
                        .copied()
                        .take(size.start_byte)
                        .chain(new.iter().copied().take(size.end_byte - size.start_byte + 1))
                        .chain(current.iter().copied().skip(size.end_byte + 1))
                        .collect::<Vec<_>>();

                    Value::Bytes(&new_bytes)
                },
                (_, new) => *new,
            }
        };

        self.set_location(&loc, sliced)
    }

    /// Allows the value of `dest` to be modified through a [`MutValue`].
    pub fn modify_dest(&mut self, dest: &Dest<A>, modify: impl FnOnce(MutValue<'_>)) {
        match dest {
            Dest::Reg(reg, size) => self.cpu_mut().modify_reg(*reg, |value| match value {
                MutValue::Num(current) => {
                    let w = (size.end_byte - size.start_byte + 1) * 8;
                    let unshifted_mask = if w == 64 { 0xffff_ffff_ffff_ffff } else { (1 << w) - 1 };
                    let mask = unshifted_mask << (size.start_byte * 8);
                    let mut val = (*current >> (size.start_byte * 8)) & unshifted_mask;
                    modify(MutValue::Num(&mut val));

                    *current = (*current & !mask) | ((val << (size.start_byte * 8)) & mask);
                },
                MutValue::Bytes(bytes) => modify(MutValue::Bytes(&mut bytes[size.start_byte..=size.end_byte])),
            }),
            Dest::Mem(index, size) => self
                .memory_mut()
                .get_mut(*index)
                .modify_data(|bytes| modify(MutValue::Bytes(&mut bytes[size.start_byte..=size.end_byte]))),
        }
    }

    /// Writes the value of `reg`.
    #[inline]
    pub fn set_reg(&mut self, reg: A::Reg, new_value: Value) {
        self.cpu_mut().modify_reg(reg, |value| match (value, new_value) {
            (MutValue::Num(dst), Value::Num(src)) => *dst = src,
            (MutValue::Bytes(dst), Value::Bytes(src)) => dst.copy_from_slice(src),
            v => panic!("Set register not matching: {v:?}"),
        })
    }

    /// Returns a new [`SystemState`] where `dest` is set to `v`.
    #[inline]
    pub fn with_dest(&self, dest: &Dest<A>, v: &Value<'_>) -> Self {
        let mut result = self.clone();
        result.set_dest(dest, v);
        result
    }

    /// Writes `value` to the flag `flag`.
    #[inline]
    pub fn set_flag(&mut self, flag: A::Flag, value: bool) {
        self.cpu_mut().set_flag(flag, value)
    }

    /// Writes the value of `loc`.
    pub fn set_location(&mut self, loc: &Location<A>, value: Value) {
        match (loc, value) {
            (Location::Reg(reg), value) => self.set_reg(*reg, value),
            (Location::Memory(index), Value::Bytes(v)) => {
                self.memory_mut().get_mut(*index).modify_data(|target| {
                    target.copy_from_slice(v);
                });
            },
            (loc, value) => panic!("Unsupported (location, value) pair: {loc:?} and {value:?}"),
        }
    }

    /// Returns the value of `loc`.
    pub fn location(&self, loc: &Location<A>) -> Value<'_> {
        match loc {
            Location::Reg(reg) => self.cpu().reg(*reg),
            Location::Memory(n) => Value::Bytes(&self.memory().get(*n).2),
        }
    }

    /// Returns the value of `loc`, or returns `None` if `loc` refers to a non-existant memory access.
    pub fn get_location(&self, loc: &Location<A>) -> Option<Value<'_>> {
        match loc {
            Location::Reg(reg) => Some(self.cpu().reg(*reg)),
            Location::Memory(n) => self.memory().get_checked(*n).as_ref().map(|v| Value::Bytes(&v.2)),
        }
    }
}

/// NOTE: This value will be copied around a few times. Make sure it's small enough!
pub trait AsSystemState<A: Arch> {
    /// The output type of [`Self::as_system_state`].
    type Output<'a>: AsRef<SystemState<A>>
    where
        Self: 'a;

    /// Returns a type that implements `AsRef<SystemState<A>>`.
    /// Should be a cheap operation, as it may be called often.
    fn as_system_state(&self) -> Self::Output<'_>;

    /// Returns the number of memory mappings in the state that [`Self::as_system_state`] will return.
    fn num_memory_mappings(&self) -> usize {
        self.as_system_state().as_ref().memory().len()
    }
}

impl<A: Arch, T> AsSystemState<A> for (SystemState<A>, T) {
    type Output<'a> = &'a SystemState<A>
        where Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::arch::fake::{FakeArch, FakeReg, FakeState};
    use crate::encoding::dataflows::{Dest, Size};
    use crate::state::{CpuState, MutValue, SystemState, Value};

    #[test]
    pub fn set_dest_flag() {
        let state = FakeState::create(|_, value| match value {
            MutValue::Num(n) => *n = 0x0101,
            MutValue::Bytes(_) => (),
        });
        let mut s = SystemState::<FakeArch>::new_without_memory(state);
        assert!(match s.get_dest(&Dest::Reg(FakeReg::RF, Size::new(1, 1))) {
            Value::Num(n) => n == 1,
            _ => panic!(),
        });

        s.set_dest(&Dest::Reg(FakeReg::RF, Size::new(1, 1)), &Value::Num(0));

        assert!(match s.get_dest(&Dest::Reg(FakeReg::RF, Size::new(0, 0))) {
            Value::Num(n) => n == 1,
            _ => panic!(),
        });

        assert!(match s.get_dest(&Dest::Reg(FakeReg::RF, Size::new(1, 1))) {
            Value::Num(n) => n == 0,
            _ => panic!(),
        });
    }

    #[test]
    pub fn set_dest_byte() {
        let state = FakeState::create(|_, value| match value {
            MutValue::Num(n) => *n = 0,
            MutValue::Bytes(_) => (),
        });
        let mut s = SystemState::<FakeArch>::new_without_memory(state);
        assert!(match s.get_dest(&Dest::Reg(FakeReg::R1, Size::new(1, 1))) {
            Value::Num(n) => n == 0,
            _ => panic!(),
        });

        s.set_dest(&Dest::Reg(FakeReg::R1, Size::new(1, 1)), &Value::Num(0x25));

        assert!(match s.get_dest(&Dest::Reg(FakeReg::R0, Size::new(1, 1))) {
            Value::Num(n) => n == 0,
            _ => panic!(),
        });

        assert!(match s.get_dest(&Dest::Reg(FakeReg::R1, Size::new(1, 1))) {
            Value::Num(n) => n == 0x25,
            _ => panic!(),
        });
    }
}
