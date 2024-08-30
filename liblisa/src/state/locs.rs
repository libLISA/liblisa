use std::fmt::Debug;

use serde::{Deserialize, Serialize};

use crate::arch::{Arch, Register};
use crate::value::ValueType;

/// The kind of a storage location.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum LocationKind {
    /// A register.
    Reg,

    /// An accessed memory area.
    Memory,
}

/// A storage location in a CPU state.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Location<A: Arch> {
    /// A register
    Reg(A::Reg),

    /// The nth memory access.
    Memory(usize),
}

impl<A: Arch> Location<A> {
    /// Returns the type of the location.
    pub fn kind(&self) -> LocationKind {
        match self {
            Location::Reg(_) => LocationKind::Reg,
            Location::Memory(_) => LocationKind::Memory,
        }
    }

    /// Returns true if this location has the same [`ValueType`] as `other`.
    pub fn matches_value_type_with(&self, other: &Location<A>) -> bool {
        match (self, other) {
            (Location::Reg(a), Location::Reg(b)) => a.reg_type() == b.reg_type(),
            (Location::Reg(r), Location::Memory(_)) => matches!(r.reg_type(), ValueType::Bytes(_)),
            (Location::Memory(_), Location::Reg(r)) => matches!(r.reg_type(), ValueType::Bytes(_)),
            (Location::Memory(_), Location::Memory(_)) => true,
        }
    }

    /// Returns true if the location is a flags register.1
    pub fn is_flags(&self) -> bool {
        if let Location::Reg(reg) = self {
            reg.is_flags()
        } else {
            false
        }
    }
}

impl<A: Arch> Debug for Location<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Location::Reg(reg) => write!(f, "Reg[{reg}]")?,
            Location::Memory(index) => write!(f, "Memory[#{index}]")?,
        }

        Ok(())
    }
}
