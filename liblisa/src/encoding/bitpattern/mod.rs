//! Types representing the bitpattern in an [`Encoding`](super::Encoding).

use std::fmt::Debug;

use serde::{Deserialize, Serialize};

use crate::arch::Arch;
use crate::encoding::AddressComputation;
use crate::utils::EitherIter;

mod locs;
pub use locs::*;

/// The maximum number of supported parts in an encoding.
pub const MAX_PARTS: usize = 32;

/// Single-letter names for the parts.
pub const PART_NAMES: &[&str] = &[
    "a", "b", "c", "d", "e", "f", "g", "h", "j", "k", "m", "n", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
];

/// The purpose of a bit in an encoding.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Bit {
    /// A bit that belongs to a part.
    Part(usize),

    // TODO: Enforce correctness via typing
    /// A fixed bit.
    /// Can either be `Fixed(0)` or `Fixed(1)`.
    /// Other values should not be used.
    Fixed(u8),

    /// A "DontCare" bit.
    /// Can be either 0 or 1.
    /// Does not have an effect on the behavior of the instruction.
    DontCare,
}

impl Bit {
    /// Returns `n` in `Bit::Fixed(n)`.
    /// Panics if the bit is not `Bit::Fixed`.
    pub fn unwrap_fixed(&self) -> u8 {
        match self {
            Bit::Fixed(n) => *n,
            _ => panic!(),
        }
    }

    /// Returns `Some(n)` if bit is `Bit::Part(n)`.
    /// Otherwise, returns `None`.
    pub fn part_index(&self) -> Option<usize> {
        match self {
            Bit::Part(index) => Some(*index),
            _ => None,
        }
    }
}

impl Debug for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bit::Part(n) => f.write_str(PART_NAMES[*n]),
            Bit::Fixed(v) => write!(f, "{v}"),
            Bit::DontCare => f.write_str("_"),
        }
    }
}

/// Represents whether a specific immediate value is valid or invalid.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PartValue {
    /// The immediate value is valid.
    Valid,

    /// The immediate value is invalid.
    Invalid,
}

impl PartValue {
    /// Returns true if the `PartValue` is `PartValue::Valid`.
    pub fn is_valid(&self) -> bool {
        self == &PartValue::Valid
    }

    /// Returns true if the `PartValue` is `PartValue::Invalid`.
    pub fn is_invalid(&self) -> bool {
        self == &PartValue::Invalid
    }
}

/// The bit ordering of bits in a memory address immediate value.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum ImmBitOrder {
    /// The bit adds `2**N` when set.
    Positive(usize),

    /// The bit subtracts `2**N` when set.
    Negative(usize),
}

impl ImmBitOrder {
    /// Converts the `ImmBitOrder` to an offset (either `2**N` or `-2**N`), then converts this to an unsigned `u64`.
    pub fn as_offset(&self, source_bit: u64) -> u64 {
        match self {
            ImmBitOrder::Positive(bit) => source_bit << bit,
            ImmBitOrder::Negative(bit) => (!(source_bit << bit)).wrapping_add(1),
        }
    }
}

/// Part mapping for an immediate value.
/// If the immediate value is used in a memory address, `MappingOrBitorder::BitOrder` is used.
/// Otherwise, `MappingOrBitOrder::Mapping` is used.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum MappingOrBitOrder {
    /// A mapping that maps each immediate value to [`PartValue::Valid`] or [`PartValue::Invalid`].
    Mapping(Vec<PartValue>),

    /// A bit ordering for a memory address immediate value.
    BitOrder(Vec<ImmBitOrder>),
}

/// The source of an immediate value bits.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum ImmBit {
    /// The bit is fixed to 0.
    Is0,

    /// The bit is fixed to 1.
    Is1,

    /// The bit is filled from the instruction bitstring.
    Fill,
}

/// The sources of the immediate value bits.
///
/// When bits are removed from an immediate value part, the interpretation might change.
/// This can be a problem when we have already synthesized a computation that uses the immediate value.
///
/// In such a case, we keep track of which bits we remove to be able to recover the correct value to pass to the synthesized computation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct ImmBits(Vec<ImmBit>);

impl ImmBits {
    /// Creates a new set of `ImmBits`
    pub fn new(iter: impl Iterator<Item = ImmBit>) -> Self {
        Self(iter.collect())
    }

    /// Interprets a part value as an immediate value, using the immediate bits.
    pub fn interpret_value(&self, value: u64) -> u64 {
        let mut result = 0;
        let mut data = value;

        for (index, bit) in self.0.iter().enumerate() {
            let val = match bit {
                ImmBit::Is0 => 0,
                ImmBit::Is1 => 1,
                ImmBit::Fill => {
                    let val = data & 1;
                    data >>= 1;
                    val
                },
            };

            result |= val << index;
        }

        result
    }

    /// Iterates over all bits.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = ImmBit> + '_ {
        self.0.iter().copied()
    }

    /// Iterates over all bits, but returns mutable references.
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut ImmBit> {
        self.0.iter_mut()
    }

    /// Returns the number of bits in this set.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if there are no bits in this set.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A part mapping in an encodin.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(bound = "")]
pub enum PartMapping<A: Arch> {
    /// An immediate value part mapping.
    Imm {
        /// A mapping of valid immediate values, or a bit ordering.
        mapping: Option<MappingOrBitOrder>,

        /// The input locations affected by this part.
        /// All input locations should be [`Source::Imm`](super::Source::Imm)s.
        locations: Vec<FlowInputLocation>,

        /// Keeps track of what bits we removed with remove_bit.
        /// Is not used if the immediate value is only used in a memory access (in that case MappingOrBitorder::BitOrder suffices).
        #[serde(default)]
        bits: Option<ImmBits>,
    },
    /// A memory computation part mapping.
    MemoryComputation {
        /// The possible memory computations.
        mapping: Vec<Option<AddressComputation>>,

        /// The memory indices affected by this part.
        memory_indexes: Vec<usize>,
    },
    /// A register part mapping.
    Register {
        /// The possible registers.
        mapping: Vec<Option<A::Reg>>,

        /// The sources/destinations that are affected by this part.
        /// All sources/destinatons should be [`Source::Dest`]([`Dest::Reg`])s.
        locations: Vec<FlowValueLocation>,
    },
}

impl<A: Arch> PartMapping<A> {
    /// Returns the mapping of registers if the part mapping is a register part mapping.
    /// Otherwise, returns `None`.
    pub fn register_mapping(&self) -> Option<&[Option<A::Reg>]> {
        match self {
            PartMapping::Register {
                mapping, ..
            } => Some(mapping),
            _ => None,
        }
    }

    /// Returns an iterator that iterates over all valid values for this part.
    pub fn valid_values(&self) -> Option<impl Iterator<Item = usize> + '_> {
        match self {
            PartMapping::Imm {
                mapping: Some(MappingOrBitOrder::Mapping(mapping)),
                ..
            } if mapping.iter().any(PartValue::is_invalid) => Some(EitherIter::Left(EitherIter::Left(
                mapping
                    .iter()
                    .enumerate()
                    .filter(|(_, &item)| item == PartValue::Valid)
                    .map(|(index, _)| index),
            ))),
            PartMapping::MemoryComputation {
                mapping, ..
            } if mapping.iter().any(Option::is_none) => Some(EitherIter::Left(EitherIter::Right(
                mapping
                    .iter()
                    .enumerate()
                    .filter(|(_, &item)| item.is_some())
                    .map(|(index, _)| index),
            ))),
            PartMapping::Register {
                mapping, ..
            } if mapping.iter().any(Option::is_none) => Some(EitherIter::Right(
                mapping
                    .iter()
                    .enumerate()
                    .filter(|(_, &item)| item.is_some())
                    .map(|(index, _)| index),
            )),
            _ => None,
        }
    }

    /// Returns the smallest valid value for this part.
    pub fn first_valid_value(&self) -> u64 {
        match self.valid_values() {
            Some(mut iter) => iter.next().unwrap() as u64,
            None => 0,
        }
    }

    /// Returns whether the value `val` is valid for this part.
    pub fn value_is_valid(&self, val: u64) -> bool {
        match self {
            PartMapping::Imm {
                mapping: Some(MappingOrBitOrder::Mapping(mapping)),
                ..
            } if mapping.iter().any(PartValue::is_invalid) => mapping[val as usize] == PartValue::Valid,
            PartMapping::MemoryComputation {
                mapping, ..
            } if mapping.iter().any(Option::is_none) => mapping[val as usize].is_some(),
            PartMapping::Register {
                mapping, ..
            } if mapping.iter().any(Option::is_none) => mapping[val as usize].is_some(),
            _ => true,
        }
    }
}

/// A part in an [`Encoding`](super::Encoding).
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(bound = "")]
pub struct Part<A: Arch> {
    /// The number of bits in this part.
    pub size: usize,

    /// The current value of the part.
    pub value: u64,

    /// The mapping of the part.
    pub mapping: PartMapping<A>,
}

impl<A: Arch> Part<A> {
    /// Get the part's size.
    pub fn size(&self) -> usize {
        self.size
    }
}
