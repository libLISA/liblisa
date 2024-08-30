use std::fmt::{Debug, Display};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::arch::{Arch, Register};
use crate::state::{Location, LocationKind};
use crate::value::ValueType;

/// A range of bytes.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Size {
    /// The lowest index included in the range.
    pub start_byte: usize,

    /// The highest index included in the range.
    pub end_byte: usize,
}

impl Default for Size {
    fn default() -> Self {
        Size {
            start_byte: usize::MIN,
            end_byte: usize::MAX,
        }
    }
}

impl Size {
    /// Creates a new range from the provided values.
    #[inline]
    pub const fn new(start_byte: usize, end_byte: usize) -> Self {
        Size {
            start_byte,
            end_byte,
        }
    }

    /// Returns `Size::new(0, 7)`.
    #[inline]
    pub const fn qword() -> Self {
        Size {
            start_byte: 0,
            end_byte: 7,
        }
    }

    /// Returns a union of the two ranges.
    #[inline]
    pub fn union(&self, other: &Self) -> Self {
        Size {
            start_byte: self.start_byte.min(other.start_byte),
            end_byte: self.end_byte.max(other.end_byte),
        }
    }

    /// Returns true if the size contains `other`.
    #[inline]
    pub fn contains(&self, other: &Self) -> bool {
        self.start_byte <= other.start_byte && self.end_byte >= other.end_byte
    }

    /// Returns true if the size and `other` overlap.
    #[inline]
    pub fn overlaps(&self, other: &Self) -> bool {
        self.end_byte >= other.start_byte && self.start_byte <= other.end_byte
    }

    /// Returns the overlapping area between the two sizes.
    /// If the two sizes do not overlap, returns None.
    #[inline]
    pub fn overlapping_area(&self, other: Size) -> Option<Size> {
        let start_byte = self.start_byte.max(other.start_byte);
        let end_byte = self.end_byte.min(other.end_byte);

        if start_byte <= end_byte {
            Some(Size {
                start_byte,
                end_byte,
            })
        } else {
            None
        }
    }

    /// Computes the union of the two sizes, and splits it by overlapping area.
    /// Returns None is the sizes do not overlap.
    ///
    /// Returns a triple of `(before, overlapping, after)`.
    /// `before` is the area in the union < `overlapping`.
    /// `overlapping` is the overlapping area between the two sizes.
    /// `after` is the area in the union > `overlapping`.
    pub fn split_by_overlap(&self, existing_size: Size) -> Option<(Option<Size>, Size, Option<Size>)> {
        let union = self.union(&existing_size);
        self.overlapping_area(existing_size).map(|overlapping| {
            let before = if overlapping.start_byte > union.start_byte {
                Some(Size::new(union.start_byte, overlapping.start_byte - 1))
            } else {
                None
            };

            let after = if overlapping.end_byte < union.end_byte {
                Some(Size::new(overlapping.end_byte + 1, union.end_byte))
            } else {
                None
            };

            (before, overlapping, after)
        })
    }

    /// The number of bytes in the size.
    #[inline]
    pub fn num_bytes(&self) -> usize {
        (self.end_byte - self.start_byte) + 1
    }

    /// If the size and `other` occur consecutively one after the other, returns a size that contains both.
    #[inline]
    pub fn try_glue(&self, other: &Size) -> Option<Size> {
        Some(if self.end_byte + 1 == other.start_byte {
            Size::new(self.start_byte, other.end_byte)
        } else if self.start_byte == other.end_byte + 1 {
            Size::new(other.start_byte, self.end_byte)
        } else {
            return None
        })
    }

    /// Crops `mask` to only have bits set in the area described by this size.
    #[inline]
    pub fn select_mask(&self, mask: Option<u64>) -> Option<u64> {
        mask.map(|mask| {
            let shift = self.start_byte * 8;
            let select = (1 << (self.num_bytes() * 8)) - 1;

            (mask >> shift) & select
        })
    }

    /// Returns an iterator that yields all byte indices in this size
    pub fn iter_byte_indices(&self) -> impl Iterator<Item = usize> {
        self.start_byte..=self.end_byte
    }
}

impl Debug for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.end_byte < self.start_byte {
            write!(f, "-")
        } else {
            write!(f, "{}..{}", self.start_byte, self.end_byte)
        }
    }
}

/// A destination in a dataflow.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(bound(serialize = "", deserialize = ""))]
pub enum Dest<A: Arch> {
    /// A specific area of a register.
    Reg(A::Reg, Size),

    /// A specific area of a memory access.
    Mem(usize, Size),
}

/// A source in a dataflow
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(bound(serialize = "", deserialize = ""))]
pub enum Source<A: Arch> {
    /// A destination.
    Dest(Dest<A>),

    /// The value of an immediate
    Imm(usize),

    /// A constant value.
    Const {
        /// The actual constant value.
        /// Should not have any bits above `num_bits` set.
        value: u64,

        /// The bitsize of the constant value.
        num_bits: usize,
    },
}

impl<A: Arch> PartialEq<Location<A>> for Dest<A> {
    fn eq(&self, other: &Location<A>) -> bool {
        match (self, other) {
            (Dest::Reg(a, _), Location::Reg(b)) => a == b,
            (Dest::Mem(a, _), Location::Memory(b)) => a == b,
            _ => false,
        }
    }
}

impl<R: Register, A: Arch<Reg = R>> PartialEq<R> for Dest<A> {
    fn eq(&self, other: &R) -> bool {
        match self {
            Dest::Reg(reg, _) => reg == other,
            _ => false,
        }
    }
}

impl<A: Arch> PartialEq<Location<A>> for Source<A> {
    fn eq(&self, other: &Location<A>) -> bool {
        match self {
            Source::Dest(d) => d == other,
            Source::Imm(_)
            | Source::Const {
                ..
            } => false,
        }
    }
}

impl<R: Register, A: Arch<Reg = R>> PartialEq<R> for Source<A> {
    fn eq(&self, other: &R) -> bool {
        match self {
            Source::Dest(Dest::Reg(reg, _)) => reg == other,
            Source::Imm(_)
            | Source::Const {
                ..
            }
            | Source::Dest {
                ..
            } => false,
        }
    }
}

impl<A: Arch> Dest<A> {
    /// The size of the destination.
    #[inline]
    pub fn size(&self) -> Size {
        match self {
            Dest::Reg(_, size) | Dest::Mem(_, size) => *size,
        }
    }

    /// Replaces the size of the destination with the provided `size`.
    #[inline]
    pub fn with_size(&self, size: Size) -> Self {
        match self {
            Dest::Reg(r, _) => Dest::Reg(*r, size),
            Dest::Mem(a, _) => Dest::Mem(*a, size),
        }
    }

    /// Returns true if the destination fully contains `other`.
    #[inline]
    pub fn contains(&self, other: &Dest<A>) -> bool {
        match (self, other) {
            (Dest::Reg(r1, s1), Dest::Reg(r2, s2)) => r1 == r2 && s1.contains(s2),
            (Dest::Mem(m1, s1), Dest::Mem(m2, s2)) => m1 == m2 && s1.contains(s2),
            _ => false,
        }
    }

    /// Returns true if the destination is a flags register.
    #[inline]
    pub fn is_flags(&self) -> bool {
        match self {
            Dest::Reg(reg, _) => reg.is_flags(),
            Dest::Mem(..) => false,
        }
    }

    /// Returns the mask of the destination, if it has one.
    /// The value of the destination must always be masked with the mask before setting it.
    #[inline]
    pub fn mask(&self) -> Option<u64> {
        match self {
            Dest::Reg(reg, size) => reg
                .mask()
                .map(|m| (m >> (size.start_byte * 8)) & (u64::MAX >> (64 - size.num_bytes() * 8))),
            _ => None,
        }
    }

    /// Returns the [`LocationKind`] of the destination.
    #[inline]
    pub fn kind(&self) -> LocationKind {
        match self {
            Dest::Reg(..) => LocationKind::Reg,
            Dest::Mem(..) => LocationKind::Memory,
        }
    }

    /// Returns true if the destination (partially or completely) overlaps with `other`.
    /// Destinations overlap if both destinations are the same register or the same memory access, and the size overlaps.
    pub fn overlaps(&self, other: &Dest<A>) -> bool {
        self.overlapping_area(other).is_some()
    }

    /// Returns the overlapping area between this destination and `other`.
    /// Returns `None` if there is no overlap.
    pub fn overlapping_area(&self, other: &Dest<A>) -> Option<Size> {
        match (self, other) {
            (Dest::Reg(reg_a, size_a), Dest::Reg(reg_b, size_b)) if reg_a == reg_b => size_a.overlapping_area(*size_b),
            (Dest::Mem(index_a, size_a), Dest::Mem(index_b, size_b)) if index_a == index_b => size_a.overlapping_area(*size_b),
            _ => None,
        }
    }

    /// Returns the [`ValueType`] of the destination.
    pub fn value_type(&self) -> ValueType {
        match self {
            Dest::Reg(reg, size) => match reg.reg_type() {
                ValueType::Num => ValueType::Num,
                ValueType::Bytes(_) => ValueType::Bytes(size.num_bytes()),
            },
            Dest::Mem(_, size) => ValueType::Bytes(size.num_bytes()),
        }
    }
}

impl<A: Arch> Source<A> {
    /// Returns the size of the source, if it has one.
    #[inline]
    pub fn size(&self) -> Option<Size> {
        match self {
            Source::Dest(d) => Some(d.size()),
            Source::Const {
                num_bits, ..
            } => Some(Size::new(0, (num_bits - 1) / 8)),
            Source::Imm(_) => None,
        }
    }

    /// Returns true if this source fully contains `other`.
    #[inline]
    pub fn contains(&self, other: &Source<A>) -> bool {
        match (self, other) {
            (Source::Dest(a), Source::Dest(b)) => a.contains(b),
            _ => false,
        }
    }

    /// Returns the destination if this source is a `Source::Dest`.
    /// Panics otherwise.
    #[inline]
    pub fn unwrap_dest(self) -> Dest<A> {
        match self {
            Source::Dest(d) => d,
            other => panic!("Tried to unwrap a Dest in {other:?}, but it contains no Dest"),
        }
    }

    /// Returns true if the source is a flags register.
    #[inline]
    pub fn is_flags(&self) -> bool {
        match self {
            Source::Dest(d) => d.is_flags(),
            _ => false,
        }
    }

    /// Returns the mask of the source.
    /// See [`Dest::mask`].
    #[inline]
    pub fn mask(&self) -> Option<u64> {
        match self {
            Source::Dest(d) => d.mask(),
            _ => panic!(),
        }
    }

    /// Returns true if the value of this source can be changed in the CPU state.
    /// Returns false if the value of this source is a constant or an immediate value from the instruction bitstring.
    #[inline]
    pub fn can_modify(&self) -> bool {
        match self {
            Source::Dest(_) => true,
            Source::Imm(_)
            | Source::Const {
                ..
            } => false,
        }
    }

    /// Replaces the size of this source with `size`, if possible.
    /// If the source has no size, the original source is returned.
    pub fn with_size(&self, size: Size) -> Source<A> {
        match self {
            Source::Dest(d) => Source::Dest(d.with_size(size)),
            other => *other,
        }
    }
}

impl<A: Arch> Debug for Dest<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Dest::Reg(reg, size) => write!(f, "Reg({reg})[{size:?}]"),
            Dest::Mem(index, size) => write!(f, "Mem{index}[{size:?}]"),
        }
    }
}

impl<A: Arch> Debug for Source<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Source::Imm(index) => write!(f, "v{index}"),
            Source::Dest(d) => write!(f, "{d:?}"),
            Source::Const {
                value, ..
            } => write!(f, "0x{value:X}"),
        }
    }
}

impl<A: Arch> Display for Dest<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Dest::Reg(reg, size) => {
                if reg.is_flags() && size.num_bytes() == 1 {
                    let flags = A::flagreg_to_flags(*reg, size.start_byte, size.end_byte);
                    write!(f, "Flag({})", flags.iter().map(|f| f.to_string()).join(", "))
                } else {
                    write!(f, "Reg({reg})[{size:?}]")
                }
            },
            Dest::Mem(index, size) => write!(f, "Mem{index}[{size:?}]"),
        }
    }
}

impl<A: Arch> Display for Source<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Source::Imm(index) => write!(f, "v{index}"),
            Source::Dest(d) => write!(f, "{d}"),
            Source::Const {
                value, ..
            } => write!(f, "0x{value:X}"),
        }
    }
}

impl<A: Arch> From<Dest<A>> for Source<A> {
    #[inline]
    fn from(d: Dest<A>) -> Source<A> {
        Source::Dest(d)
    }
}

impl<A: Arch> TryFrom<Source<A>> for Dest<A> {
    type Error = ();

    #[inline]
    fn try_from(s: Source<A>) -> Result<Dest<A>, ()> {
        match s {
            Source::Dest(d) => Ok(d),
            _ => Err(()),
        }
    }
}

impl<A: Arch> From<Location<A>> for Dest<A> {
    #[inline]
    fn from(location: Location<A>) -> Dest<A> {
        match location {
            Location::Reg(reg) => Dest::Reg(reg, Size::new(0, reg.byte_size() - 1)),
            Location::Memory(index) => Dest::Mem(index, Size::qword()),
        }
    }
}

impl<A: Arch> From<Dest<A>> for Location<A> {
    #[inline]
    fn from(dest: Dest<A>) -> Location<A> {
        match dest {
            Dest::Reg(reg, _) => Location::Reg(reg),
            Dest::Mem(index, _) => Location::Memory(index),
        }
    }
}

impl<A: Arch> From<&Source<A>> for Option<Location<A>> {
    #[inline]
    fn from(v: &Source<A>) -> Self {
        Location::try_from(v).ok()
    }
}

/// Types that implement this trait can be converted into destinations, given a size.
pub trait IntoDestWithSize<A: Arch> {
    /// Converts `self` into a [`Dest`].
    fn into_dest_with_size(self, size: Size) -> Dest<A>;
}

/// Types that implement this trait can be converted into sources, given a size.
pub trait IntoSourceWithSize<A: Arch> {
    /// Converts `self` into a [`Source`].
    fn into_source_with_size(self, size: Size) -> Source<A>;
}

impl<A: Arch> IntoDestWithSize<A> for Location<A> {
    #[inline]
    fn into_dest_with_size(self, size: Size) -> Dest<A> {
        match self {
            Location::Reg(reg) => Dest::Reg(reg, size),
            Location::Memory(index) => Dest::Mem(index, size),
        }
    }
}

impl<A: Arch> IntoSourceWithSize<A> for Location<A> {
    #[inline]
    fn into_source_with_size(self, size: Size) -> Source<A> {
        Source::Dest(self.into_dest_with_size(size))
    }
}

impl<A: Arch> From<&Dest<A>> for Location<A> {
    #[inline]
    fn from(dest: &Dest<A>) -> Self {
        match dest {
            Dest::Reg(reg, _) => Location::Reg(*reg),
            Dest::Mem(index, _) => Location::Memory(*index),
        }
    }
}

impl<A: Arch> TryFrom<&Source<A>> for Location<A> {
    type Error = ();

    #[inline]
    fn try_from(source: &Source<A>) -> Result<Self, Self::Error> {
        match source {
            Source::Dest(d) => Ok(d.into()),
            Source::Imm(_)
            | Source::Const {
                ..
            } => Err(()),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::encoding::dataflows::Size;

    #[test]
    pub fn size_contains() {
        assert!(Size::new(0, 7).contains(&Size::new(0, 5)));
        assert!(Size::new(0, 7).contains(&Size::new(0, 7)));
        assert!(Size::new(0, 7).contains(&Size::new(0, 6)));
        assert!(!Size::new(0, 7).contains(&Size::new(0, 8)));
        assert!(Size::new(0, 7).contains(&Size::new(1, 7)));
        assert!(!Size::new(1, 7).contains(&Size::new(0, 7)));
    }
}
