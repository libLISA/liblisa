//! [`InstructionFilter`]s are used to reason over instruction space.
//! An encoding can return a set of filters representing the instruction space it covers.
//!
//! The various types in this module can be used to manipulate and query sets of [`InstructionFilter`]s.

use std::fmt::{Debug, Write};
use std::str::FromStr;

use arrayvec::ArrayVec;
use hex::FromHexError;
use log::trace;
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::arch::Arch;
use crate::encoding::EncodingWithFilters;
use crate::instr::extended::ExtendedFilter;
use crate::instr::Instruction;

/// Types that represent groups of instructions.
/// The group of instructions can be described using a set of filters.
pub trait WithFilters {
    /// Returns a set of (potentially overlapping) filters that cover the entire area covered by the type.
    fn filters(&self) -> &[InstructionFilter];
}

impl<A: Arch, C> WithFilters for EncodingWithFilters<A, C> {
    fn filters(&self) -> &[InstructionFilter] {
        &self.filters
    }
}

/// A bit in a filter.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FilterBit {
    /// Matches only a '0' bit.
    Is0,

    /// Matches only a '1' bit.
    Is1,

    /// Matches either a '0' or a '1' bit.
    Wildcard,
}

impl FilterBit {
    /// Returns the matching bit value as an u8, or `None` if the filter bit is a wildcard.
    pub fn as_u8(&self) -> Option<u8> {
        match self {
            FilterBit::Is0 => Some(0),
            FilterBit::Is1 => Some(1),
            FilterBit::Wildcard => None,
        }
    }
}

/// A filter that matches a single byte.
///
/// A value `b` matches the filter if `(b & self.mask) == self.value`.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ByteFilter {
    /// The mask applied to the byte value.
    ///
    /// If a bit is 1, it indicates the bit must be matched to value.
    /// If it is 0, the bit can be ignored.
    /// In other words: the filter matches if (X & mask) == value
    pub mask: u8,

    /// The value to which the byte value is compared after masking.
    pub value: u8,
}

impl Debug for ByteFilter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in (0..8).rev() {
            if (self.mask >> i) & 1 == 1 {
                write!(f, "{}", (self.value >> i) & 1)?;
            } else {
                write!(f, "_")?;
            }
        }

        Ok(())
    }
}

impl ByteFilter {
    /// Creates a new [`ByteFilter`].
    pub fn new(mask: u8, value: u8) -> Self {
        debug_assert_eq!(value & !mask, 0, "Unset bits in mask should also be unset in value");
        ByteFilter {
            mask,
            value,
        }
    }

    /// Returns true if `value` matches the [`ByteFilter`].
    pub fn matches(&self, value: u8) -> bool {
        (value & self.mask) == self.value
    }

    /// Returns the largest value matched by the filter.
    pub fn max_matching_val(&self) -> u8 {
        self.value | !self.mask
    }

    /// Returns the smallest value matched by the filter.
    pub fn min_matching_val(&self) -> u8 {
        self.value & self.mask
    }

    /// Returns true if all 256 possible values for an `u8` match this filter.
    pub fn matches_anything(&self) -> bool {
        self.mask == 0
    }

    /// Returns true if all instructions matched by other are also matched by self
    pub fn covers(&self, other: &ByteFilter) -> bool {
        // Example: _ _ _ _ covers _ _ 0 1
        // Example: _ _ _ 0 covers 0 1 1 0
        self.value & self.mask == other.value & self.mask && other.mask & self.mask == self.mask
    }

    /// Returns true if the filters overlap.
    pub fn can_intersect(&self, other: &ByteFilter) -> bool {
        // Example: _ _ 1 _ can intersect with _ _ _ 0 into _ _ 1 0
        // Example: _ _ 0 _ can intersect with _ 1 _ _ into _ 1 0 _
        // Example: _ _ 1 1 CANNOT intersect with _ _ _ 0
        let intersect_mask = self.mask & other.mask;
        intersect_mask & self.value == intersect_mask & other.value
    }

    /// Returns true if the other filter can be merged into self.
    pub fn can_merge(&self, other: &ByteFilter) -> bool {
        if self.value == other.value && self.mask == other.mask {
            // If the filters are equal there's nothing to merge
            return false;
        }

        self.mask == other.mask && ((self.value ^ other.value) & other.mask).count_ones() == 1
    }

    /// Merges the other filter into self.
    pub fn merge(&mut self, other: &ByteFilter) {
        let filter = !((self.value ^ other.value) & other.mask);
        debug_assert_eq!(filter.count_ones(), 7, "merge() can only be called if can_merge returns true");

        self.mask &= filter;
        self.value &= filter;

        self.consistency_check();
    }

    /// Returns true if `self - other` can be computed.
    pub fn can_exclude(&self, other: &ByteFilter) -> bool {
        // A: 1_10__
        // B: 1____0
        // A excluding B is:
        //    1_10_1

        if other.covers(self) {
            // We would be excluding everything
            return false;
        }

        let combined_mask = self.mask & other.mask;

        (!self.mask & other.mask).count_ones() == 1 && self.value & combined_mask == other.value & combined_mask
    }

    /// Computes `self - other`.
    pub fn exclude(&mut self, other: &ByteFilter) {
        debug_assert!(self.can_exclude(other));

        let excluded_bit = !self.mask & other.mask;

        self.mask |= excluded_bit;
        self.value = (self.value & !excluded_bit) | (!other.value & excluded_bit);

        self.consistency_check();
    }

    /// Intersects `self` with `other`, storing the result in `self`.
    pub fn intersect(&mut self, other: &ByteFilter) {
        debug_assert!(
            self.can_intersect(other) || other.can_intersect(self),
            "intersect() can only be called if can_intersect(a, b) or can_intersect(b, a) returns true; {self:?} does not intersect with {other:?}"
        );

        let new_mask = self.mask | other.mask;

        debug_assert_eq!(
            self.value & other.mask,
            other.value & self.mask,
            "Unable to intersect {self:?} and {other:?}"
        );

        self.value |= other.value;
        self.mask = new_mask;

        self.consistency_check();
    }

    /// Returns the number of wildcard bits in the filter.
    pub fn num_wildcard_bits(&self) -> usize {
        self.mask.count_zeros() as usize
    }

    /// Returns the value matched by the filter, if the filter does not contain any wildcard bits.
    /// Otherwise, returns `None`.
    pub fn as_value(&self) -> Option<u8> {
        if self.mask == 0xff { Some(self.value) } else { None }
    }

    fn consistency_check(&self) {
        debug_assert_eq!(self.value & !self.mask, 0);
    }
}

/// A filter that can match groups of instructions.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstructionFilter {
    /// The filters for each byte in the instruction.
    pub data: ArrayVec<ByteFilter, 16>,
}

impl Clone for InstructionFilter {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.data.clone_from(&source.data)
    }
}

impl Debug for InstructionFilter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for bf in self.data.iter() {
            write!(f, "{bf:?} ")?;
        }

        Ok(())
    }
}

impl From<&str> for InstructionFilter {
    fn from(s: &str) -> Self {
        Self::from_str(s).unwrap()
    }
}

impl Serialize for InstructionFilter {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = String::new();
        for bf in self.data.iter() {
            match bf.mask {
                0x00 => s.push_str("__"),
                0xff => write!(&mut s, "{:02x}", bf.value).unwrap(),
                _ => write!(&mut s, "{:02x}:{:02x}", bf.value, bf.mask).unwrap(),
            }
        }

        serializer.serialize_str(&s)
    }
}

impl FromStr for InstructionFilter {
    type Err = FromHexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut data = ArrayVec::new();

        let mut s = s.trim();
        while !s.is_empty() {
            // Parse the value
            let (value, mask) = match &s[..2] {
                "__" => (0, Some(0)),
                hexval => {
                    let mut value = [0; 1];
                    hex::decode_to_slice(hexval, &mut value)?;
                    (value[0], None)
                },
            };
            s = &s[2..];

            // Check if we need a mask
            let mask = if let Some(mask) = mask {
                mask
            } else if s.len() >= 3 && &s[..1] == ":" {
                let mut mask = [0; 1];
                hex::decode_to_slice(&s[1..3], &mut mask)?;
                s = &s[3..];
                mask[0]
            } else {
                0xff
            };

            s = s.trim();
            data.push(ByteFilter::new(mask, value & mask));
        }

        Ok(InstructionFilter {
            data,
        })
    }
}

impl<'de> Deserialize<'de> for InstructionFilter {
    fn deserialize<D>(deserializer: D) -> Result<InstructionFilter, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct InstructionFilterVisitor;

        impl<'de> Visitor<'de> for InstructionFilterVisitor {
            type Value = InstructionFilter;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("an instruction filter string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(InstructionFilter::from(value))
            }
        }

        deserializer.deserialize_str(InstructionFilterVisitor)
    }
}

impl InstructionFilter {
    /// Creates a new [`InstructionFilter`] from the provided iterator.
    /// The iterator should not yield more than 15 elements.
    pub fn new<I: IntoIterator<Item = ByteFilter>>(data: I) -> InstructionFilter {
        InstructionFilter {
            data: data.into_iter().collect(),
        }
    }

    /// Parses an instruction filter from a string.
    pub fn parse(s: &str) -> InstructionFilter {
        let mut bfs = Vec::new();
        for part in s.split(' ') {
            let cs = part.chars().collect::<Vec<_>>();

            let mut bf = ByteFilter::new(0, 0);
            for i in (0..8).rev() {
                match cs[7 - i] {
                    '0' => bf.mask |= 1 << i,
                    '1' => {
                        bf.mask |= 1 << i;
                        bf.value |= 1 << i;
                    },
                    '_' => {},
                    _ => panic!(),
                }
            }

            bfs.push(bf);
        }

        let result = Self::new(bfs);
        println!("Parsed: {result:?} (from {s})");
        result
    }

    /// Computes the intersection of the [`InstructionFilter`]s.
    pub fn intersect(&self, other: &InstructionFilter) -> InstructionFilter {
        assert!(self.len() == other.len());

        InstructionFilter {
            data: self
                .data
                .iter()
                .zip(other.data.iter())
                .map(|(a, b)| {
                    let mut result = a.clone();
                    result.intersect(b);

                    result
                })
                .collect(),
        }
    }

    /// Returns true if the filter matches `instr`.
    pub fn matches(&self, instr: &Instruction) -> bool {
        for (i, bf) in self.data.iter().enumerate() {
            if let Some(idata) = instr.bytes().get(i) {
                if !bf.matches(*idata) {
                    return false;
                }
            } else if !bf.matches_anything() {
                // TODO: This else if seems undesirable.
                return false;
            }
        }

        true
    }

    /// Returns true if the filter matches all bytes in `instr`, even if not all instructions that start with `instr` are matched by this filter.
    ///
    /// For example: the filter `03AB` partially matches the instruction `03`.
    /// However, it does not match all instructions starting with `03`.
    /// For example, `0300`.
    pub fn matches_smaller_instr_partially(&self, instr: &Instruction) -> bool {
        if instr.byte_len() > self.len() {
            false
        } else {
            self.data.iter().zip(instr.bytes()).all(|(bf, idata)| bf.matches(*idata))
        }
    }

    /// Returns the byte length of the instructions matched by the [`InstructionFilter`].
    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the [`InstructionFilter`] is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the bitlength of the instructions matched by the [`InstructionFilter`].
    #[must_use]
    pub fn bit_len(&self) -> usize {
        self.data.len() * 8
    }

    /// Returns the byte length of the instructions matched by the [`InstructionFilter`].
    #[must_use]
    pub fn byte_len(&self) -> usize {
        self.data.len()
    }

    /// Returns the bit at position `index`, counting from the left.
    pub fn nth_bit_from_left(&self, index: usize) -> FilterBit {
        let byte = &self.data[index / 8];
        let bit = 7 - (index % 8);
        let val = (byte.value >> bit) & 1;
        let mask = (byte.mask >> bit) & 1;

        if mask == 1 {
            if val == 1 { FilterBit::Is1 } else { FilterBit::Is0 }
        } else {
            FilterBit::Wildcard
        }
    }

    /// Returns the bit at position `index`, counting from the right.
    pub fn nth_bit_from_right(&self, index: usize) -> FilterBit {
        self.nth_bit_from_left(self.bit_len() - 1 - index)
    }

    /// Returns the values of the [`ByteFilter`]s concatenated into an `u128`.
    pub fn value_as_u128(&self) -> u128 {
        self.data
            .iter()
            .map(|x| x.value)
            .fold(0, |acc, item| (acc << 8) | item as u128)
    }

    /// Returns the masks of the [`ByteFilter`]s concatenated into an `u128`.
    pub fn mask_as_u128(&self) -> u128 {
        self.data
            .iter()
            .map(|x| x.mask)
            .fold(0, |acc, item| (acc << 8) | item as u128)
    }

    /// Returns true if the filter matches all instructions matched by `other`.
    pub fn covers(&self, other: &InstructionFilter) -> bool {
        self.data.len() <= other.data.len() && self.data.iter().zip(other.data.iter()).all(|(a, b)| a.covers(b))
    }

    /// Returns true if there is at least one instruction which both filters match.
    pub fn overlaps(&self, other: &InstructionFilter) -> bool {
        self.data.iter().zip(other.data.iter()).all(|(a, b)| a.can_intersect(b))
    }

    /// Tries to merge the filters into a filter that matches all instructions matched by either self or `other`.
    pub fn try_merge(&self, other: &InstructionFilter) -> Option<InstructionFilter> {
        if self.data.len() != other.data.len() {
            return None;
        }

        #[cfg(debug_assertions)]
        self.data.iter().for_each(ByteFilter::consistency_check);

        #[cfg(debug_assertions)]
        other.data.iter().for_each(ByteFilter::consistency_check);

        for (merge_index, (a, b)) in self.data.iter().zip(other.data.iter()).enumerate() {
            if a.can_merge(b)
                && self
                    .data
                    .iter()
                    .zip(other.data.iter())
                    .skip(merge_index + 1)
                    .all(|(a, b)| a == b)
            {
                let mut new = self.clone();
                new.data[merge_index].merge(&other.data[merge_index]);
                return Some(new);
            }

            if a != b {
                break
            }
        }

        None
    }

    /// Tries to compute `self - other`.
    pub fn try_exclude(&self, other: &InstructionFilter) -> Option<InstructionFilter> {
        if self.data.len() != other.data.len() {
            return None;
        }

        let mut exclude_index = None;
        for (index, (a, b)) in self.data.iter().zip(other.data.iter()).enumerate() {
            if a.can_exclude(b)
                && self
                    .data
                    .iter()
                    .zip(other.data.iter())
                    .skip(index + 1)
                    .all(|(a, b)| b.covers(a))
            {
                exclude_index = Some(index);
            }

            if !b.covers(a) {
                break;
            }
        }

        if let Some(merge_index) = exclude_index {
            let mut new = self.clone();
            new.data[merge_index].exclude(&other.data[merge_index]);
            Some(new)
        } else {
            None
        }
    }

    /// Returns the smallest matching instruction. In other words, the instruction with all wildcard bits set to 0.
    pub fn smallest_matching_instruction(&self) -> Instruction {
        Instruction::from_iter(self.data.iter().map(|bf| bf.value & bf.mask))
    }

    /// Returns the largest matching instruction. In other words, the instruction with all wildcard bits set to 1.
    pub fn largest_matching_instruction(&self) -> Instruction {
        Instruction::from_iter(self.data.iter().map(|bf| (bf.value & bf.mask) | !bf.mask))
    }

    /// When instr does not match the filter, returns the first instruction after `instr` that matches the filter.
    /// When instr does match the filter, returns `instr`.
    pub fn next_matching_instruction(&self, instr: &Instruction) -> Option<Instruction> {
        if instr > &self.largest_matching_instruction() {
            None
        } else {
            let mut result = self.smallest_matching_instruction();
            trace!("Instr   : {instr:?}");
            trace!("Smallest: {result:?}");

            let len = result.bit_len().min(instr.bit_len());

            let mut bit = 0;
            while bit < len {
                match (instr.nth_bit_from_left(bit), result.nth_bit_from_left(bit)) {
                    (0, 0) | (1, 1) => (),
                    (1, 0) => {
                        if self.nth_bit_from_left(bit) == FilterBit::Wildcard {
                            result = result.with_nth_bit_from_left(bit, 1)
                        } else {
                            break
                        }
                    },
                    (0, 1) => break,
                    (..) => unreachable!(),
                }

                bit += 1;
            }

            trace!("Found something bigger or equal: {result:?}");

            if &result < instr {
                for bit in (0..len).rev() {
                    if self.nth_bit_from_left(bit) == FilterBit::Wildcard {
                        let val = result.nth_bit_from_left(bit);
                        trace!("Bit {bit} = {val}");
                        match val {
                            0 => {
                                let new = result.with_nth_bit_from_left(bit, 1);
                                if &new > instr {
                                    result = new;
                                    break
                                }
                            },
                            1 => {
                                // Carry
                                result = result.with_nth_bit_from_left(bit, 0);
                                trace!("Carry: {result:?}");
                            },
                            _ => (),
                        }
                    }
                }
            }

            Some(result)
        }
    }

    /// Returns the number of wildcard bits in the [`InstructionFilter`].
    pub fn num_wildcard_bits(&self) -> usize {
        self.data.iter().map(|f| f.num_wildcard_bits()).sum()
    }

    /// Sets the bit at position `index`, counting from the right, to `bit`.
    pub fn set_nth_bit_from_right(&mut self, index: usize, bit: FilterBit) {
        self.set_nth_bit_from_left(self.bit_len() - 1 - index, bit)
    }

    /// Sets the bit at position `index`, counting from the left, to `bit`.
    pub fn set_nth_bit_from_left(&mut self, index: usize, bit: FilterBit) {
        let byte = &mut self.data[index / 8];
        let bit_index = 7 - (index % 8);
        match bit {
            FilterBit::Is0 => {
                byte.mask |= 1 << bit_index;
                byte.value &= !(1 << bit_index);
            },
            FilterBit::Is1 => {
                byte.mask |= 1 << bit_index;
                byte.value |= 1 << bit_index;
            },
            FilterBit::Wildcard => {
                byte.mask &= !(1 << bit_index);
                byte.value &= !(1 << bit_index);
            },
        }
    }

    /// Returns an [`crate::instr::Instruction`] that matches this filter, but none of the filters in `covering_filters`.
    pub fn find_uncovered_instr(&self, covering_filters: Vec<InstructionFilter>) -> Option<Instruction> {
        ExtendedFilter::new_ex(self.clone(), covering_filters, false).map(|ef| ef.matching_instr())
    }
}

/// Attempts to merge all filters in the provided `filters`.
pub fn merge_filters(mut filters: Vec<InstructionFilter>) -> Vec<InstructionFilter> {
    for index in (0..filters.len()).rev() {
        loop {
            let item = &filters[index];

            if let Some((merged_index, merged)) = filters
                .iter()
                .enumerate()
                .skip(index + 1)
                .flat_map(|(index, other)| item.try_merge(other).map(|x| (index, x)))
                .next()
            {
                trace!(
                    "Removing {index} = {:?} because we merged it with {item:?} into {merged:?}",
                    filters[merged_index]
                );
                filters[index] = merged;
                filters.remove(merged_index);
            } else {
                break;
            }
        }
    }

    filters
}

impl From<Instruction> for InstructionFilter {
    fn from(instr: Instruction) -> Self {
        InstructionFilter::new(instr.bytes().iter().copied().map(|b| ByteFilter::new(0xff, b)))
    }
}

impl From<&Instruction> for InstructionFilter {
    fn from(instr: &Instruction) -> Self {
        InstructionFilter::new(instr.bytes().iter().copied().map(|b| ByteFilter::new(0xff, b)))
    }
}

#[cfg(test)]
mod tests {
    use crate::instr::{ByteFilter, Instruction, InstructionFilter};

    #[test]
    pub fn test_filter_redundancy() {
        let f1 = InstructionFilter::new(vec![
            ByteFilter::new(0xff, 0b10000011),
            ByteFilter::new(0b01110110, 0b00000100),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0b10, 0),
        ]);

        let f2 = InstructionFilter::new(vec![
            ByteFilter::new(0xff, 0b10000011),
            ByteFilter::new(0xff, 0b00001100),
            ByteFilter::new(0x01, 0x00),
            ByteFilter::new(0x80, 0x80),
        ]);

        assert!(!f1.covers(&f2));
    }

    #[test]
    pub fn bytefilter_match() {
        let bf = ByteFilter::new(0b1111_1100, 0b0010_1000);
        assert!(bf.matches(0b0010_1000));
        assert!(bf.matches(0b0010_1001));
        assert!(bf.matches(0b0010_1010));
        assert!(bf.matches(0b0010_1011));
        assert!(!bf.matches(0b1010_1011));
        assert!(!bf.matches(0b0110_1011));
        assert!(!bf.matches(0b0000_1011));
        assert!(!bf.matches(0b0011_1011));
        assert!(!bf.matches(0b0010_0011));
        assert!(!bf.matches(0b0010_1111));

        let bf = ByteFilter::new(0b0000_0001, 0b0000_0000);
        assert!(bf.matches(0b0000_0000));
        assert!(bf.matches(0b0000_0010));
    }

    #[test]
    pub fn bytefilter_covers() {
        let bf1 = ByteFilter::new(0b0011_1100, 0b0010_1000);
        let bf2 = ByteFilter::new(0b1111_1100, 0b1010_1000);

        assert!(bf1.covers(&bf1));
        assert!(bf2.covers(&bf2));
        assert!(bf1.covers(&bf2));
        assert!(!bf2.covers(&bf1));
    }

    #[test]
    pub fn bytefilter_max() {
        let bf = ByteFilter::new(0b0011_1100, 0b0010_1000);
        assert_eq!(bf.max_matching_val(), 0b1110_1011);

        let bf = ByteFilter::new(0b0000_0001, 0b0000_0001);
        assert_eq!(bf.max_matching_val(), 0b1111_1111);

        let bf = ByteFilter::new(0b0011_0000, 0b0000_0000);
        assert_eq!(bf.max_matching_val(), 0b1100_1111);

        let bf = ByteFilter::new(0b0000_0001, 0b0000_0000);
        assert_eq!(bf.max_matching_val(), 0b1111_1110);
    }

    #[test]
    pub fn bytefilter_merge() {
        let mut bf1 = ByteFilter::new(0b0010, 0b0000);
        let bf2 = ByteFilter::new(0b0010, 0b0010);
        assert!(bf1.can_merge(&bf2));

        bf1.merge(&bf2);
        assert_eq!(bf1, ByteFilter::new(0, 0));

        let m = ByteFilter::new(0b1010, 0b1010);
        assert!(!bf1.can_merge(&m));

        let bf3 = ByteFilter::new(0b1010, 0b0000);
        assert!(!bf3.can_merge(&m));

        let a1 = ByteFilter::new(0b0011_0010, 0b0001_0010);
        let a2 = ByteFilter::new(0b1001_1001, 0b1001_0001);
        let b1 = ByteFilter::new(0b0001_0010, 0b0001_0010);
        let b2 = ByteFilter::new(0b0000_0001, 0b0000_0000);

        assert!(!a1.can_merge(&b1));
        assert!(b1.covers(&a1));

        println!("{a2:?} merge {b2:?}");
        assert!(!a2.can_merge(&b2));
    }

    #[test]
    pub fn bytefilter_intersect() {
        let mut bf1 = ByteFilter::new(0b0010, 0b0000);
        let bf2 = ByteFilter::new(0b0100, 0b0100);

        assert!(bf1.can_intersect(&bf2));

        bf1.intersect(&bf2);
        assert_eq!(bf1, ByteFilter::new(0b0110, 0b0100));
    }

    #[test]
    pub fn bytefilter_exclude() {
        let mut bf1 = ByteFilter::new(0b0010, 0b0000);
        let bf2 = ByteFilter::new(0b0100, 0b0100);
        let bf3 = ByteFilter::new(0b1100, 0b0100);

        assert!(bf1.can_exclude(&bf2));
        assert!(!bf1.can_exclude(&bf3));

        bf1.exclude(&bf2);
        assert_eq!(bf1, ByteFilter::new(0b0110, 0b0000));
    }

    #[test]
    pub fn bytefilter_exclude_two_sides() {
        let mut bf1 = ByteFilter::new(0b1110_0000, 0b1110_0000);
        let bf2 = ByteFilter::new(0b0111_0000, 0b0110_0000);

        println!("{bf1:?} {bf2:?}");

        assert!(bf1.can_exclude(&bf2));

        bf1.exclude(&bf2);
        assert_eq!(bf1, ByteFilter::new(0b1111_0000, 0b1111_0000));
    }

    #[test]
    pub fn instruction_filter_exclude() {
        let f = InstructionFilter::parse("0000____");
        let g = InstructionFilter::parse("00___1__");

        assert_eq!(f.try_exclude(&g), Some(InstructionFilter::parse("0000_0__")));

        let f = InstructionFilter::parse("0111011_ ____0010");
        let g = InstructionFilter::parse("0111011_ 1_______");

        assert_eq!(f.try_exclude(&g), Some(InstructionFilter::parse("0111011_ 0___0010")));
    }

    #[test]
    pub fn instruction_filter_covers() {
        let f = InstructionFilter::parse("0000____");
        let g = InstructionFilter::parse("00000___");
        assert!(f.covers(&g));

        let f = InstructionFilter::parse("0000____");
        let g = InstructionFilter::parse("000_0___");
        assert!(!f.covers(&g));

        let f = InstructionFilter::parse("0000____");
        let g = InstructionFilter::parse("0001____");
        assert!(!f.covers(&g));

        let f = InstructionFilter::parse("0000____");
        let g = InstructionFilter::parse("0000____");
        assert!(f.covers(&g));

        let f = InstructionFilter::parse("0000____");
        let g = InstructionFilter::parse("00000__1");
        assert!(f.covers(&g));
    }

    #[test]
    pub fn instruction_filter() {
        let f = InstructionFilter::new(vec![
            ByteFilter::new(0b1111_1100, 0b0010_1000),
            ByteFilter::new(0b1001_1001, 0b1001_0001),
        ]);

        assert!(f.matches(&Instruction::new(&[0b0010_1000, 0b1001_0001])));
        assert!(f.matches(&Instruction::new(&[0b0010_1011, 0b1011_0111])));
        assert!(f.matches(&Instruction::new(&[0b0010_1000, 0b1001_0001, 0b1111_0000])));
        assert!(!f.matches(&Instruction::new(&[])));
        assert!(!f.matches(&Instruction::new(&[0b0010_1000])));

        assert!(!f.matches(&Instruction::new(&[0b0010_1011, 0b1011_1111])));

        let f = InstructionFilter::new(vec![ByteFilter::new(0, 0), ByteFilter::new(0b1000_0000, 0b0000_0000)]);
        assert!(!f.matches(&Instruction::new(&[1, 0b1000_0000])));
    }

    #[test]
    pub fn instruction_filter_redundancy() {
        let f = InstructionFilter::new(vec![
            ByteFilter::new(0b0011_0010, 0b0001_0010),
            ByteFilter::new(0b1001_1001, 0b1001_0001),
        ]);
        let g = InstructionFilter::new(vec![
            ByteFilter::new(0b0001_0010, 0b0001_0010),
            ByteFilter::new(0b0001_1001, 0b0001_0001),
        ]);

        assert!(!f.covers(&g));
        assert!(g.covers(&f));
    }

    #[test]
    pub fn instruction_filter_merge() {
        let f = InstructionFilter::parse("__01__1_ 1__10__1");
        let g = InstructionFilter::parse("__01__1_ 1__10__0");

        let expected = InstructionFilter::parse("__01__1_ 1__10___");

        println!("Merging: {f:?}");
        println!("With   : {g:?}");
        println!("Expect : {expected:?}");

        assert_eq!(f.try_merge(&g), Some(expected));
    }

    #[test]
    pub fn instruction_filter_merge_long() {
        let f = InstructionFilter::parse("10000011 00110101 01______ ________ ________ ________ ________");
        let g = InstructionFilter::parse("10000011 00110101 ________ ________ ________ _____100 ________");

        assert_eq!(f.try_merge(&g), None);
        assert_eq!(g.try_merge(&f), None);

        let f = InstructionFilter::parse("10000011 00110101 ________ ________ ________ ______10 ________");
        let g = InstructionFilter::parse("10000011 00110101 ________ _______1 ________ ________ ________");

        assert_eq!(f.try_merge(&g), None);
        assert_eq!(g.try_merge(&f), None);

        let f = InstructionFilter::parse("10000011 00110101 001_____ ________ ________ ________ ________");
        let g = InstructionFilter::parse("10000011 00110101 01______ ________ ________ ________ ________");

        assert_eq!(f.try_merge(&g), None);
        assert_eq!(g.try_merge(&f), None);
    }

    #[test]
    pub fn instruction_filter_next_matching_instruction_basic() {
        let f1 = InstructionFilter::parse("0100____ 00001111");
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x00, 0x00]))),
            Some(Instruction::new(&[0x40, 0x0f]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x49, 0x00]))),
            Some(Instruction::new(&[0x49, 0x0f]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x40, 0x10]))),
            Some(Instruction::new(&[0x41, 0x0f]))
        );
        assert_eq!(dbg!(f1.next_matching_instruction(&Instruction::new(&[0x50, 0x00]))), None);
    }

    #[test]
    pub fn instruction_filter_next_matching_instruction_length_difference() {
        let f1 = InstructionFilter::parse("0001___1 0110__00");
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x00]))),
            Some(Instruction::new(&[0x11, 0x60]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x00, 0x00, 0x00]))),
            Some(Instruction::new(&[0x11, 0x60]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x12, 0x55, 0x40, 0x20]))),
            Some(Instruction::new(&[0x13, 0x60]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x1f, 0x61]))),
            Some(Instruction::new(&[0x1f, 0x64]))
        );
        assert_eq!(dbg!(f1.next_matching_instruction(&Instruction::new(&[0x1f, 0x6d]))), None);
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x11, 0x6c, 0x00]))),
            Some(Instruction::new(&[0x13, 0x60]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x11, 0x68, 0x00]))),
            Some(Instruction::new(&[0x11, 0x6c]))
        );
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x11, 0x68]))),
            Some(Instruction::new(&[0x11, 0x68]))
        );
    }

    #[test]
    pub fn instruction_filter_next_matching_instruction3() {
        let f1 = InstructionFilter::parse("_0000100 11______");
        assert_eq!(
            dbg!(f1.next_matching_instruction(&Instruction::new(&[0x4c, 0x0f, 0xc7, 0x0c, 0xc5, 0x08, 0x1f, 0x69, 0x35]))),
            Some(Instruction::new(&[0x84, 0xc0]))
        );
    }

    #[test]
    pub fn instruction_filter_serialize() {
        let f = InstructionFilter::new(vec![ByteFilter::new(0xff, 0xab), ByteFilter::new(0xfe, 0xdc)]);
        assert_eq!(serde_json::to_string(&f).unwrap(), r#""abdc:fe""#);

        let f = InstructionFilter::new(vec![
            ByteFilter::new(0xff, 0xab),
            ByteFilter::new(0xfe, 0xdc),
            ByteFilter::new(0xdd, 0xdc),
        ]);
        assert_eq!(serde_json::to_string(&f).unwrap(), r#""abdc:fedc:dd""#);

        let f = InstructionFilter::new(vec![ByteFilter::new(0xff, 0xab), ByteFilter::new(0x00, 0x00)]);
        assert_eq!(serde_json::to_string(&f).unwrap(), r#""ab__""#);
    }

    #[test]
    pub fn instruction_filter_deserialize() {
        let f: InstructionFilter = serde_json::from_str(r#""abdc:fe""#).unwrap();
        assert_eq!(
            f,
            InstructionFilter::new(vec![ByteFilter::new(0xff, 0xab), ByteFilter::new(0xfe, 0xdc)])
        );

        let f: InstructionFilter = serde_json::from_str(r#""ab__""#).unwrap();
        assert_eq!(
            f,
            InstructionFilter::new(vec![ByteFilter::new(0xff, 0xab), ByteFilter::new(0x00, 0x00)])
        );

        let f: InstructionFilter = serde_json::from_str(r#""abdc:fedc:dd""#).unwrap();
        assert_eq!(
            f,
            InstructionFilter::new(vec![
                ByteFilter::new(0xff, 0xab),
                ByteFilter::new(0xfe, 0xdc),
                ByteFilter::new(0xdd, 0xdc),
            ])
        );
    }

    #[test]
    pub fn instruction_filter_overlaps() {
        let a = InstructionFilter::parse("00000000 000__000");
        let b = InstructionFilter::parse("00000000 000__0__");
        assert!(a.overlaps(&b));
        assert!(b.overlaps(&a));
    }

    #[test]
    pub fn instruction_filter_overlapping() {
        let a = InstructionFilter::parse("01001___ 00001001 00_1_00_");
        let b = InstructionFilter::parse("01001___ 00001001 00__00__");

        assert!(a.overlaps(&b));
    }
}
