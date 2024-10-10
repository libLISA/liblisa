// TODO: Update this documentation
//! [`InstructionFilter`]s are used to reason over instruction space.
//! An encoding can return a set of filters representing the instruction space it covers.
//!
//! The various types in this module can be used to manipulate and query sets of [`InstructionFilter`]s.

use std::cmp::Ordering;
use std::fmt::{Debug, LowerHex, UpperHex};
use std::hash::Hash;
use std::str::FromStr;

use arrayvec::ArrayVec;
use hex::FromHexError;
use itertools::Itertools;
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

mod counter;
mod extended;
mod filter;
mod filter_mcs;
mod map;
mod set;
mod tree;

pub use counter::InstructionCounter;
pub use filter::{merge_filters, ByteFilter, FilterBit, InstructionFilter, WithFilters};
pub(crate) use filter_mcs::MinimumCoveringFilterSet;
pub use map::FilterMap;
pub use set::FilterList;
pub use tree::FilterTree;

/// An instruction bitstring.
/// Can contain instructions up to 15 bytes long.
#[derive(Copy, Clone)]
pub struct Instruction {
    data: [u8; 15],
    len: u8,
}

impl<'a> arbitrary::Arbitrary<'a> for Instruction {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let num = u.arbitrary::<u8>()? % 15 + 1;
        let mut data = ArrayVec::<_, 15>::new();
        for _ in 0..num {
            data.push(u.arbitrary()?);
        }

        Ok(Instruction::new(&data))
    }
}

#[cfg(feature = "schemars")]
impl schemars::JsonSchema for Instruction {
    fn schema_name() -> String {
        "Instruction".to_owned()
    }

    fn schema_id() -> std::borrow::Cow<'static, str> {
        std::borrow::Cow::Borrowed(concat!(module_path!(), "::Instruction"))
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        let schema: schemars::schema::SchemaObject = <String>::json_schema(gen).into();
        schema.into()
    }
}

impl From<&str> for Instruction {
    fn from(s: &str) -> Self {
        Self::from_str(s).unwrap()
    }
}

impl<'a> From<&'a [u8]> for Instruction {
    fn from(data: &'a [u8]) -> Self {
        Self::new(data)
    }
}

impl Serialize for Instruction {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = self.into_string();
        serializer.serialize_str(&s)
    }
}

impl FromStr for Instruction {
    type Err = FromHexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.chars().filter(|c| !c.is_whitespace() && *c != ',').collect::<String>();
        let mut data = [0u8; 15];
        let len = s.len() / 2;
        hex::decode_to_slice(s, &mut data[..len])?;

        Ok(Instruction {
            data,
            len: len as u8,
        })
    }
}

impl<'de> Deserialize<'de> for Instruction {
    fn deserialize<D>(deserializer: D) -> Result<Instruction, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct InstructionVisitor;

        impl Visitor<'_> for InstructionVisitor {
            type Value = Instruction;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("an instruction string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Instruction::from(value))
            }
        }

        deserializer.deserialize_str(InstructionVisitor)
    }
}

impl Instruction {
    /// Creates a new instruction from the provided slice.
    /// The slice must be 15 bytes or less.
    pub const fn new(data: &[u8]) -> Instruction {
        assert!(data.len() <= 15);
        let len = data.len() as u8;
        let mut slice = [0u8; 15];
        let mut index = 0;
        loop {
            if index >= data.len() {
                break;
            }

            slice[index] = data[index];
            index += 1;
        }

        Instruction {
            data: slice,
            len,
        }
    }

    /// Converts the instruction into an uppercase hexadecimal string.
    pub fn into_string(&self) -> String {
        hex::encode_upper(self.bytes())
    }

    /// Returns true if the instruction starts with the prefix `p`, followed by zero or more additional bytes.
    pub fn starts_with(&self, p: &Instruction) -> bool {
        p.byte_len() <= self.byte_len() && self.resize(p.byte_len(), 0x00) == *p
    }

    /// Sets the bit at position `index`, counting from the right.
    ///
    /// `bit` must be `0` or `1`.
    pub fn set_nth_bit_from_right(&mut self, index: usize, bit: u8) {
        assert!(bit == 0 || bit == 1);
        let i = self.len as usize - 1 - index / 8;
        self.data[i] = (self.data[i] & !(1 << (index % 8))) | bit << (index % 8);
    }

    /// Sets multiple bits starting at position `index`, counting from the right and moving to the left.
    /// Shifts new bits to insert out of `data`.
    /// The lowest bit in `data` is inserted first.
    pub fn set_multiple_bits_from_right(&mut self, index: usize, mut data: u64, mut num: usize) {
        assert!(num % 8 == 0 && index % 8 == 0);

        let mut i = self.len as usize - 1 - index / 8;
        for _ in 0..num / 8 {
            self.data[i] = data as u8;
            i = i.wrapping_sub(1);
            data >>= 8;
            num = num.wrapping_sub(8);
        }
    }
}

impl FromIterator<u8> for Instruction {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        let mut slice = [0u8; 15];
        let mut len = 0;
        for byte in iter {
            slice[len] = byte;
            len += 1;
        }

        Instruction {
            data: slice,
            len: len as u8,
        }
    }
}

impl PartialEq for Instruction {
    fn eq(&self, other: &Self) -> bool {
        self.bytes() == other.bytes()
    }
}

impl Hash for Instruction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.bytes().hash(state);
    }
}

impl Eq for Instruction {}

impl PartialOrd for Instruction {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Instruction {
    fn cmp(&self, other: &Self) -> Ordering {
        for (a, b) in self.bytes().iter().zip(other.bytes().iter()) {
            match a.cmp(b) {
                Ordering::Equal => {},
                other => return other,
            }
        }

        self.bytes().len().cmp(&other.bytes().len())
    }
}

impl Instruction {
    /// Returns a slice containing the bytes of the instruction.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        &self.data[0..self.len as usize]
    }

    /// Returns the number of bytes in the instruction.
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.bytes().len()
    }

    /// Returns the number of bits in the instruction.
    #[inline]
    pub fn bit_len(&self) -> usize {
        self.byte_len() * 8
    }

    /// Returns an instruction where the bit at position `index`, counting from the right, is flipped.
    pub fn with_nth_bit_from_right_flipped(&self, index: usize) -> Instruction {
        let mut instr = Instruction::new(self.bytes());
        instr.data[instr.len as usize - 1 - index / 8] ^= 1 << (index % 8);

        instr
    }

    /// Replaces the bit at position `index`, counting from the right, with `bit`.
    /// `bit` must be `0` or `1`.
    pub fn with_nth_bit_from_right(&self, index: usize, bit: u8) -> Instruction {
        assert!(bit == 0 || bit == 1);
        let mut instr = Instruction::new(self.bytes());
        let i = instr.len as usize - 1 - index / 8;
        instr.data[i] = (instr.data[i] & !(1 << (index % 8))) | bit << (index % 8);

        instr
    }

    /// Replaces the bit at position `index`, counting from the left, with `bit`.
    /// `bit` must be `0` or `1`.
    pub fn with_nth_bit_from_left(&self, index: usize, bit: u8) -> Instruction {
        assert!(bit == 0 || bit == 1);
        let mut instr = Instruction::new(self.bytes());
        let i = index / 8;
        let offset = 7 - (index % 8);
        instr.data[i] = (instr.data[i] & !(1 << offset)) | bit << offset;

        instr
    }

    /// Extends the instruction with one extra 0-byte.
    /// The instruction must be 15 bytes or less.
    pub fn extend(&self) -> Instruction {
        self.resize(self.byte_len() + 1, 0)
    }

    /// Resizes the instruction to be `num_bytes` long.
    /// If this is longer than the current instruction, new bytes are filled with the value `fill`.
    pub fn resize(&self, num_bytes: usize, fill: u8) -> Instruction {
        assert!(num_bytes < 15);
        let mut instr = *self;
        instr.len = num_bytes as u8;
        for b in instr.data.iter_mut().take(num_bytes).skip(self.byte_len()) {
            *b = fill;
        }

        instr
    }

    /// Replaces the `num` rightmost bits in the instruction with value `bit`.
    pub fn with_rightmost_bits(&self, num: usize, bit: u8) -> Instruction {
        assert!(bit == 0 || bit == 1);
        let mut instr = *self;
        for i in 0..num {
            instr = instr.with_nth_bit_from_right(i, bit);
        }

        instr
    }

    /// Returns the value of the bit at position `index`, counting from the right.
    #[inline]
    pub fn nth_bit_from_right(&self, index: usize) -> u8 {
        (self.bytes()[self.byte_len() - 1 - index / 8] >> (index % 8)) & 1
    }

    /// Returns the value of the bit at position `index`, counting from the left.
    #[inline]
    pub fn nth_bit_from_left(&self, index: usize) -> u8 {
        (self.bytes()[index / 8] >> (7 - (index % 8))) & 1
    }
}

impl Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]:", self.bytes().iter().map(|b| format!("{b:02x}")).join(""))?;

        for b in self.data[0..self.len as usize].iter() {
            write!(f, " {b:08b}")?;
        }

        Ok(())
    }
}

impl LowerHex for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.bytes().iter().map(|b| format!("{b:02x}")).join(""))
    }
}

impl UpperHex for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.bytes().iter().map(|b| format!("{b:02X}")).join(""))
    }
}

#[cfg(test)]
mod tests {
    use crate::instr::Instruction;

    #[test]
    pub fn test_instr_ordering() {
        assert!(Instruction::new(&[0x47, 0xF0]) < Instruction::new(&[0x48, 0x89, 0xBB, 0x00, 0x00, 0x00, 0x00]));
        assert!(Instruction::new(&[0x48]) < Instruction::new(&[0x48, 0x89, 0xBB, 0x00, 0x00, 0x00, 0x00]));
    }

    #[test]
    pub fn test_instruction_ordering() {
        assert!(Instruction::new(&[0x47, 0xF0]) < Instruction::new(&[0x48, 0x89, 0xBB, 0x00, 0x00, 0x00, 0x00]));
        assert!(Instruction::new(&[0x48]) < Instruction::new(&[0x48, 0x89, 0xBB, 0x00, 0x00, 0x00, 0x00]));
    }

    #[test]
    pub fn test_nth_bit_from_right() {
        for n in 0..16 {
            assert_eq!(
                Instruction::new(&[0x47, 0xF0]).nth_bit_from_right(n),
                (0x47f0 >> n) as u8 & 1,
                "Bit {n} does not match"
            );
        }
    }

    #[test]
    pub fn with_rightmost_bits() {
        assert_eq!(
            Instruction::new(&[0x47, 0xF0]).with_rightmost_bits(5, 0),
            Instruction::new(&[0x47, 0xe0])
        );
        assert_eq!(
            Instruction::new(&[0x47, 0xF0]).with_rightmost_bits(10, 0),
            Instruction::new(&[0x44, 0x00])
        );

        assert_eq!(
            Instruction::new(&[0x47, 0xF0]).with_rightmost_bits(5, 1),
            Instruction::new(&[0x47, 0xff])
        );
        assert_eq!(
            Instruction::new(&[0x46, 0x80]).with_rightmost_bits(10, 1),
            Instruction::new(&[0x47, 0xff])
        );
    }

    #[test]
    pub fn test_serialize_instr() {
        println!("{}", serde_json::to_string(&Instruction::new(&[0xff, 0x13, 0x22])).unwrap());

        assert_eq!(
            serde_json::to_string(&Instruction::new(&[0xff, 0x13, 0x22])).unwrap(),
            r#""FF1322""#
        );

        assert_eq!(
            serde_json::to_string(&Instruction::new(&[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC])).unwrap(),
            r#""123456789ABC""#
        );
    }

    #[test]
    pub fn test_deserialize_instr_hex() {
        assert_eq!(
            serde_json::from_str::<Instruction>(r#""1F""#).unwrap(),
            Instruction::new(&[0x1F]),
        );

        assert_eq!(
            serde_json::from_str::<Instruction>(r#""FF1322""#).unwrap(),
            Instruction::new(&[0xff, 0x13, 0x22]),
        );

        assert_eq!(
            serde_json::from_str::<Instruction>(r#""FA1322""#).unwrap(),
            Instruction::new(&[0xfa, 0x13, 0x22]),
        );
    }
}
