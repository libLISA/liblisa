//! A [`Value`] is an integer or byte sequence in a CPU state or dataflow.
//!
//! This module contains definitions for three versions of this struct:
//!
//! - [`OwnedValue`]
//! - [`Value`]
//! - [`MutValue`]
//!
//! Byte sequences in [`OwnedValue`] are backed by a `Vec<u8>`,
//! while they are backed by a `&[u8]` and `&mut [u8]` in [`Value`] and [`MutValue`], respectively.

use std::fmt::{Debug, UpperHex};
use std::hash::Hash;

use serde::{Deserialize, Serialize};

use crate::encoding::dataflows::Size;
use crate::utils::switch_endianness_u64;

/// A value that stores its byte data as a `Vec<u8>`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OwnedValue {
    /// An integer value.
    Num(u64),

    /// Byte data
    Bytes(Vec<u8>),
}

/// The hash of an OwnedValue is the same as the hash of a Value<'_>
impl Hash for OwnedValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_value().hash(state)
    }
}

impl hashbrown::Equivalent<Value<'_>> for OwnedValue {
    fn equivalent(&self, key: &Value<'_>) -> bool {
        self.as_value() == *key
    }
}

impl hashbrown::Equivalent<OwnedValue> for Value<'_> {
    fn equivalent(&self, key: &OwnedValue) -> bool {
        *self == key.as_value()
    }
}

/// Trait that is implemented by any type that can be converted into a [`Value`].
pub trait AsValue: Debug + Hash + PartialEq<OwnedValue> {
    /// Returns a reference to the value as a [`Value`].
    fn as_value(&self) -> Value<'_>;

    /// If the value is an integer, returns the integer.
    /// Otherwise, panics.
    #[inline]
    fn unwrap_num(&self) -> u64 {
        match self.as_value() {
            Value::Num(v) => v,
            _ => panic!("called as_integer_ref on Value::Bytes"),
        }
    }

    /// If the value is Byte data, returns a reference to the bytestring.
    /// Otherwise, panics.
    #[inline]
    fn unwrap_bytes(&self) -> &[u8] {
        match self.as_value() {
            Value::Bytes(b) => b,
            _ => panic!("called unwrap_bytes on Value::Integer"),
        }
    }

    /// If the value is an integer, returns true if and only if the integer is non-zero.
    /// Otherwise, panics.
    #[inline]
    fn interpret_as_bool(&self) -> bool {
        self.unwrap_num() != 0
    }

    /// Converts the value to an [`OwnedValue`].
    #[inline]
    fn to_owned_value(&self) -> OwnedValue {
        match self.as_value() {
            Value::Num(n) => OwnedValue::Num(n),
            Value::Bytes(b) => OwnedValue::Bytes(b.to_vec()),
        }
    }
}

impl AsValue for u64 {
    fn as_value(&self) -> Value<'_> {
        Value::Num(*self)
    }
}

impl PartialEq<OwnedValue> for u64 {
    fn eq(&self, other: &OwnedValue) -> bool {
        match other {
            OwnedValue::Num(a) => a == self,
            _ => false,
        }
    }
}

impl<'a> PartialEq<Value<'a>> for OwnedValue {
    fn eq(&self, other: &Value<'a>) -> bool {
        match (self, other) {
            (OwnedValue::Num(a), Value::Num(b)) => a == b,
            (OwnedValue::Bytes(a), Value::Bytes(b)) => a == b,
            _ => false,
        }
    }
}

impl PartialEq<OwnedValue> for Value<'_> {
    fn eq(&self, other: &OwnedValue) -> bool {
        other.eq(self)
    }
}

impl AsValue for OwnedValue {
    #[inline]
    fn as_value(&self) -> Value<'_> {
        match self {
            OwnedValue::Num(n) => Value::Num(*n),
            OwnedValue::Bytes(b) => Value::Bytes(b),
        }
    }
}

impl AsValue for Value<'_> {
    #[inline]
    fn as_value(&self) -> Value<'_> {
        *self
    }
}

/// Helper trait that provides `value_eq`, which compares equality of collections whose elements implement [`AsValue`].
pub trait ValueArrayEquality {
    /// Returns true if the array of values is equal to `other`.
    fn value_eq<V: AsValue>(&self, other: &[V]) -> bool;
}

impl<V: AsValue> ValueArrayEquality for &[V] {
    fn value_eq<W: AsValue>(&self, other: &[W]) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.as_value() == b.as_value())
    }
}

impl<V: AsValue> ValueArrayEquality for &Vec<V> {
    fn value_eq<W: AsValue>(&self, other: &[W]) -> bool {
        (self as &[V]).value_eq(other)
    }
}

impl<V: AsValue> ValueArrayEquality for Vec<V> {
    fn value_eq<W: AsValue>(&self, other: &[W]) -> bool {
        (self as &[V]).value_eq(other)
    }
}

/// A value that stores mutable references to the underlying data.
#[derive(PartialEq, Eq, Debug)]
pub enum MutValue<'a> {
    /// An integer value.
    Num(&'a mut u64),

    /// Byte data value.
    Bytes(&'a mut [u8]),
}

impl MutValue<'_> {
    /// Treats the value as a little-endian number, and fills it from `value`.
    pub fn fill_le_from_value(&mut self, num_bytes_in_value: usize, value: &Value<'_>) {
        match self {
            MutValue::Num(n) => {
                **n = match value {
                    Value::Num(n) => switch_endianness_u64(*n, num_bytes_in_value * 8),
                    Value::Bytes(b) => {
                        let mut n = 0;
                        for (index, b) in b.iter().enumerate().take(8) {
                            n |= (*b as u64) << (index * 8);
                        }

                        n
                    },
                }
            },
            MutValue::Bytes(b) => match value {
                Value::Num(n) => {
                    for (x, y) in b.iter_mut().zip(n.to_le_bytes()) {
                        *x = y;
                    }
                },
                Value::Bytes(b2) => {
                    for (x, y) in b.iter_mut().zip(b2.iter().rev()) {
                        *x = *y;
                    }
                },
            },
        }
    }

    /// Treats the value as a big-endian number, and fills it from `value`.
    pub fn fill_be_from_value(&mut self, value: &Value<'_>) {
        match self {
            MutValue::Num(n) => {
                **n = match value {
                    Value::Num(n) => *n,
                    Value::Bytes(b) => {
                        let mut n = 0;
                        for (index, b) in b.iter().rev().enumerate().take(8) {
                            n |= (*b as u64) << (index * 8);
                        }

                        n
                    },
                }
            },
            MutValue::Bytes(b) => match value {
                Value::Num(n) => {
                    for (x, y) in b.iter_mut().zip(n.to_be_bytes()) {
                        *x = y;
                    }
                },
                Value::Bytes(b2) => {
                    for (x, y) in b.iter_mut().zip(b2.iter()) {
                        *x = *y;
                    }
                },
            },
        }
    }

    /// Copies the value from `val`.
    pub fn copy_from(&mut self, val: &impl AsValue) {
        match (self, val.as_value()) {
            (Self::Num(d), Value::Num(s)) => **d = s,
            (Self::Bytes(d), Value::Bytes(s)) => {
                d.copy_from_slice(s);
            },
            _ => panic!("MutValue::copy_from cannot copy bytes-to-num or num-to-bytes"),
        }
    }
}

/// The type of a value. Can be a number (`ValueType::Num`) or a byte sequence (`ValueType::Bytes(num_bytes)`)
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ValueType {
    /// An integer value.
    Num,

    /// Byte data of the specific number of bytes.
    Bytes(usize),
}

/// A values that stores its byte data as a `&[u8]`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Value<'a> {
    /// An integer value.
    Num(u64),

    /// Byte data
    Bytes(&'a [u8]),
}

impl Debug for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.to_le_bytes().iter().rev() {
            write!(f, "{b:02X}")?;
        }

        Ok(())
    }
}

impl UpperHex for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.to_le_bytes().iter().rev() {
            write!(f, "{b:02X}")?;
        }

        Ok(())
    }
}

impl Value<'_> {
    /// Converts the value to little-endian bytes.
    #[inline]
    pub fn to_le_bytes(&self) -> Vec<u8> {
        match self {
            Value::Num(n) => n.to_le_bytes().to_vec(),
            Value::Bytes(v) => v.to_vec(),
        }
    }

    /// Returns the byte at position `index` in the value.
    /// For integers, returns `(val >> (index * 8)) as u8`
    #[inline]
    pub fn select_byte(&self, index: usize) -> u8 {
        match self {
            Value::Num(n) => (n >> (index * 8)) as u8,
            Value::Bytes(v) => v[index],
        }
    }

    /// Slices the value to include only the area in `size`.
    pub fn slice(&self, size: Size) -> Self {
        let w = (size.end_byte - size.start_byte + 1) * 8;
        match self {
            Value::Num(n) => {
                Value::Num((n >> (size.start_byte * 8)) & if w == 64 { 0xffff_ffff_ffff_ffff } else { (1 << w) - 1 })
            },
            Value::Bytes(b) => {
                // TODO: imm analysis used to slice out-of-bounds, but this seems to be fixed now. If you encounter this error, a quick fix can be to comment out the panic. Imm analysis will work regardless (Because `Value::Bytes` of different lengths are considered not equal).
                if b.len() <= size.end_byte {
                    panic!("Slicing {size:?} is out of bounds in {self:X?}");
                }

                let start = size.start_byte.min(b.len() - 1);
                let end = (size.end_byte + 1).min(b.len());

                Value::Bytes(&b[start..end])
            },
        }
    }

    /// Computes the XOR of this value and `b`.
    /// The result is provided to `f`.
    pub fn xor<T>(&self, b: &Value, mut f: impl FnMut(&Value) -> T) -> T {
        match (self, b) {
            (Value::Num(a), Value::Num(b)) => f(&Value::Num(a ^ b)),
            (Value::Bytes(a), Value::Bytes(b)) => f(&Value::Bytes(
                &a.iter()
                    .copied()
                    .zip(b.iter().copied())
                    .map(|(a, b)| a ^ b)
                    .collect::<Vec<_>>(),
            )),
            _ => panic!("Comparing mixed values"),
        }
    }

    /// Computes the OR of this value and `b`.
    /// The result is provided to `f`.
    pub fn or<T>(&self, b: &Value, mut f: impl FnMut(&Value) -> T) -> T {
        match (self, b) {
            (Value::Num(a), Value::Num(b)) => f(&Value::Num(a | b)),
            (Value::Bytes(a), Value::Bytes(b)) => f(&Value::Bytes(
                &a.iter()
                    .copied()
                    .zip(b.iter().copied())
                    .map(|(a, b)| a | b)
                    .collect::<Vec<_>>(),
            )),
            _ => panic!("Comparing mixed values"),
        }
    }

    /// Computes the AND of this value and `b`.
    /// The result is provided to `f`.
    pub fn and<T>(&self, b: &Value, mut f: impl FnMut(&Value) -> T) -> T {
        match (self, b) {
            (Value::Num(a), Value::Num(b)) => f(&Value::Num(a & b)),
            (Value::Bytes(a), Value::Bytes(b)) => f(&Value::Bytes(
                &a.iter()
                    .copied()
                    .zip(b.iter().copied())
                    .map(|(a, b)| a & b)
                    .collect::<Vec<_>>(),
            )),
            _ => panic!("Comparing mixed values"),
        }
    }
}

impl<'a> From<Value<'a>> for OwnedValue {
    fn from(value: Value<'a>) -> Self {
        value.to_owned_value()
    }
}
