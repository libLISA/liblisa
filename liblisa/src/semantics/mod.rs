//! Semantics are defined in terms of [`Computation`]s.
//! In order to support different kinds of definitions, [`Computation`] is a trait.
//! The default implementation used by `liblisa-synth` can be found [here](default).

use std::fmt::{Debug, Display};
use std::num::NonZeroU64;
use std::ops::{Deref, Index, IndexMut};

use serde::{Deserialize, Serialize};

use crate::utils::bitmask_u64;
use crate::value::{AsValue, OwnedValue, Value};

pub mod default;

/// A default set of argument names that can be passed to [`Computation::display`].
pub const ARG_NAMES: &[&str] = &[
    "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y",
    "Z",
];

/// Implements the semantics of a single dataflow.
pub trait Computation: Debug + Clone {
    /// Computes the output of the semantics, given `inputs`.
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue;

    /// Returns true if `expected` matches the output of the computation.
    /// This function can be more efficient than manually comparing the result of `self.evaluate(..)`.
    /// For example, we can avoid allocating a `Vec` for `OwnedValue::Bytes` results.
    fn compare_eq<V: AsValue>(&self, inputs: &[V], expected: Value) -> bool {
        self.evaluate(inputs) == expected
    }

    /// Returns a struct that is suitable for printing, which uses `input_names` in place of the inputs.
    fn display<'a, S: AsRef<str>>(&'a self, input_names: &'a [S]) -> impl Display + Debug + 'a;

    /// The indices of all inputs used in the computation.
    fn used_input_indices(&self) -> Vec<usize>;

    /// Remaps the input indices, such that `new_index = map[old_index].unwrap_or(old_index)`.
    fn remap_inputs(&mut self, map: &[Option<usize>]);

    /// Returns true when the computation is the identity function.
    /// This function may under-approximate: it does not necessarily have to return true in *all* cases.
    ///
    /// For example, this function might return true for `f(x) = x`, but return false for `f(x) = (x + 5) - 5`.
    fn is_identity(&self) -> bool;
}

impl Computation for () {
    fn evaluate<V: AsValue>(&self, _inputs: &[V]) -> OwnedValue {
        panic!("Void computation cannot run evaluate()")
    }

    fn display<'a, S: AsRef<str>>(&'a self, _input_names: &'a [S]) -> impl Display + Debug + 'a {
        DisplayVoidComputation
    }

    fn used_input_indices(&self) -> Vec<usize> {
        Vec::new()
    }

    fn remap_inputs(&mut self, _map: &[Option<usize>]) {}

    fn is_identity(&self) -> bool {
        false
    }
}

#[derive(Debug, Copy, Clone)]
struct DisplayVoidComputation;

impl Display for DisplayVoidComputation {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        panic!("This should never happen")
    }
}

/// An optimized representation of an output type.
/// In case of [`IoType::Integer`], this representation pre-computes the bitmask needed to perform equality comparisons.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum OutputType {
    /// An integer output. Usually [`Value::Num`] or [`OwnedValue::Num`].
    Number {
        /// A mask that can be applied to an `u64` to crop the `u64` to the correct value.
        mask: NonZeroU64,
    },

    /// A byte output. Usually [`Value::Bytes`] or [`OwnedValue::Bytes`].
    Bytes {
        /// The number of bytes in the output.
        num_bytes: usize,
    },
}

impl OutputType {
    /// Constructs the output type from an [`IoType`].
    pub const fn const_from(value: IoType) -> Self {
        match value {
            IoType::Integer {
                num_bits,
            } => OutputType::Number {
                mask: match NonZeroU64::new(bitmask_u64(num_bits as u32)) {
                    Some(x) => x,
                    _ => panic!("`value` must be at least 1 bit wide"),
                },
            },
            IoType::Bytes {
                num_bytes,
            } => OutputType::Bytes {
                num_bytes,
            },
        }
    }
}

impl From<IoType> for OutputType {
    fn from(value: IoType) -> Self {
        Self::const_from(value)
    }
}

/// The type of an input or output of a [`Computation`].
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum IoType {
    /// An integer output. Usually [`Value::Num`] or [`OwnedValue::Num`].
    Integer {
        /// The number of bits in the output.
        num_bits: usize,
    },

    /// A byte output. Usually [`Value::Bytes`] or [`OwnedValue::Bytes`].
    Bytes {
        /// The number of bytes in the output.
        num_bytes: usize,
    },
}

impl IoType {
    /// Returns the number of bits.
    /// For [`IoType::Integer`] this is simply the number of bits.
    /// For [`IoType::Bytes`] this is the number of bytes multiplied by 8.
    pub fn num_bits(&self) -> usize {
        match self {
            IoType::Integer {
                num_bits,
            } => *num_bits,
            IoType::Bytes {
                num_bytes,
            } => *num_bytes * 8,
        }
    }
}

/// A collection of input values for a [`Computation`].
///
/// In particular, this struct implements [`hashbrown::Equivalent`].
/// This means that [`InputValues`] can be used in a [`hashbrown::HashMap`]/[`hashbrown::HashSet`],
/// and existance checks can be performed using non-owned `&[Value]`.
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct InputValues(Vec<OwnedValue>);

impl std::fmt::Debug for InputValues {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl FromIterator<OwnedValue> for InputValues {
    fn from_iter<T: IntoIterator<Item = OwnedValue>>(iter: T) -> Self {
        InputValues(iter.into_iter().collect())
    }
}

impl<V: AsValue> From<&[V]> for InputValues {
    fn from(value: &[V]) -> Self {
        value.iter().map(|v| v.to_owned_value()).collect()
    }
}

impl InputValues {
    /// Iterates over all values in the collection.
    pub fn iter(&self) -> impl Iterator<Item = &OwnedValue> {
        self.0.iter()
    }
}

impl Deref for InputValues {
    type Target = [OwnedValue];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Index<usize> for InputValues {
    type Output = OwnedValue;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for InputValues {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl hashbrown::Equivalent<[Value<'_>]> for InputValues {
    fn equivalent(&self, key: &[Value<'_>]) -> bool {
        self.0.len() == key.len() && self.0.iter().zip(key.iter()).all(|(lhs, &rhs)| lhs.as_value() == rhs)
    }
}

impl hashbrown::Equivalent<InputValues> for [Value<'_>] {
    fn equivalent(&self, key: &InputValues) -> bool {
        key.equivalent(self)
    }
}

impl hashbrown::Equivalent<Vec<OwnedValue>> for InputValues {
    fn equivalent(&self, key: &Vec<OwnedValue>) -> bool {
        self.0 == *key
    }
}

impl hashbrown::Equivalent<InputValues> for Vec<OwnedValue> {
    fn equivalent(&self, key: &InputValues) -> bool {
        *self == key.0
    }
}

impl hashbrown::Equivalent<[OwnedValue]> for InputValues {
    fn equivalent(&self, key: &[OwnedValue]) -> bool {
        self.0 == key
    }
}

impl hashbrown::Equivalent<InputValues> for [OwnedValue] {
    fn equivalent(&self, key: &InputValues) -> bool {
        self == key.0
    }
}
