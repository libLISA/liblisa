//! Various kinds of computations.

use std::fmt::{Debug, Display};
use std::iter::once;
use std::num::NonZeroU64;

use arrayvec::ArrayVec;
use log::trace;
use serde::{Deserialize, Serialize};

use super::{Expr, Expression, FALSE, TRUE};
use crate::semantics::default::ops::Op;
use crate::semantics::{Computation, IoType, OutputType};
use crate::utils::cmov::CmovAnd;
use crate::utils::{create_from_le_bytes, sign_extend, sign_extend_u64, switch_endianness_u128, switch_endianness_u64};
use crate::value::{AsValue, OwnedValue, Value};

/// A computation using an [`Expr`].
/// The result of the [`Expr`] is interpreted using an output encoding.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ExprComputation<'a> {
    expr: Expr<'a>,
    output_encoding: OutputEncoding,
    output_type: OutputType,
}

impl Default for ExprComputation<'_> {
    fn default() -> Self {
        Self::const_default()
    }
}

impl Default for &ExprComputation<'_> {
    fn default() -> Self {
        ExprComputation::const_default_ref()
    }
}

impl ExprComputation<'_> {
    /// Returns a default identity function expression
    pub const fn const_default() -> Self {
        Self {
            expr: Expr::new(&[Op::Hole(0)]),
            output_encoding: OutputEncoding::UnsignedBigEndian,
            output_type: OutputType::Number {
                mask: match NonZeroU64::new(u64::MAX) {
                    Some(x) => x,
                    _ => unreachable!(),
                },
            },
        }
    }

    /// Returns a reference to the expression returned by [`Self::const_default`].
    pub const fn const_default_ref() -> &'static Self {
        const DEFAULT_TEMPLATE: ExprComputation<'static> = ExprComputation::const_default();
        &DEFAULT_TEMPLATE
    }
}

/// A prepared comparison to an output value.
/// Comparison is quicker, because we can directly compare against an `i128` instead of having to decode a [`Value`].
#[derive(Clone, Debug, PartialEq)]
pub struct PreparedComparison {
    /// The expected little-endian value.
    pub little_endian: i128,

    /// The expected big-endian value.
    pub big_endian: i128,
}

impl PreparedComparison {
    /// Creates a new prepared comparison from a [`Value`].
    pub fn from(value: &Value) -> Self {
        match value {
            Value::Num(n) => PreparedComparison {
                little_endian: *n as i128,
                big_endian: *n as i128,
            },
            Value::Bytes(bytes) => {
                let v = create_from_le_bytes(bytes, |n| n as u128, |n| n);
                PreparedComparison {
                    little_endian: v as i128,
                    big_endian: switch_endianness_u128(v, bytes.len() * 8) as i128,
                }
            },
        }
    }
}

/// Result of a [`PreparedComparison`] comparison.
pub struct CompareResult {
    /// True if the output was equal if encoded as little-endian.
    pub little_endian: bool,

    /// True if the output was equal if encoded as big-endian.
    pub big_endian: bool,
}

impl PreparedComparison {
    /// Performs the comparison given a specific output encoding.
    pub fn compare(&self, output_type: OutputType, output_encoding: OutputEncoding, result: i128) -> bool {
        match output_type {
            OutputType::Number {
                mask,
            } => result as u64 & mask.get() == self.big_endian as u64 & mask.get(),
            OutputType::Bytes {
                num_bytes,
            } => {
                let mask = !(-1i128 << (8 * num_bytes));
                match output_encoding {
                    OutputEncoding::UnsignedLittleEndian => result & mask == self.little_endian & mask,
                    OutputEncoding::UnsignedBigEndian => result & mask == self.big_endian & mask,
                }
            },
        }
    }

    /// Performs the comparison for both output encodings.
    /// Is more efficient than invoking [`Self::compare`] twice.
    pub fn compare_dual(&self, output_type: OutputType, result: i128) -> CompareResult {
        match output_type {
            OutputType::Number {
                mask,
            } => {
                let v = result as u64 & mask.get() == self.big_endian as u64 & mask.get();
                CompareResult {
                    little_endian: v,
                    big_endian: v,
                }
            },
            OutputType::Bytes {
                num_bytes,
            } => {
                let mask = if num_bytes == 16 {
                    -1i128
                } else {
                    !(-1i128 << (8 * num_bytes))
                };

                CompareResult {
                    little_endian: result & mask == self.little_endian & mask,
                    big_endian: result & mask == self.big_endian & mask,
                }
            },
        }
    }
}

impl<'a> ExprComputation<'a> {
    /// Creates a new computation using the provided [`Expr`] and output encoding.
    pub const fn new(expr: Expr<'a>, output_encoding: OutputEncoding, output_type: IoType) -> ExprComputation<'a> {
        ExprComputation {
            expr,
            output_encoding,
            output_type: OutputType::const_from(output_type),
        }
    }

    /// Returns the underlying [`Expr`] of this computation.
    pub fn expr(&self) -> Expr<'a> {
        self.expr
    }

    fn i128_to_output(&self, result: i128) -> OwnedValue {
        match self.output_type {
            OutputType::Number {
                mask,
            } => OwnedValue::Num(result as u64 & mask.get()),
            OutputType::Bytes {
                num_bytes,
            } => self.i128_as_bytes(num_bytes, result),
        }
    }

    fn i128_as_bytes(&self, num_bytes: usize, result: i128) -> OwnedValue {
        let mut bytes = vec![0u8; num_bytes];
        let mut v = result;
        match self.output_encoding {
            OutputEncoding::UnsignedLittleEndian => {
                for b in bytes.iter_mut() {
                    *b = v as u8;
                    v >>= 8;
                }
            },
            OutputEncoding::UnsignedBigEndian => {
                for b in bytes.iter_mut().rev() {
                    *b = v as u8;
                    v >>= 8;
                }
            },
        }

        OwnedValue::Bytes(bytes)
    }

    fn i128_compare_eq(&self, expected: Value, result: i128) -> bool {
        match self.output_type {
            OutputType::Number {
                mask,
            } => expected == Value::Num(result as u64 & mask.get()),
            OutputType::Bytes {
                num_bytes,
            } => {
                let expected_bytes = expected.unwrap_bytes();
                if expected_bytes.len() != num_bytes {
                    return false
                }

                let mut v = result;
                match self.output_encoding {
                    OutputEncoding::UnsignedLittleEndian => {
                        for b in expected_bytes.iter() {
                            if *b != v as u8 {
                                return false;
                            }

                            v >>= 8;
                        }
                    },
                    OutputEncoding::UnsignedBigEndian => {
                        for b in expected_bytes.iter().rev() {
                            if *b != v as u8 {
                                return false;
                            }

                            v >>= 8;
                        }
                    },
                }

                true
            },
        }
    }

    /// Evaluates the computation with the provided (already interpreted) arguments, and returns an [`OwnedValue`].
    pub fn evaluate_with_args(&self, args: &[i128]) -> OwnedValue {
        let result = self.expr.evaluate(args);
        self.i128_to_output(result)
    }

    /// Evaluates the computation with the provided (already interpreted) arguments, and returns an [`OwnedValue`].
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    pub fn evaluate_with_args_indirect(&self, all_args: &[i128], mapping: &[u16]) -> OwnedValue {
        match self.output_type {
            OutputType::Number {
                mask,
            } => {
                let result = self.expr.evaluate_indirect_as_u64(all_args, mapping);
                OwnedValue::Num(result & mask.get())
            },
            OutputType::Bytes {
                num_bytes,
            } => {
                let result = self.expr.evaluate_indirect(all_args, mapping);
                self.i128_as_bytes(num_bytes, result)
            },
        }
    }

    /// Evaluates the computation with the provided (already interpreted) arguments, and interprets the result as a boolean.
    /// A zero-result is interpreted as false, while all non-zero results are interpreted as true.
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    pub fn evaluate_as_bool_with_args_indirect(&self, all_args: &[i128], mapping: &[u16]) -> bool {
        let result = self.expr.evaluate_indirect_as_u64(all_args, mapping);
        match self.output_type {
            OutputType::Number {
                mask,
            } => result & mask.get() != 0,
            _ => panic!("Cannot evaluate bytes as boolean"),
        }
    }

    /// Evaluates the computation with the provided (already interpreted) arguments, and compares the result with `expected`.
    ///
    /// Returns true if the result is equal to `expected`, false otherwise.
    pub fn compare_eq_with_args(&self, args: &[i128], expected: Value) -> bool {
        let result = self.expr.evaluate(args);
        self.i128_compare_eq(expected, result)
    }

    /// Evaluates the computation with the provided (already interpreted) arguments, and compares the result with `expected`.
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    ///
    /// Returns true if the result is equal to `expected`, false otherwise.
    pub fn compare_eq_with_args_indirect(&self, all_args: &[i128], mapping: &[u16], expected: Value) -> bool {
        let result = self.expr.evaluate_indirect(all_args, mapping);
        self.i128_compare_eq(expected, result)
    }

    /// Evaluates the computation with the provided (already interpreted) arguments, and compares the result with `expected`.
    /// Uses a [`PreparedComparison`] for better performance.
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    ///
    /// Returns true if the result is equal to `expected`, false otherwise.
    pub fn prepared_compare_eq_with_args_indirect(
        &self, all_args: &[i128], mapping: &[u16], expected: &PreparedComparison,
    ) -> bool {
        let result = self.expr.evaluate_indirect(all_args, mapping);
        match self.output_type {
            OutputType::Number {
                mask,
            } => result as u64 & mask.get() == expected.big_endian as u64 & mask.get(),
            OutputType::Bytes {
                num_bytes,
            } => {
                let mask = !(-1i128 << (8 * num_bytes));
                match self.output_encoding {
                    OutputEncoding::UnsignedLittleEndian => result & mask == expected.little_endian & mask,
                    OutputEncoding::UnsignedBigEndian => result & mask == expected.big_endian & mask,
                }
            },
        }
    }

    /// Returns the output encoding to which the `i128` result of the computation is converted.
    pub fn output_encoding(&self) -> OutputEncoding {
        self.output_encoding
    }

    /// Returns the optimized internal output type of the computation.
    pub fn internal_output_type(&self) -> OutputType {
        self.output_type
    }

    /// Returns the output type of the computation.
    pub fn output_type(&self) -> IoType {
        match self.output_type {
            OutputType::Number {
                mask,
            } => IoType::Integer {
                num_bits: mask.get().trailing_ones() as usize,
            },
            OutputType::Bytes {
                num_bytes,
            } => IoType::Bytes {
                num_bytes,
            },
        }
    }
}

/// The encoding of an input argument passed to an expression.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ArgEncoding {
    /// Signed value with the least-significant byte first.
    /// If the input is an integer value, the bytes in the integer are reversed.
    SignedLittleEndian = 0,

    /// Signed value with the most-significant byte first.
    /// If the input is an integer value, the bytes in the integer are *not* reversed.
    SignedBigEndian = 1,

    /// Unsigned value with the least-significant byte first.
    /// If the input is an integer value, the bytes in the integer are reversed.
    UnsignedLittleEndian = 2,

    /// Unsigned value with the most-significant byte first.
    /// If the input is an integer value, the bytes in the integer are *not* reversed.
    UnsignedBigEndian = 3,
}

impl ArgEncoding {
    /// Returns true if the encoding is [`ArgEncoding::SignedLittleEndian`] or [`ArgEncoding::SignedBigEndian`]
    pub fn is_signed(self) -> bool {
        (self as u8) < 2
    }

    /// Returns true if the encoding is [`ArgEncoding::SignedLittleEndian`] or [`ArgEncoding::UnsignedLittleEndian`]
    pub fn is_le(self) -> bool {
        (self as u8) & 1 == 0
    }
}

/// The output encoding of an expression.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum OutputEncoding {
    /// Value with the least-significant byte first.
    /// If the output is an integer value, the bytes in the integer are reversed.
    UnsignedLittleEndian,

    /// Value with the most-significant byte first.
    /// If the output is an integer value, the bytes in the integer are *not* reversed.
    UnsignedBigEndian,
}

/// An argrument for an expression.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Arg {
    /// One of the inputs encoded accoding to `encoding`.
    Input {
        /// The index of the input in the array of inputs passed to any of the `evaluate*` functions on a [`Computation`].
        index: u8,

        /// The number of bits in the input.
        num_bits: u8,

        /// The encoding of the input.
        /// The input is first cropped to the number of bits specified, then sign extension or byte-swapping occurs according to this encoding.
        encoding: ArgEncoding,
    },

    /// A tiny constant value (contained within the `Arg`)
    ///
    /// The `i16` is cast to an `i128`.
    TinyConst(i16),

    /// A constant in the constant list of an expression.
    ///
    /// The `u16` is used as an index into the list of constants.
    Const(u16),
}

impl Arg {
    fn interpret_be_u64(n: u64, num_bits: u8, encoding: ArgEncoding) -> i128 {
        let n_le = switch_endianness_u64(n, num_bits as usize);

        // The compiler refuses to automatically generate a cmov here, even though it is faster.
        let mut n = n;
        n.cmov_if_and_imm_zero::<1>(&n_le, encoding as u8);

        match encoding {
            ArgEncoding::SignedBigEndian | ArgEncoding::SignedLittleEndian => sign_extend_u64(n, num_bits as usize) as i128,
            ArgEncoding::UnsignedBigEndian | ArgEncoding::UnsignedLittleEndian => n as i128,
        }
    }

    fn interpret_le_u64(n: u64, num_bits: u8, encoding: ArgEncoding) -> i128 {
        let n_be = switch_endianness_u64(n, num_bits as usize);

        // The compiler refuses to automatically generate a cmov here, even though it is faster.
        let mut n = n;
        n.cmov_if_and_imm_nonzero::<1>(&n_be, encoding as u8);

        match encoding {
            ArgEncoding::SignedBigEndian | ArgEncoding::SignedLittleEndian => sign_extend_u64(n, num_bits as usize) as i128,
            ArgEncoding::UnsignedBigEndian | ArgEncoding::UnsignedLittleEndian => n as i128,
        }
    }

    fn interpret_u128(encoding: &ArgEncoding, n: u128, num_bits: &u8) -> i128 {
        let n = match encoding {
            ArgEncoding::SignedLittleEndian | ArgEncoding::UnsignedLittleEndian => n,
            ArgEncoding::SignedBigEndian | ArgEncoding::UnsignedBigEndian => switch_endianness_u128(n, *num_bits as usize),
        };

        match encoding {
            ArgEncoding::SignedLittleEndian | ArgEncoding::SignedBigEndian => sign_extend(n as i128, *num_bits as usize),
            ArgEncoding::UnsignedLittleEndian | ArgEncoding::UnsignedBigEndian => n as i128,
        }
    }

    /// Interprets argument given the `inputs` and `consts`.
    pub fn interpret_inputs<V: AsValue>(&self, inputs: &[V], consts: &[i128]) -> i128 {
        trace!("Interpreting {self:?} in inputs={inputs:?}, consts={consts:X?}");
        match self {
            Arg::Input {
                index,
                num_bits,
                encoding,
            } => match inputs[*index as usize].as_value() {
                Value::Num(n) => Self::interpret_be_u64(n, *num_bits, *encoding),
                Value::Bytes(b) => create_from_le_bytes(
                    b,
                    |n| Self::interpret_le_u64(n, *num_bits, *encoding),
                    |n| Self::interpret_u128(encoding, n, num_bits),
                ),
            },
            Arg::TinyConst(v) => *v as i128,
            Arg::Const(index) => consts[*index as usize],
        }
    }
}

/// A computation using an [`Expression`].
/// The arguments for the [`Expression`] are pre-processed, and he result of the [`Expression`] is interpreted using an output encoding.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct ExpressionComputation {
    expr: Expression,
    arg_interpretation: ArrayVec<Arg, 8>,
    output_encoding: OutputEncoding,
    output_type: IoType,
}

impl AsComputationRef for ComputationRef<'_, '_> {
    fn as_internal(&self) -> ComputationRef<'_, '_> {
        ComputationRef {
            template: self.template,
            consts: &[],
            arg_interpretation: self.arg_interpretation,
        }
    }
}

impl AsComputationRef for ExpressionComputation {
    fn as_internal(&self) -> ComputationRef<'_, '_> {
        ComputationRef {
            template: ExprComputation::new(self.expr.as_expr(), self.output_encoding, self.output_type),
            consts: &[],
            arg_interpretation: &self.arg_interpretation,
        }
    }
}

impl ExpressionComputation {
    /// Creates a new [`ExpressionComputation`].
    pub fn new(
        expr: Expression, arg_interpretation: ArrayVec<Arg, 8>, output_encoding: OutputEncoding, output_type: IoType,
    ) -> Self {
        Self {
            expr,
            arg_interpretation,
            output_encoding,
            output_type,
        }
    }

    /// Replaces the output encoding with `output_encoding`.
    pub fn set_output_encoding(&mut self, output_encoding: OutputEncoding) {
        self.output_encoding = output_encoding;
    }

    /// Creates an [`ExpressionComputation`] that always returns `0i128`.
    pub fn always_false(output_type: IoType) -> Self {
        Self::new(
            FALSE.to_owned(),
            ArrayVec::new(),
            OutputEncoding::UnsignedBigEndian,
            output_type,
        )
    }
}

/// Provides generic methods that work on references to computations.
pub trait AsComputationRef {
    /// Return a [`ComputationRef`].
    fn as_internal(&self) -> ComputationRef<'_, '_>;

    /// Return an owned [`SynthesizedComputation`].
    fn to_synthesized_computation(&self) -> SynthesizedComputation {
        let i = self.as_internal();
        SynthesizedComputation {
            expr: self.expr().to_owned(),
            consts: i.consts.to_vec(),
            arg_interpretation: i.arg_interpretation.to_vec(),
            output_type: i.output_type(),
            output_encoding: i.output_encoding(),
        }
    }

    /// Return a reference to the expression used in the template.
    fn expr(&self) -> Expr {
        self.as_internal().template.expr
    }

    /// Returns the argument interpretations of the computation.
    fn arg_interpretation(&self) -> &[Arg] {
        self.as_internal().arg_interpretation
    }

    /// Returns a new expression that returns `if_zero` if the current expression is equal to `0`, and returns `if_nonzero` otherwise.
    fn if_zero<A: AsComputationRef, B: AsComputationRef>(&self, if_zero: &A, if_nonzero: &B) -> SynthesizedComputation {
        let if_zero = if_zero.as_internal();
        let if_nonzero = if_nonzero.as_internal();

        assert_eq!(if_zero.output_type(), if_nonzero.output_type());

        let need_bit_swap_nonzero = (if_zero.output_type().num_bits() > 8 || if_nonzero.output_type().num_bits() > 8)
            && if_zero.output_encoding() != if_nonzero.output_encoding();

        let arg_interpretation = if_nonzero
            .arg_interpretation
            .iter()
            .cloned()
            .chain(if_zero.arg_interpretation.iter().cloned().map(|arg| match arg {
                Arg::Const(index) => Arg::Const(index + if_nonzero.consts.len() as u16),
                _ => arg,
            }))
            .chain(self.as_internal().arg_interpretation.iter().cloned().map(|arg| match arg {
                Arg::Const(index) => Arg::Const(index + if_nonzero.consts.len() as u16 + if_zero.consts.len() as u16),
                _ => arg,
            }))
            .collect::<Vec<_>>();

        let consts = if_nonzero
            .consts
            .iter()
            .copied()
            .chain(if_zero.consts.iter().copied())
            .chain(self.as_internal().consts.iter().copied())
            .collect();

        let offset_a = if_nonzero.arg_interpretation.len();
        let offset_b = if_nonzero.arg_interpretation.len() + if_zero.arg_interpretation.len();
        let ops =
            // condition
            self.expr().ops().iter().map(|op| match op {
                Op::Hole(n) => Op::Hole(n.checked_add(offset_b as u16).unwrap()),
                other => *other,
            })
            .chain(once(Op::Crop { num_bits: self.as_internal().output_type().num_bits() as u8 }))
            // zero
            .chain(if_zero.template.expr.ops().iter().map(|op| match op {
                Op::Hole(n) => Op::Hole(n.checked_add(offset_a as u16).unwrap()),
                other => *other,
            }))
            .chain(once(Op::Crop { num_bits: if_zero.output_type().num_bits() as u8 }))
            // nonzero
            .chain(if_nonzero.template.expr.ops().iter().copied())
            .chain(once(Op::Crop { num_bits: if_nonzero.output_type().num_bits() as u8 }))
            .chain(once(Op::SwapBytes { num_bits: if_nonzero.output_type().num_bits() as u8 }).filter(|_| need_bit_swap_nonzero))
            .chain(once(Op::IfZero))
            .collect::<Vec<_>>();

        // TODO: If we're outputting bytes, we need to apply endianness

        SynthesizedComputation {
            expr: Expression::new(ops),
            consts,
            arg_interpretation,
            output_encoding: if_zero.output_encoding(),
            output_type: if_zero.output_type(),
        }
    }

    /// Concatenates the operations of the two computations.
    /// In and of itself, this produces a computation that ends with two values on the evaluation stack.
    /// The last value is normally popped and returned, which would be the result of `other`.
    ///
    /// This method is only useful if you want to then perform an operation that uses the results of both computations.
    /// For example, chaining the results of two computations and then adding the [`Op::Add`] operation to compute the sum of both computations.
    fn chain(&self, other: &impl AsComputationRef) -> SynthesizedComputation
    where
        Self: Debug,
    {
        let other = other.as_internal();

        assert_eq!(self.as_internal().output_type(), other.output_type());
        if self.as_internal().output_type().num_bits() > 8 || other.output_type().num_bits() > 8 {
            assert_eq!(
                self.as_internal().output_encoding(),
                other.output_encoding(),
                "In {self:?} vs {other:?}"
            );
        }

        let consts = self
            .as_internal()
            .consts
            .iter()
            .copied()
            .chain(other.consts.iter().copied())
            .collect();
        let mut arg_interpretation = other
            .arg_interpretation
            .iter()
            .cloned()
            .map(|arg| match arg {
                Arg::Const(index) => Arg::Const(index + self.as_internal().consts.len() as u16),
                _ => arg,
            })
            .collect::<Vec<_>>();

        let ops = other
            .template
            .expr
            .ops()
            .iter()
            .copied()
            .chain(self.expr().ops().iter().map(|op| match op {
                Op::Hole(n) => Op::Hole({
                    let new_arg = self.as_internal().arg_interpretation[*n as usize];
                    arg_interpretation
                        .iter()
                        .position(|a| a == &new_arg)
                        .map(|index| u16::try_from(index).expect("should always succeed because it's an index we used before"))
                        .unwrap_or_else(|| {
                            let index = arg_interpretation.len();
                            arg_interpretation.push(new_arg);

                            u16::try_from(index).expect("templates should not have more than 256 different arguments")
                        })
                }),
                other => *other,
            }))
            .collect::<Vec<_>>();

        SynthesizedComputation {
            expr: Expression::new(ops),
            consts,
            arg_interpretation,
            output_encoding: self.as_internal().output_encoding(),
            output_type: self.as_internal().output_type(),
        }
    }

    /// Returns a computation that computes the bitwise AND of both computations.
    fn and(&self, other: &SynthesizedComputation) -> SynthesizedComputation
    where
        Self: Debug,
    {
        let mut result = self.chain(other);
        result.expr.push_op(Op::And);
        result
    }

    /// Returns a computation that computes the bitwise OR of both computations.
    fn or(&self, other: &SynthesizedComputation) -> SynthesizedComputation
    where
        Self: Debug,
    {
        let mut result = self.chain(other);
        result.expr.push_op(Op::Or);
        result
    }

    /// Returns a computation that computes the bitwise NOT of the computation.
    fn not(&self) -> SynthesizedComputation {
        let ops = self.expr().ops().iter().copied().chain(once(Op::Not)).collect::<Vec<_>>();

        SynthesizedComputation {
            expr: Expression::new(ops),
            arg_interpretation: self.as_internal().arg_interpretation.to_vec(),
            consts: self.as_internal().consts.to_vec(),
            output_encoding: self.as_internal().output_encoding(),
            output_type: self.as_internal().output_type(),
        }
    }

    /// Returns a computation that computes the bitwise NOT of the computation, and then crops the result to 1 bit.
    fn not_crop(&self) -> SynthesizedComputation {
        let ops = self
            .expr()
            .ops()
            .iter()
            .copied()
            .chain(once(Op::Not))
            .chain(once(Op::Crop {
                num_bits: 1,
            }))
            .collect::<Vec<_>>();

        SynthesizedComputation {
            expr: Expression::new(ops),
            arg_interpretation: self.as_internal().arg_interpretation.to_vec(),
            consts: self.as_internal().consts.to_vec(),
            output_encoding: self.as_internal().output_encoding(),
            output_type: self.as_internal().output_type(),
        }
    }

    /// Returns the constants used in this computation.
    fn consts(&self) -> &[i128] {
        self.as_internal().consts
    }
}

/// A synthesized computation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct SynthesizedComputation {
    expr: Expression,
    arg_interpretation: Vec<Arg>,
    consts: Vec<i128>,
    output_encoding: OutputEncoding,
    output_type: IoType,
}

impl AsComputationRef for SynthesizedComputation {
    fn as_internal(&self) -> ComputationRef<'_, '_> {
        ComputationRef {
            template: ExprComputation::new(self.expr.as_expr(), self.output_encoding, self.output_type),
            consts: &self.consts,
            arg_interpretation: &self.arg_interpretation,
        }
    }
}

impl SynthesizedComputation {
    /// Creates a new [`SynthesizedComputation`].
    pub fn new(
        expr: Expression, arg_interpretation: Vec<Arg>, consts: Vec<i128>, output_encoding: OutputEncoding, output_type: IoType,
    ) -> Self {
        Self {
            expr,
            consts,
            arg_interpretation,
            output_encoding,
            output_type,
        }
    }

    /// Returns a computation that always returns `0`.
    pub fn always_false() -> Self {
        Self::new(
            FALSE.to_owned(),
            Vec::new(),
            Vec::new(),
            OutputEncoding::UnsignedBigEndian,
            IoType::Integer {
                num_bits: 1,
            },
        )
    }

    /// Returns a computation that always returns `1`.
    pub fn always_true() -> Self {
        Self::new(
            TRUE.to_owned(),
            Vec::new(),
            Vec::new(),
            OutputEncoding::UnsignedBigEndian,
            IoType::Integer {
                num_bits: 1,
            },
        )
    }

    /// Returns the output type of the computation.
    pub fn output_type(&self) -> IoType {
        self.output_type
    }

    /// Returns the output encoding of the computation.
    pub fn output_encoding(&self) -> OutputEncoding {
        self.output_encoding
    }

    /// Replaces the output encoding of the computation with `output_encoding`.
    pub fn set_output_encoding(&mut self, output_encoding: OutputEncoding) {
        self.output_encoding = output_encoding;
    }
}

impl Computation for ExpressionComputation {
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue {
        self.as_internal().evaluate(inputs)
    }

    fn display<'a, S: AsRef<str>>(&'a self, input_names: &'a [S]) -> impl Display + Debug + 'a {
        self.expr.as_expr().display(
            self.arg_interpretation
                .iter()
                .map(|item| match item {
                    Arg::Input {
                        index,
                        encoding,
                        ..
                    } => {
                        let convert = match encoding {
                            ArgEncoding::SignedLittleEndian => "sle",
                            ArgEncoding::SignedBigEndian => "sbe",
                            ArgEncoding::UnsignedLittleEndian => "ule",
                            ArgEncoding::UnsignedBigEndian => "ube",
                        };
                        format!(
                            "{}({})",
                            convert,
                            input_names.get(*index as usize).map(|x| x.as_ref()).unwrap_or("<ERROR>")
                        )
                    },
                    Arg::TinyConst(v) => format!("0x{v:X}"),
                    Arg::Const(_) => unreachable!(),
                })
                .collect::<Vec<_>>(),
        )
    }

    fn compare_eq<V: AsValue>(&self, inputs: &[V], expected: Value) -> bool {
        self.as_internal().compare_eq(inputs, expected)
    }

    fn used_input_indices(&self) -> Vec<usize> {
        self.as_internal().used_input_indices()
    }

    fn remap_inputs(&mut self, map: &[Option<usize>]) {
        for arg in self.arg_interpretation.iter_mut() {
            if let Arg::Input {
                index, ..
            } = arg
            {
                *index = map[*index as usize]
                    .expect("Cannot remove input that is in use")
                    .try_into()
                    .unwrap()
            }
        }
    }

    fn is_identity(&self) -> bool {
        self.as_internal().is_identity()
    }
}

impl Computation for SynthesizedComputation {
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue {
        self.as_internal().evaluate(inputs)
    }

    fn compare_eq<V: AsValue>(&self, inputs: &[V], expected: Value) -> bool {
        self.as_internal().compare_eq(inputs, expected)
    }

    fn display<'a, S: AsRef<str>>(&'a self, input_names: &'a [S]) -> impl Display + Debug + 'a {
        self.expr.as_expr().display(
            self.arg_interpretation
                .iter()
                .map(|item| match item {
                    Arg::Input {
                        index,
                        encoding,
                        ..
                    } => {
                        let convert = match encoding {
                            ArgEncoding::SignedLittleEndian => "sle",
                            ArgEncoding::SignedBigEndian => "sbe",
                            ArgEncoding::UnsignedLittleEndian => "ule",
                            ArgEncoding::UnsignedBigEndian => "ube",
                        };
                        format!(
                            "{}({})",
                            convert,
                            input_names.get(*index as usize).map(|x| x.as_ref()).unwrap_or("<ERROR>")
                        )
                    },
                    Arg::TinyConst(v) => format!("0x{v:X}"),
                    Arg::Const(index) => format!("0x{:X}", self.consts[*index as usize]),
                })
                .collect::<Vec<_>>(),
        )
    }

    fn used_input_indices(&self) -> Vec<usize> {
        self.as_internal().used_input_indices()
    }

    fn remap_inputs(&mut self, map: &[Option<usize>]) {
        for arg in self.arg_interpretation.iter_mut() {
            if let Arg::Input {
                index, ..
            } = arg
            {
                *index = map[*index as usize]
                    .expect("Cannot remove input that is in use")
                    .try_into()
                    .unwrap()
            }
        }
    }

    fn is_identity(&self) -> bool {
        self.as_internal().is_identity()
    }
}

/// The computation type shared between [`SynthesizedComputation`], [`ExprComputation`] and [`ExpressionComputation`].
#[derive(Clone, Debug, PartialEq)]
pub struct ComputationRef<'template, 'a> {
    /// The expression used.
    pub template: ExprComputation<'template>,

    /// The argument interpretation.
    pub arg_interpretation: &'a [Arg],

    /// The constants used in the arguments.
    pub consts: &'a [i128],
}

impl<'template, 'a> ComputationRef<'template, 'a> {
    /// Creates a new computation reference that does not use any constants.
    pub fn new(template: ExprComputation<'template>, arg_interpretation: &'a [Arg]) -> Self {
        Self {
            template,
            consts: &[],
            arg_interpretation,
        }
    }

    /// Returns the output encoding of the computation.
    pub fn output_encoding(&self) -> OutputEncoding {
        self.template.output_encoding
    }

    /// Returns the output type of the computation.
    pub fn output_type(&self) -> IoType {
        self.template.output_type()
    }

    /// Creates an owned [`ExpressionComputation`] from the computation.
    pub fn to_expression_computation(&self) -> ExpressionComputation {
        assert!(self.consts.is_empty());
        ExpressionComputation {
            expr: self.template.expr.to_owned(),
            arg_interpretation: self.arg_interpretation.iter().copied().collect(),
            output_encoding: self.output_encoding(),
            output_type: self.output_type(),
        }
    }

    /// Returns the expression of this computation.
    pub fn expr_computation(&self) -> &ExprComputation<'template> {
        &self.template
    }
}

impl Computation for ComputationRef<'_, '_> {
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue {
        if self.arg_interpretation.len() <= 128 {
            let args = self
                .arg_interpretation
                .iter()
                .map(|arg| arg.interpret_inputs(inputs, self.consts))
                .collect::<ArrayVec<_, 128>>();

            self.expr_computation()
                .evaluate_with_args(&args[..self.arg_interpretation.len()])
        } else {
            let args = self
                .arg_interpretation
                .iter()
                .map(|arg| arg.interpret_inputs(inputs, self.consts))
                .collect::<Vec<_>>();

            self.expr_computation().evaluate_with_args(&args)
        }
    }

    fn compare_eq<V: AsValue>(&self, inputs: &[V], expected: Value) -> bool {
        if self.arg_interpretation.len() <= 128 {
            let args = self
                .arg_interpretation
                .iter()
                .map(|arg| arg.interpret_inputs(inputs, self.consts))
                .collect::<ArrayVec<_, 128>>();

            self.expr_computation().compare_eq_with_args(&args, expected)
        } else {
            let args = self
                .arg_interpretation
                .iter()
                .map(|arg| arg.interpret_inputs(inputs, self.consts))
                .collect::<Vec<_>>();

            self.expr_computation().compare_eq_with_args(&args, expected)
        }
    }

    fn display<'a, S: AsRef<str>>(&'a self, input_names: &'a [S]) -> impl Display + Debug + 'a {
        self.template.expr.display(
            self.arg_interpretation
                .iter()
                .map(|item| match item {
                    Arg::Input {
                        index,
                        encoding,
                        ..
                    } => {
                        let convert = match encoding {
                            ArgEncoding::SignedLittleEndian => "sle",
                            ArgEncoding::SignedBigEndian => "sbe",
                            ArgEncoding::UnsignedLittleEndian => "ule",
                            ArgEncoding::UnsignedBigEndian => "ube",
                        };
                        format!("{}({})", convert, input_names[*index as usize].as_ref())
                    },
                    Arg::TinyConst(v) => format!("0x{v:X}"),
                    Arg::Const(index) => format!("0x{:X}", self.consts[*index as usize]),
                })
                .collect::<Vec<_>>(),
        )
    }

    fn used_input_indices(&self) -> Vec<usize> {
        self.arg_interpretation
            .iter()
            .flat_map(|arg| match arg {
                Arg::Input {
                    index, ..
                } => Some(*index as usize),
                _ => None,
            })
            .collect()
    }

    fn remap_inputs(&mut self, _map: &[Option<usize>]) {
        panic!("Impossible to remap inputs of immutable InternalComputation")
    }

    fn is_identity(&self) -> bool {
        if self.arg_interpretation.len() == 1 {
            match self.arg_interpretation[0] {
                Arg::Input {
                    index,
                    num_bits,
                    encoding,
                } => {
                    index == 0
                        && num_bits as usize >= self.output_type().num_bits()
                        && matches!(
                            (encoding, self.output_encoding()),
                            (
                                ArgEncoding::SignedLittleEndian | ArgEncoding::UnsignedLittleEndian,
                                OutputEncoding::UnsignedLittleEndian
                            ) | (
                                ArgEncoding::SignedBigEndian | ArgEncoding::UnsignedBigEndian,
                                OutputEncoding::UnsignedBigEndian
                            )
                        )
                        && self.template.expr.ops() == [Op::Hole(0)]
                },
                _ => false,
            }
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::random::randomized_value;

    #[test]
    pub fn expression_computation_if_zero() {
        const T: Expr<'static> = Expr::new(&[Op::Hole(0)]);

        let v0 = ComputationRef {
            template: ExprComputation::new(
                T,
                OutputEncoding::UnsignedBigEndian,
                IoType::Integer {
                    num_bits: 64,
                },
            ),
            arg_interpretation: &[Arg::TinyConst(0)],
            consts: &[],
        }
        .to_expression_computation();

        let v3 = ComputationRef {
            template: ExprComputation::new(
                T,
                OutputEncoding::UnsignedBigEndian,
                IoType::Integer {
                    num_bits: 64,
                },
            ),
            arg_interpretation: &[Arg::TinyConst(3)],
            consts: &[],
        }
        .to_expression_computation();

        let v5 = ComputationRef {
            template: ExprComputation::new(
                T,
                OutputEncoding::UnsignedBigEndian,
                IoType::Integer {
                    num_bits: 64,
                },
            ),
            arg_interpretation: &[Arg::TinyConst(5)],
            consts: &[],
        }
        .to_expression_computation();

        assert_eq!(v0.if_zero(&v3, &v5).evaluate::<OwnedValue>(&[]), OwnedValue::Num(3));
        assert_eq!(v3.if_zero(&v3, &v5).evaluate::<OwnedValue>(&[]), OwnedValue::Num(5));
    }

    #[test]
    pub fn test_be_to_le() {
        let result = switch_endianness_u64(0x12345678, 32);
        println!("Result = {result:X}");
        assert_eq!(result, 0x78563412);
    }

    #[test]
    pub fn expr_bit_set() {
        // expr!(or(hole::<0>(), shl(hole::<2>(), hole::<1>().crop::<3>())));
        const T: Expr<'static> = Expr::new(&[
            Op::Hole(0),
            Op::Hole(2),
            Op::Hole(1),
            Op::Crop {
                num_bits: 3,
            },
            Op::Shl,
            Op::Or,
        ]);

        let instance = ComputationRef {
            template: ExprComputation::new(
                T,
                OutputEncoding::UnsignedBigEndian,
                IoType::Integer {
                    num_bits: 64,
                },
            ),
            arg_interpretation: &[
                Arg::Input {
                    index: 0,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(1),
            ],
            consts: &[],
        };

        assert_eq!(
            instance.evaluate(&[OwnedValue::Num(0x123450), OwnedValue::Num(3)]),
            OwnedValue::Num(0x123458)
        );
        assert_eq!(
            instance.evaluate(&[OwnedValue::Num(0xFFFD5744FE9EAB63), OwnedValue::Num(0x3FFE16F32426)]),
            OwnedValue::Num(0xFFFD5744FE9EAB63)
        );
    }

    #[test]
    pub fn shr_minus_one() {
        let mut rng = rand::thread_rng();
        // expr!(shr(hole::<0>(), sub(hole::<1>().crop::<6>(), one())))
        const T: Expr<'static> = Expr::new(&[
            Op::Hole(0),
            Op::Hole(1),
            Op::Crop {
                num_bits: 6,
            },
            Op::Const(1),
            Op::Sub,
            Op::Shr,
        ]);

        for _ in 0..100_000 {
            let a = randomized_value(&mut rng);
            let b = randomized_value(&mut rng) & 0xff;

            if b & 0b11_1111 != 0 {
                let expected = a.wrapping_shr(b as u32 - 1) & 1;
                let result = T.evaluate(&[a as i128, b as i128]) & 1;
                assert_eq!(
                    result, expected as i128,
                    "For carry of shift ({a:X?} >> {b:X?}) we expected {expected:X?} but found {result:X?}"
                );
            }
        }
    }

    #[test]
    pub fn sbb_cf() {
        // expr!(select::<64, 1, _>(add(hole::<0>().crop::<64>(), sub(c::<0>(), add(hole::<1>(), hole::<2>())).crop::<64>())))
        const T: Expr<'static> = Expr::new(&[
            Op::Hole(0),
            Op::Crop {
                num_bits: 64,
            },
            Op::Const(0),
            Op::Hole(1),
            Op::Hole(2),
            Op::Add,
            Op::Sub,
            Op::Crop {
                num_bits: 64,
            },
            Op::Add,
            Op::Select {
                num_skip: 64,
                num_take: 1,
            },
        ]);

        assert_eq!(T.evaluate(&[0xFFFFFFFFFACF7FFF, 0x1440000000000000, 1]), 1);
        assert_eq!(T.evaluate(&[0x1F99A, 0xFFFFFFFF4F6FFFFF, 1]), 0);
        assert_eq!(T.evaluate(&[0x53, 0xA, 1]), 1);
        assert_eq!(T.evaluate(&[0xFFFFFFFAC1358B66, 0x74921638C3E, 1]), 1);
        assert_eq!(T.evaluate(&[0xFFFFFFFFFFCEB79E, 0x1EAFC000, 0]), 1);
        assert_eq!(T.evaluate(&[0x1C0000000, 0x1C01F9DB0B0, 0]), 0);
        assert_eq!(T.evaluate(&[0xEFD89100000, 0xE59228A600, 0]), 1);
        assert_eq!(T.evaluate(&[0x15, 0x222D9E700000000, 1]), 0);
        assert_eq!(T.evaluate(&[0xFFE3FFFFFFFFFFFF, 0x0, 0]), 0);
    }

    #[test]
    pub fn arg_interpretation_ints() {
        use OwnedValue::*;

        // num_bits = 64
        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x1122334455667788)], &[]), 0x1122334455667788);
        assert_eq!(a.interpret_inputs(&[Num(0xfffffffffffffffe)], &[]), -2);

        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::UnsignedBigEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x1122334455667788)], &[]), 0x1122334455667788);
        assert_eq!(a.interpret_inputs(&[Num(0xfffffffffffffffe)], &[]), 0xfffffffffffffffe);

        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedLittleEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x1122334455667718)], &[]), 0x1877665544332211);
        assert_eq!(
            a.interpret_inputs(&[Num(0xfffffffffffffffe)], &[]),
            0xfeffffffffffffffu64 as i64 as i128
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::UnsignedLittleEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x1122334455667788)], &[]), 0x8877665544332211);
        assert_eq!(a.interpret_inputs(&[Num(0xfffffffffffffffe)], &[]), 0xfeffffffffffffff);

        // num_bits = 56
        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::SignedBigEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x11223344556677)], &[]), 0x11223344556677);
        assert_eq!(a.interpret_inputs(&[Num(0xfffffffffffffe)], &[]), -2);

        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::UnsignedBigEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x11223344556677)], &[]), 0x11223344556677);
        assert_eq!(a.interpret_inputs(&[Num(0xfffffffffffffe)], &[]), 0xfffffffffffffe);

        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::SignedLittleEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x11223344556677)], &[]), 0x77665544332211);
        assert_eq!(
            a.interpret_inputs(&[Num(0xfffffffffffffe)], &[]),
            0xfffeffffffffffffu64 as i64 as i128
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::UnsignedLittleEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x11223344556677)], &[]), 0x77665544332211);
        assert_eq!(a.interpret_inputs(&[Num(0xfffffffffffffe)], &[]), 0xfeffffffffffff);

        // num_bits = 10
        let a = Arg::Input {
            index: 0,
            num_bits: 10,
            encoding: ArgEncoding::SignedBigEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x123)], &[]), 0x123);
        assert_eq!(a.interpret_inputs(&[Num(0x3fe)], &[]), -2);

        let a = Arg::Input {
            index: 0,
            num_bits: 10,
            encoding: ArgEncoding::UnsignedBigEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x123)], &[]), 0x123);
        assert_eq!(a.interpret_inputs(&[Num(0x3fe)], &[]), 0x3fe);

        // We shouldn't rely on this behavior, because it makes no sense.
        // But here's a test anyway, just to make sure we don't change the behavior without noticing.
        let a = Arg::Input {
            index: 0,
            num_bits: 10,
            encoding: ArgEncoding::SignedLittleEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x121)], &[]), 0x101);
        assert_eq!(a.interpret_inputs(&[Num(0x3fe)], &[]), 0xfffffffffffffe03u64 as i64 as i128);

        let a = Arg::Input {
            index: 0,
            num_bits: 10,
            encoding: ArgEncoding::UnsignedLittleEndian,
        };
        assert_eq!(a.interpret_inputs(&[Num(0x123)], &[]), 0x2301);
        assert_eq!(a.interpret_inputs(&[Num(0x3fe)], &[]), 0xfe03);
    }

    #[test]
    pub fn arg_interpretation_bytes() {
        use OwnedValue::*;

        // num_bits = 64
        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])], &[]),
            0x1122334455667788
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            -2
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::UnsignedBigEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])], &[]),
            0x1122334455667788
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            0xfffffffffffffffe
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedLittleEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x18])], &[]),
            0x1877665544332211
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            0xfeffffffffffffffu64 as i64 as i128
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::UnsignedLittleEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])], &[]),
            0x8877665544332211
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            0xfeffffffffffffff
        );

        // num_bits = 56
        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::SignedBigEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77])], &[]),
            0x11223344556677
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            -2
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::UnsignedBigEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77])], &[]),
            0x11223344556677
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            0xfffffffffffffe
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::SignedLittleEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77])], &[]),
            0x77665544332211
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            0xfffeffffffffffffu64 as i64 as i128
        );

        let a = Arg::Input {
            index: 0,
            num_bits: 56,
            encoding: ArgEncoding::UnsignedLittleEndian,
        };
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77])], &[]),
            0x77665544332211
        );
        assert_eq!(
            a.interpret_inputs(&[Bytes(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe])], &[]),
            0xfeffffffffffff
        );
    }
}
