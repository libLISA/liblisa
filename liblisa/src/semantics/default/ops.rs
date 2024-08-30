//! Defines all operations supported by computations, as well as functions to execute the operations.

use std::fmt::Display;

use arrayvec::ArrayVec;
use serde::{Deserialize, Serialize};

use crate::utils::{deposit_bits_u128, sign_extend};

/// Operations in an expression.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Op {
    /// Looks up the value passed as the Nth input, and returns it.
    Hole(u16),

    /// Converts the i8 to i128 and returns it.
    Const(i8),

    /// Negates all 128 bits.
    Not,

    /// Clears bits num_bits..128
    Crop {
        /// The number of bits to keep.
        num_bits: u8,
    },

    /// Fills bits num_bits..128 to 0 with the value in bit num_bits
    SignExtend {
        /// The number of bits to which the number will be cropped before sign-extending it.
        num_bits: u8,
    },

    /// Fills bits [0..num_take] with the bits in [num_skip..num_skip + num_take], clears the bits [num_take..128]
    Select {
        /// The number of bits to skip.
        num_skip: u8,

        /// The number of bits to copy to the result, after skipping the first `num_skip` bits.
        num_take: u8,
    },

    /// Computes NOT(XOR(bit0, bit1, bit2, bit3, bit4, bit5, bit6, bit7))
    Parity,

    /// If the argument is zero, returns 1i128. Otherwise, returns 0i128.
    IsZero,

    /// Fills bits [0..8] with bits [7, 15, 23, .., 127], clears bits [8..128].
    ByteMask,

    /// Sets bits [0..N], clears bits [N..128]. If N >= 128, sets all bits.
    BitMask,

    /// Counts the number of bits that are 0, starting from the least significant bit.
    TrailingZeros,

    /// Counts the number of bits that are 0, starting from the most significant bit.
    LeadingZeros,

    /// Counts the number of ones in the value
    PopCount,

    /// Clears bits [num_bits..128]. Then reverses the order of the lower `(num_bits + 7) / 8` bytes.
    SwapBytes {
        /// The number of bits to keep.
        num_bits: u8,
    },

    /// Computes the sum of the two arguments.
    Add,

    /// Subtracts the second argument from the first.
    Sub,

    /// Multiplies the two arguments.
    Mul,

    /// Performs carry-less multiplication
    CarrylessMul,

    /// Performs a signed 128-bit division.
    Div,

    /// Performs an unsigned 128-bit division.
    UnsignedDiv,

    /// Performs a signed 128-bit division, and returns the remainder.
    Rem,

    /// Performs an unsigned 128-bit division, and returns the remainder.
    UnsignedRem,

    /// Shifts all the bits in the first argument left by the amount specified in the second argument.
    /// The shift amount in the second argument is masked with 0x7f.
    Shl,

    /// Shifts all the bits in the first argument right by the amount specified in the second argument.
    /// The topmost bit is copied from the previous topmost bit. So `-1i128 >> x` always returns `-1i128`.
    /// The shift amount in the second argument is masked with 0x7f.
    Shr,

    /// Computes the bitwise AND of the two arguments.
    And,

    /// Computes the bitwise OR of the two arguments.
    Or,

    /// Computes the bitwise XOR of the two arguments.
    Xor,

    /// Performs a signed comparison on the two arguments.
    /// Returns 1i128 if the first argument is less than the second argument.
    /// Otherwise, returns 0i128.
    CmpLt,

    /// Clears bits [num_bits..128].
    /// Rotates the lowest `num_bits` bits in the first argument to the left, by the amount specified in the second argument.
    /// The rotation amount in the second argument is first masked with 0xFFFFFFFF.
    /// Then the first argument is rotated by `x % num_bits`.
    Rol {
        /// The number of bits to which the value will be cropped before rotating it.
        num_bits: u8,
    },

    /// Performs bit deposition with source bits from the first argument, and selector bits from the second argument.
    /// Nth bit in the source bit is copied to the result at the position of the Nth set bit in the selector.
    ///
    /// Example: Source bits `0b00001011` and selector bits: `0b11001001`, yields: 0b10001001.
    DepositBits,

    /// Performs bit extraction with source bits from the first argument, and selector bits from the second argument.
    /// The Nth bit in the result is copied from the source bits at the position of the Nth set bit in the selector.
    ///
    /// Example: Source bits `0b00001011` and selector bits: `0b11001001`, yields: 0b0011.
    ExtractBits,

    /// If the first argument is 0, the second argument is returned.
    /// Otherwise, the third argument is returned.
    IfZero,
}

#[doc(hidden)] // public for macro
pub trait FastOpImpl: Copy {
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128;

    fn reconstruct() -> Self;
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct Val(pub i128);

impl FastOpImpl for Val {
    #[inline(always)]
    fn compute(&self, _: &impl Fn(usize) -> i128) -> i128 {
        self.0
    }

    fn reconstruct() -> Self {
        panic!("reconstruct not supported for Val")
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct HoleOp<const INDEX: u16>;

impl<const INDEX: u16> FastOpImpl for HoleOp<INDEX> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        args(INDEX as usize)
    }

    fn reconstruct() -> Self {
        Self
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct ConstOp<const CONST: i8>;

impl<const CONST: i8> FastOpImpl for ConstOp<CONST> {
    #[inline(always)]
    fn compute(&self, _: &impl Fn(usize) -> i128) -> i128 {
        CONST as i128
    }

    fn reconstruct() -> Self {
        Self
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct NotOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for NotOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        !self.0.compute(args)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct CropOp<const NUM_BITS: u8, V: FastOpImpl>(pub V);

impl<const NUM_BITS: u8, V: FastOpImpl> FastOpImpl for CropOp<NUM_BITS, V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args) & ((1i128 << NUM_BITS) - 1)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct SignExtendOp<const NUM_BITS: u8, V: FastOpImpl>(pub V);

impl<const NUM_BITS: u8, V: FastOpImpl> FastOpImpl for SignExtendOp<NUM_BITS, V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        sign_extend(self.0.compute(args) & ((1 << NUM_BITS) - 1), NUM_BITS as usize)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct SelectOp<const NUM_SKIP: u8, const NUM_TAKE: u8, V: FastOpImpl>(pub V);

impl<const NUM_SKIP: u8, const NUM_TAKE: u8, V: FastOpImpl> FastOpImpl for SelectOp<NUM_SKIP, NUM_TAKE, V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        (self.0.compute(args) >> NUM_SKIP) & ((1i128 << NUM_TAKE) - 1)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct ParityOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for ParityOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        (((self.0.compute(args) as u8).count_ones() + 1) % 2) as i128
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct IsZeroOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for IsZeroOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        i128::from(self.0.compute(args) == 0)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct ByteMaskOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for ByteMaskOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let v = self.0.compute(args);
        (0..16).fold(0, |acc, index| acc | (((v >> (index * 8 + 7)) & 1) << index))
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct BitMaskOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for BitMaskOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let v = self.0.compute(args);
        if v >= 128 {
            -1i128
        } else {
            1i128.wrapping_shl(v as u32).wrapping_sub(1)
        }
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct TrailingZerosOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for TrailingZerosOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args).trailing_zeros() as i128
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct LeadingZerosOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for LeadingZerosOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args).leading_zeros() as i128
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct PopCountOp<V: FastOpImpl>(pub V);

impl<V: FastOpImpl> FastOpImpl for PopCountOp<V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args).count_ones() as i128
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct SwapBytesOp<const NUM_BITS: u8, V: FastOpImpl>(pub V);

impl<const NUM_BITS: u8, V: FastOpImpl> FastOpImpl for SwapBytesOp<NUM_BITS, V> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let num_bits = NUM_BITS;
        self.compute_internal(args, num_bits)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct())
    }
}

impl<const NUM_BITS: u8, V: FastOpImpl> SwapBytesOp<NUM_BITS, V> {
    fn compute_internal(&self, args: &impl Fn(usize) -> i128, num_bits: u8) -> i128 {
        let val = self.0.compute(args);
        val.swap_bytes() >> (((128 - num_bits) / 8) * 8)
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct AddOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for AddOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args).wrapping_add(self.1.compute(args))
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct SubOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for SubOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args).wrapping_sub(self.1.compute(args))
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct MulOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for MulOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args).wrapping_mul(self.1.compute(args))
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct CarrylessMulOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for CarrylessMulOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let x = self.0.compute(args);
        let y = self.1.compute(args);

        let mut result = 0;
        for i in 0..128 {
            if (x >> i) & 1 != 0 {
                result ^= y << i
            }
        }

        result
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct DivOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for DivOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args);
        let b = self.1.compute(args);
        if b == 0 { 0 } else { a.wrapping_div(b) }
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct UnsignedDivOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for UnsignedDivOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args) as u128;
        let b = self.1.compute(args) as u128;
        if b == 0 { 0 } else { (a.wrapping_div(b)) as i128 }
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct RemOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for RemOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args);
        let b = self.1.compute(args);
        if b == 0 { 0 } else { a.wrapping_rem(b) }
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct UnsignedRemOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for UnsignedRemOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args) as u128;
        let b = self.1.compute(args) as u128;
        if b == 0 { 0 } else { (a.wrapping_rem(b)) as i128 }
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct ShlOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for ShlOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args);
        let b = self.1.compute(args);
        a.wrapping_shl(b as u32)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct ShrOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for ShrOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args);
        let b = self.1.compute(args);
        a.wrapping_shr(b as u32)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct AndOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for AndOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args) & self.1.compute(args)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct OrOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for OrOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args) | self.1.compute(args)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct XorOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for XorOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        self.0.compute(args) ^ self.1.compute(args)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct CmpLtOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for CmpLtOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        i128::from(self.0.compute(args) < self.1.compute(args))
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct RolOp<const NUM_BITS: u8, V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<const NUM_BITS: u8, V: FastOpImpl, W: FastOpImpl> FastOpImpl for RolOp<NUM_BITS, V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let a = self.0.compute(args);
        let b = self.1.compute(args);
        compute_rol(a, b, NUM_BITS)
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[inline(always)]
fn compute_rol(val: i128, n: i128, num_bits: u8) -> i128 {
    let mask = (u128::MAX >> (128 - num_bits)) as i128;
    let a = val & mask;
    let n = (n as u32) % num_bits as u32;

    (a.wrapping_shl(n) | a.wrapping_shr(num_bits as u32 - n)) & mask
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct IfZeroOp<COND: FastOpImpl, ZERO: FastOpImpl, NZERO: FastOpImpl>(pub COND, pub ZERO, pub NZERO);

impl<COND: FastOpImpl, ZERO: FastOpImpl, NZERO: FastOpImpl> FastOpImpl for IfZeroOp<COND, ZERO, NZERO> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let condition = self.0.compute(args);
        let zero = self.1.compute(args);
        let nonzero = self.2.compute(args);

        if condition == 0 { zero } else { nonzero }
    }

    fn reconstruct() -> Self {
        Self(COND::reconstruct(), ZERO::reconstruct(), NZERO::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct DepositBitsOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for DepositBitsOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let source = self.0.compute(args) as u128;
        let selector = self.1.compute(args) as u128;
        deposit_bits_u128(source, selector) as i128
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

#[doc(hidden)] // public for macro
#[derive(Copy, Clone, Debug)]
pub struct ExtractBitsOp<V: FastOpImpl, W: FastOpImpl>(pub V, pub W);

impl<V: FastOpImpl, W: FastOpImpl> FastOpImpl for ExtractBitsOp<V, W> {
    #[inline(always)]
    fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        let mut source = self.0.compute(args) as u128;
        let mut selector = self.1.compute(args) as u128;
        let mut dest = 0u128;

        let mut dest_bit = 0;
        while selector != 0 {
            let bit_index = selector.trailing_zeros();
            source >>= bit_index;
            let bit = source & 1;

            selector >>= bit_index + 1;
            source >>= 1;

            dest |= bit << dest_bit;
            dest_bit += 1;
        }

        dest as i128
    }

    fn reconstruct() -> Self {
        Self(V::reconstruct(), W::reconstruct())
    }
}

const DEFAULT_OP: Op = Op::Hole(0);

impl Default for Op {
    fn default() -> Self {
        DEFAULT_OP
    }
}

impl Op {
    /// Returns the default operation, which is `A` (first hole).
    pub const fn const_default() -> Self {
        DEFAULT_OP
    }

    /// Returns the number of arguments the operation requires.
    pub fn num_args(&self) -> usize {
        use Op::*;
        match self {
            Hole(_) | Const(_) => 0,
            Not
            | IsZero
            | Crop {
                ..
            }
            | Select {
                ..
            }
            | Parity
            | SignExtend {
                ..
            }
            | ByteMask
            | BitMask
            | TrailingZeros
            | LeadingZeros
            | PopCount
            | SwapBytes {
                ..
            } => 1,
            Add
            | Sub
            | Mul
            | CarrylessMul
            | Div
            | UnsignedDiv
            | Rem
            | UnsignedRem
            | Shl
            | Shr
            | And
            | Or
            | Xor
            | CmpLt
            | Rol {
                ..
            }
            | DepositBits
            | ExtractBits => 2,
            IfZero => 3,
        }
    }

    /// Returns an infix string that can be used for printing the operation.
    pub fn as_infix(&self) -> Option<&str> {
        Some(match self {
            Op::Add => "+",
            Op::Sub => "-",
            Op::Mul => "*",
            Op::Div => "/",
            Op::Rem => "%",
            Op::Shl => "<<",
            Op::Shr => ">>",
            Op::And => "&",
            Op::Or => "|",
            Op::Xor => "^",
            _ => return None,
        })
    }

    /// Returns true if the operation is commutative.
    pub fn is_commutative(&self) -> bool {
        matches!(self, Op::Add | Op::Mul | Op::And | Op::Or | Op::Xor) || self.num_args() <= 1
    }

    /// Returns true if the operation is associative.
    pub fn is_associative(&self) -> bool {
        matches!(self, Op::Add | Op::Mul | Op::And | Op::Or | Op::Xor) || self.num_args() <= 1
    }

    /// Evaluates the operation on the given `top_of_stack` and `stack`.
    pub fn eval_from_stack<const N: usize>(
        &self, args: &impl Fn(usize) -> i128, top_of_stack: i128, stack: &mut ArrayVec<i128, N>,
    ) -> i128 {
        match self {
            Op::Const(v) => {
                stack.push(top_of_stack);
                *v as i128
            },
            Op::Hole(n) => {
                stack.push(top_of_stack);
                args(*n as usize)
            },
            Op::Add => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                AddOp(Val(a), Val(b)).compute(args)
            },
            Op::Sub => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                SubOp(Val(a), Val(b)).compute(args)
            },
            Op::Mul => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                MulOp(Val(a), Val(b)).compute(args)
            },
            Op::CarrylessMul => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                CarrylessMulOp(Val(a), Val(b)).compute(args)
            },
            Op::Div => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                DivOp(Val(a), Val(b)).compute(args)
            },
            Op::UnsignedDiv => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                UnsignedDivOp(Val(a), Val(b)).compute(args)
            },
            Op::Rem => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                RemOp(Val(a), Val(b)).compute(args)
            },
            Op::UnsignedRem => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                UnsignedRemOp(Val(a), Val(b)).compute(args)
            },
            Op::Shl => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                ShlOp(Val(a), Val(b)).compute(args)
            },
            Op::Shr => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                ShrOp(Val(a), Val(b)).compute(args)
            },
            Op::And => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                AndOp(Val(a), Val(b)).compute(args)
            },
            Op::Or => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                OrOp(Val(a), Val(b)).compute(args)
            },
            Op::Xor => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                XorOp(Val(a), Val(b)).compute(args)
            },
            Op::CmpLt => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                CmpLtOp(Val(a), Val(b)).compute(args)
            },
            Op::Rol {
                num_bits,
            } => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                compute_rol(a, b, *num_bits)
            },
            Op::DepositBits => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                DepositBitsOp(Val(a), Val(b)).compute(args)
            },
            Op::ExtractBits => {
                let b = top_of_stack;
                let a = stack.pop().unwrap();
                ExtractBitsOp(Val(a), Val(b)).compute(args)
            },
            Op::Not => NotOp(Val(top_of_stack)).compute(args),
            Op::Parity => ParityOp(Val(top_of_stack)).compute(args),
            Op::IsZero => IsZeroOp(Val(top_of_stack)).compute(args),
            Op::Crop {
                num_bits,
            } => top_of_stack & ((1 << *num_bits) - 1),
            Op::SignExtend {
                num_bits,
            } => sign_extend(top_of_stack & ((1 << *num_bits) - 1), *num_bits as usize),
            Op::Select {
                num_skip,
                num_take,
            } => (top_of_stack >> *num_skip) & ((1i128 << *num_take) - 1),
            Op::IfZero => {
                let nonzero = top_of_stack;
                let zero = stack.pop().unwrap();
                let condition = stack.pop().unwrap();
                IfZeroOp(Val(condition), Val(zero), Val(nonzero)).compute(args)
            },
            Op::ByteMask => ByteMaskOp(Val(top_of_stack)).compute(args),
            Op::BitMask => BitMaskOp(Val(top_of_stack)).compute(args),
            Op::TrailingZeros => TrailingZerosOp(Val(top_of_stack)).compute(args),
            Op::LeadingZeros => LeadingZerosOp(Val(top_of_stack)).compute(args),
            Op::PopCount => PopCountOp(Val(top_of_stack)).compute(args),
            Op::SwapBytes {
                num_bits,
            } => SwapBytesOp::<0, _>(Val(top_of_stack)).compute_internal(args, *num_bits),
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Const(v) => write!(f, "{v}"),
            Op::Hole(n) => write!(f, "Arg[{n}]"),
            Op::Add => write!(f, "Add"),
            Op::Sub => write!(f, "Sub"),
            Op::Mul => write!(f, "Mul"),
            Op::CarrylessMul => write!(f, "CarrylessMul"),
            Op::UnsignedDiv => write!(f, "UnsignedDiv"),
            Op::Div => write!(f, "Div"),
            Op::Rem => write!(f, "Rem"),
            Op::UnsignedRem => write!(f, "UnsignedRem"),
            Op::Shl => write!(f, "Shl"),
            Op::Shr => write!(f, "Shr"),
            Op::And => write!(f, "And"),
            Op::Or => write!(f, "Or"),
            Op::Xor => write!(f, "Xor"),
            Op::CmpLt => write!(f, "CmpLt"),
            Op::Rol {
                num_bits,
            } => write!(f, "Rol[{num_bits}]"),
            Op::Not => write!(f, "Not"),
            Op::Parity => write!(f, "Parity"),
            Op::IsZero => write!(f, "IsZero"),
            Op::Crop {
                num_bits,
            } => write!(f, "Crop[{num_bits}]"),
            Op::Select {
                num_skip,
                num_take,
            } => write!(f, "Select[{num_skip}:+{num_take}]"),
            Op::SignExtend {
                num_bits,
            } => write!(f, "SignExtend[{num_bits}]"),
            Op::IfZero => write!(f, "IfZero"),
            Op::ByteMask => write!(f, "ByteMask"),
            Op::BitMask => write!(f, "BitMask"),
            Op::TrailingZeros => write!(f, "TrailingZeros"),
            Op::LeadingZeros => write!(f, "LeadingZeros"),
            Op::PopCount => write!(f, "PopCount"),
            Op::SwapBytes {
                num_bits,
            } => write!(f, "SwapBytes[{num_bits}]"),
            Op::DepositBits => write!(f, "DepositBits"),
            Op::ExtractBits => write!(f, "ExtractBits"),
        }
    }
}

#[cfg(test)]
mod tests {
    use arrayvec::ArrayVec;
    use rand::Rng;

    use crate::semantics::default::ops::{DepositBitsOp, ExtractBitsOp, FastOpImpl, Op, Val};

    #[test]
    pub fn test_execute_bytemask() {
        assert_eq!(
            Op::ByteMask.eval_from_stack(&|_| panic!(), 0x80, &mut ArrayVec::<_, 0>::from([])),
            0b1
        );
        assert_eq!(
            Op::ByteMask.eval_from_stack(&|_| panic!(), 0x00_00_00_00_80_42_75_82, &mut ArrayVec::<_, 0>::from([])),
            0b1001
        );
    }

    #[test]
    pub fn op_sub() {
        assert_eq!(
            Op::Sub.eval_from_stack(&|_| panic!(), 10, &mut ArrayVec::<_, 1>::from([100])),
            90
        );
    }

    #[test]
    pub fn op_rol() {
        assert_eq!(
            Op::Rol {
                num_bits: 8
            }
            .eval_from_stack(&|_| panic!(), 3, &mut ArrayVec::<_, 1>::from([0xf0])),
            0x87
        );
        assert_eq!(
            Op::Rol {
                num_bits: 10
            }
            .eval_from_stack(&|_| panic!(), 3, &mut ArrayVec::<_, 1>::from([0xf0])),
            0x381
        );
    }

    #[test]
    pub fn op_deposit_bits() {
        let deposited = DepositBitsOp(Val(0x4C279FFF), Val(0xFFFFFEDE)).compute(&|_| panic!());
        let expected = 0x613CFEDE;
        assert_eq!(deposited, expected, "\nFound: \n{deposited:b}; \nExpected: \n{expected:b}");

        let deposited = DepositBitsOp(Val(0xE18F6A57), Val(0xCDDBFFFF)).compute(&|_| panic!());
        let expected = 0xC1B6A57;
        assert_eq!(deposited, expected, "\nFound: \n{deposited:b}; \nExpected: \n{expected:b}");
    }

    #[test]
    pub fn fuzz_deposit_extract_bits() {
        let mut rng = rand::thread_rng();
        for _ in 0..1_000_000 {
            let source = rng.gen();
            let selector = rng.gen();

            let deposited = DepositBitsOp(Val(source), Val(selector)).compute(&|_| panic!());
            let extracted = ExtractBitsOp(Val(deposited), Val(selector)).compute(&|_| panic!());
            let deposited2 = DepositBitsOp(Val(extracted), Val(selector)).compute(&|_| panic!());

            assert_eq!(
                deposited, deposited2,
                "\nSource: \n{source:b}; \nSelector: \n{selector:b}; \nDeposited: \n{deposited:b}; \nExtracted: {extracted:b}; Deposited (2): {deposited2:b}"
            );
            assert_eq!(extracted, source & ((1 << selector.count_ones()) - 1));
        }

        assert_eq!(
            Op::Rol {
                num_bits: 8
            }
            .eval_from_stack(&|_| panic!(), 3, &mut ArrayVec::<_, 1>::from([0xf0])),
            0x87
        );
        assert_eq!(
            Op::Rol {
                num_bits: 10
            }
            .eval_from_stack(&|_| panic!(), 3, &mut ArrayVec::<_, 1>::from([0xf0])),
            0x381
        );
    }

    #[test]
    pub fn op_if_zero() {
        {
            let condition = 1;
            let zero = 5;
            let nonzero = 3;
            assert_eq!(
                Op::IfZero.eval_from_stack(&|_| panic!(), nonzero, &mut ArrayVec::<_, 2>::from([condition, zero])),
                nonzero
            );
        }

        {
            let condition = 0;
            let zero = 5;
            let nonzero = 3;
            assert_eq!(
                Op::IfZero.eval_from_stack(&|_| panic!(), nonzero, &mut ArrayVec::<_, 2>::from([condition, zero])),
                zero
            );
        }
    }
}
