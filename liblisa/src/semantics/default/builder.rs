//! Builder for [`Expr`](super::Expr)s.

use std::fmt::Debug;
use std::ptr::copy_nonoverlapping;

use super::ops::*;

const MAX_OPS: usize = 1024;

#[derive(Copy, Clone)]
// Hide this struct from documentation, because it is an implementation detail of the `expr!` macro.
#[doc(hidden)]
pub struct OpWriter {
    data: [Op; MAX_OPS],
    index: usize,
}

impl Default for OpWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl OpWriter {
    #[inline]
    pub const fn new() -> Self {
        OpWriter {
            data: [Op::const_default(); MAX_OPS],
            index: 0,
        }
    }

    #[inline]
    pub const fn write(mut self, op: Op) -> Self {
        self.data[self.index] = op;
        self.index += 1;
        self
    }

    #[inline]
    pub const fn write_builder<const N: usize, I: FastOpImpl>(mut self, ops: ExprBuilder<N, I>) -> Self {
        assert!(self.index + ops.ops.index < MAX_OPS);
        // SAFETY: Assert above ensures correctness
        unsafe {
            let target = self.data.as_mut_ptr().add(self.index);
            copy_nonoverlapping(ops.ops.data.as_ptr(), target, ops.ops.index);
        }

        self.index += ops.ops.index;

        self
    }

    #[inline]
    pub const fn unop<const N: usize, I: FastOpImpl>(val: ExprBuilder<N, I>, suffix: Op) -> Self {
        val.ops.write(suffix)
    }

    #[inline]
    pub const fn binop<const N: usize, const M: usize, I1: FastOpImpl, I2: FastOpImpl>(
        lhs: ExprBuilder<N, I1>, rhs: ExprBuilder<M, I2>, suffix: Op,
    ) -> Self {
        lhs.ops.write_builder(rhs).write(suffix)
    }

    #[inline]
    pub const fn copy_to(self, target: &mut [Op]) {
        let mut n = 0;
        while n < self.index {
            target[n] = self.data[n];
            n += 1;
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[Op] {
        assert!(self.index <= MAX_OPS);
        // SAFETY: The assertion above ensures correctness
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), self.index) }
    }
}

impl Debug for OpWriter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.as_slice(), f)
    }
}

#[doc(hidden)] // Only public for macro
#[derive(Copy, Clone, Debug)]
pub struct ExprBuilder<const N: usize, I: FastOpImpl> {
    num_ops: usize,
    ops: OpWriter,
    pub builder: I,
}

type AbsResult<const N: usize, I> = ExprBuilder<N, IfZeroOp<SelectOp<127, 1, I>, I, AddOp<NotOp<I>, ConstOp<1>>>>;

impl<const N: usize, I: FastOpImpl> ExprBuilder<N, I> {
    #[inline]
    pub const fn into_inner(self) -> I {
        self.builder
    }

    #[inline]
    pub const fn num_ops(&self) -> usize {
        self.num_ops
    }

    #[inline]
    pub const fn ops(&self) -> OpWriter {
        self.ops
    }

    #[inline(always)]
    pub fn compute(&self, args: &impl Fn(usize) -> i128) -> i128 {
        // By making this not depend on self, the compiler will optimize out construction of `ops`
        I::reconstruct().compute(args)
    }

    #[inline]
    pub const fn crop<const NUM_BITS: u8>(self) -> ExprBuilder<{ N + 1 }, CropOp<NUM_BITS, I>> {
        ExprBuilder {
            num_ops: self.num_ops + 1,
            ops: self.ops.write(Op::Crop {
                num_bits: NUM_BITS,
            }),
            builder: CropOp(self.builder),
        }
    }

    #[inline]
    pub const fn rol<const NUM_BITS: u8, const M: usize, B: FastOpImpl>(
        self, rhs: ExprBuilder<M, B>,
    ) -> ExprBuilder<{ N + M + 1 }, RolOp<NUM_BITS, I, B>> {
        ExprBuilder {
            num_ops: self.num_ops + rhs.num_ops + 1,
            ops: OpWriter::binop(
                self,
                rhs,
                Op::Rol {
                    num_bits: NUM_BITS,
                },
            ),
            builder: RolOp(self.builder, rhs.builder),
        }
    }

    #[inline]
    pub const fn sign_extend<const NUM_BITS: u8>(self) -> ExprBuilder<{ N + 1 }, SignExtendOp<NUM_BITS, I>> {
        ExprBuilder {
            num_ops: self.num_ops + 1,
            ops: self.ops.write(Op::SignExtend {
                num_bits: NUM_BITS,
            }),
            builder: SignExtendOp(self.builder),
        }
    }

    #[inline]
    pub const fn if_zero<const M: usize, const L: usize, ZERO: FastOpImpl, NZERO: FastOpImpl>(
        self, zero: ExprBuilder<M, ZERO>, nonzero: ExprBuilder<L, NZERO>,
    ) -> ExprBuilder<{ N + M + L + 1 }, IfZeroOp<I, ZERO, NZERO>> {
        ExprBuilder {
            num_ops: self.num_ops + zero.num_ops + nonzero.num_ops + 1,
            ops: OpWriter::new()
                .write_builder(self)
                .write_builder(zero)
                .write_builder(nonzero)
                .write(Op::IfZero),
            builder: IfZeroOp(self.builder, zero.builder, nonzero.builder),
        }
    }

    #[inline]
    pub const fn byte_mask(self) -> ExprBuilder<{ N + 1 }, ByteMaskOp<I>> {
        ExprBuilder {
            num_ops: self.num_ops + 1,
            ops: OpWriter::unop(self, Op::ByteMask),
            builder: ByteMaskOp(self.builder),
        }
    }

    #[inline]
    pub const fn trailing_zeros(self) -> ExprBuilder<{ N + 1 }, TrailingZerosOp<I>> {
        ExprBuilder {
            num_ops: self.num_ops + 1,
            ops: OpWriter::unop(self, Op::TrailingZeros),
            builder: TrailingZerosOp(self.builder),
        }
    }

    #[inline]
    pub const fn leading_zeros(self) -> ExprBuilder<{ N + 1 }, LeadingZerosOp<I>> {
        ExprBuilder {
            num_ops: self.num_ops + 1,
            ops: OpWriter::unop(self, Op::LeadingZeros),
            builder: LeadingZerosOp(self.builder),
        }
    }

    #[inline]
    pub const fn popcount(self) -> ExprBuilder<{ N + 1 }, PopCountOp<I>>
    where
        Self: Clone,
    {
        ExprBuilder {
            num_ops: self.num_ops + 1,
            ops: OpWriter::unop(self, Op::PopCount),
            builder: PopCountOp(self.builder),
        }
    }

    #[inline]
    pub const fn abs(self) -> AbsResult<{ N * 3 + 5 }, I> {
        // if_zero(select[127:+1](self), self, add(not(self), 1))
        ExprBuilder {
            num_ops: self.num_ops * 3 + 5,
            ops: OpWriter::new()
                .write_builder(self)
                .write(Op::Select {
                    num_skip: 127,
                    num_take: 1,
                })
                .write_builder(self)
                .write_builder(self)
                .write(Op::Not)
                .write(Op::Const(1))
                .write(Op::Add)
                .write(Op::IfZero),
            builder: IfZeroOp(
                SelectOp::<127, 1, _>(self.builder),
                self.builder,
                AddOp(NotOp(self.builder), ConstOp::<1>),
            ),
        }
    }

    #[inline]
    pub const fn extract_bits<const M: usize, B: FastOpImpl>(
        self, selector: ExprBuilder<M, B>,
    ) -> ExprBuilder<{ N + M + 1 }, ExtractBitsOp<I, B>>
    where
        Self: Clone,
    {
        ExprBuilder {
            num_ops: self.num_ops + selector.num_ops + 1,
            ops: OpWriter::binop(self, selector, Op::ExtractBits),
            builder: ExtractBitsOp(self.builder, selector.builder),
        }
    }

    #[inline]
    pub const fn deposit_bits<const M: usize, B: FastOpImpl>(
        self, selector: ExprBuilder<M, B>,
    ) -> ExprBuilder<{ N + M + 1 }, DepositBitsOp<I, B>>
    where
        Self: Clone,
    {
        ExprBuilder {
            num_ops: self.num_ops + selector.num_ops + 1,
            ops: OpWriter::binop(self, selector, Op::DepositBits),
            builder: DepositBitsOp(self.builder, selector.builder),
        }
    }
}

/// Multiply two values.
#[inline]
pub const fn mul<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, MulOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Mul),
        builder: MulOp(a.builder, b.builder),
    }
}

/// Perform a carryless multiplication.
#[inline]
pub const fn carryless_mul<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, CarrylessMulOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::CarrylessMul),
        builder: CarrylessMulOp(a.builder, b.builder),
    }
}

/// Perform a division.
#[inline]
pub const fn div<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, DivOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Div),
        builder: DivOp(a.builder, b.builder),
    }
}

/// Perform an unsigned divide.
#[inline]
pub const fn udiv<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, UnsignedDivOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::UnsignedDiv),
        builder: UnsignedDivOp(a.builder, b.builder),
    }
}

/// Compute the remainder of a value.
#[inline]
pub const fn rem<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, RemOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Rem),
        builder: RemOp(a.builder, b.builder),
    }
}

/// Compute the unsigned remainder of a value.
#[inline]
pub const fn urem<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, UnsignedRemOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::UnsignedRem),
        builder: UnsignedRemOp(a.builder, b.builder),
    }
}

/// Perform a left shift.
#[inline]
pub const fn shl<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, ShlOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Shl),
        builder: ShlOp(a.builder, b.builder),
    }
}

/// Perform a right shift.
#[inline]
pub const fn shr<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, ShrOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Shr),
        builder: ShrOp(a.builder, b.builder),
    }
}

/// Perform a bitwise AND.
#[inline]
pub const fn and<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, AndOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::And),
        builder: AndOp(a.builder, b.builder),
    }
}

/// Perform an addition.
#[inline]
pub const fn add<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, AddOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Add),
        builder: AddOp(a.builder, b.builder),
    }
}

/// Perform a subtraction.
#[inline]
pub const fn sub<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, SubOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Sub),
        builder: SubOp(a.builder, b.builder),
    }
}

/// Perform a bitwise OR.
#[inline]
pub const fn or<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, OrOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Or),
        builder: OrOp(a.builder, b.builder),
    }
}

/// Perform a bitwise XOR.
#[inline]
pub const fn xor<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, XorOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::Xor),
        builder: XorOp(a.builder, b.builder),
    }
}

/// Perform a bitwise NOT.
#[inline]
pub const fn not<const N: usize, A: FastOpImpl>(a: ExprBuilder<N, A>) -> ExprBuilder<{ N + 1 }, NotOp<A>> {
    ExprBuilder {
        num_ops: N + 1,
        ops: OpWriter::unop(a, Op::Not),
        builder: NotOp(a.builder),
    }
}

/// Computes the parity of the lower 8 bits.
#[inline]
pub const fn parity<const N: usize, A: FastOpImpl>(a: ExprBuilder<N, A>) -> ExprBuilder<{ N + 1 }, ParityOp<A>> {
    ExprBuilder {
        num_ops: N + 1,
        ops: OpWriter::unop(a, Op::Parity),
        builder: ParityOp(a.builder),
    }
}

/// Selects a range of bits.
#[inline]
pub const fn select<const NUM_SKIP: u8, const NUM_TAKE: u8, const N: usize, A: FastOpImpl>(
    a: ExprBuilder<N, A>,
) -> ExprBuilder<{ N + 1 }, SelectOp<NUM_SKIP, NUM_TAKE, A>> {
    ExprBuilder {
        num_ops: N + 1,
        ops: OpWriter::unop(
            a,
            Op::Select {
                num_skip: NUM_SKIP,
                num_take: NUM_TAKE,
            },
        ),
        builder: SelectOp(a.builder),
    }
}

/// Concatenate bits.
#[inline]
pub const fn concat_bit<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ (N + 2) + M + 1 }, OrOp<ShlOp<A, ConstOp<1>>, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::new()
            .write_builder(a)
            .write(Op::Const(1))
            .write(Op::Shl)
            .write_builder(b)
            .write(Op::Or),
        builder: OrOp(ShlOp(a.builder, ConstOp::<1>), b.builder),
    }
}

/// Returns `1` if the value is 0, otherwise returns `0`.
#[inline]
pub const fn is_zero<const N: usize, A: FastOpImpl>(a: ExprBuilder<N, A>) -> ExprBuilder<{ N + 1 }, IsZeroOp<A>> {
    ExprBuilder {
        num_ops: N + 1,
        ops: OpWriter::unop(a, Op::IsZero),
        builder: IsZeroOp(a.builder),
    }
}

/// Returns `1` if `a` is less than `b`. Returns `0` if `a` is equal to or greater than `b`.
#[inline]
pub const fn less_than<const N: usize, const M: usize, A: FastOpImpl, B: FastOpImpl>(
    a: ExprBuilder<N, A>, b: ExprBuilder<M, B>,
) -> ExprBuilder<{ N + M + 1 }, CmpLtOp<A, B>> {
    ExprBuilder {
        num_ops: N + M + 1,
        ops: OpWriter::binop(a, b, Op::CmpLt),
        builder: CmpLtOp(a.builder, b.builder),
    }
}

/// Computes (1 << N) - 1, which is an integer with the lowest N bits set to 1 and the rest to 0.
#[inline]
pub const fn bit_mask<const N: usize, A: FastOpImpl>(a: ExprBuilder<N, A>) -> ExprBuilder<{ N + 1 }, BitMaskOp<A>> {
    ExprBuilder {
        num_ops: N + 1,
        ops: OpWriter::unop(a, Op::BitMask),
        builder: BitMaskOp(a.builder),
    }
}

/// Returns a template hole.
#[inline]
pub const fn hole<const N: u16>() -> ExprBuilder<1, HoleOp<N>> {
    ExprBuilder {
        num_ops: 1,
        ops: OpWriter::new().write(Op::Hole(N)),
        builder: HoleOp::<N>,
    }
}

/// Returns the constant 0.
#[inline]
pub const fn zero() -> ExprBuilder<1, ConstOp<0>> {
    c::<0>()
}

/// Returns the constant 1.
#[inline]
pub const fn one() -> ExprBuilder<1, ConstOp<1>> {
    c::<1>()
}

/// Returns a constant.
#[inline]
pub const fn c<const VAL: i8>() -> ExprBuilder<1, ConstOp<VAL>> {
    ExprBuilder {
        num_ops: 1,
        ops: OpWriter::new().write(Op::Const(VAL)),
        builder: ConstOp::<VAL>,
    }
}
