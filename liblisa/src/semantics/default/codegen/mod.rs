//! Provides [`CodeGenerator`], a trait for code generation.
//!
//! Also provides two code generators in submodules:
//!
//! - [`sexpr::SExprCodeGen`]
//! - [`smt::Z3CodeGen`]

use log::trace;

use crate::semantics::default::computation::{Arg, ArgEncoding, AsComputationRef, OutputEncoding};
use crate::semantics::default::ops::Op;

pub mod sexpr;
pub mod smt;

/// A code generator that can generate code for computations.
pub trait CodeGenerator {
    /// An expression in the generated code.
    type T;

    /// Create a constant value.
    fn leaf_const(&mut self, value: i128) -> Self::T;

    /// Create a value that loads the argument.
    fn leaf_arg(&mut self, arg_index: usize) -> Term<Self::T>;

    /// Simplify the expression, if possible.
    fn simplify(&mut self, item: Self::T) -> Self::T {
        item
    }

    /// Generate an error for an unknown operation.
    fn unknown_op_any(&mut self, name: &str, args: &[Self::T]) -> Self::T;

    /// Generate an error for a 1-argument unknown operation.
    fn unknown_op1(&mut self, name: &str, item: Self::T) -> Self::T {
        self.unknown_op_any(name, &[item])
    }

    /// Generate an error for a 2-argument unknown operation.
    fn unknown_op2(&mut self, name: &str, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op_any(name, &[lhs, rhs])
    }

    /// Generate an error for a 3-argument unknown operation.
    fn unknown_op3(&mut self, name: &str, arg0: Self::T, arg1: Self::T, arg2: Self::T) -> Self::T {
        self.unknown_op_any(name, &[arg0, arg1, arg2])
    }

    /// Negate the expression.
    fn not(&mut self, item: Self::T) -> Self::T {
        self.unknown_op1("not", item)
    }

    /// Crop the expression to the lowest `num_bits` bits.
    fn crop(&mut self, num_bits: u8, item: Self::T) -> Self::T {
        self.select(0, num_bits, item)
    }

    /// Crop the expression to the lowest `num_bits` bits, then sign-extend it.
    fn sign_extend(&mut self, num_bits: u8, item: Self::T) -> Self::T {
        self.unknown_op1(&format!("sign_extend{num_bits}"), item)
    }

    /// Select `num_take` bits starting at bit index `num_skip` from `item`.
    fn select(&mut self, num_skip: u8, num_take: u8, item: Self::T) -> Self::T {
        self.unknown_op1(&format!("select{num_skip}_{num_take}"), item)
    }

    /// Crop the expression to the lowest 8 bits, then compute the parity.
    fn parity(&mut self, item: Self::T) -> Self::T {
        let low8 = self.crop(8, item);
        self.popcount(low8)
    }

    /// Return '1' if the expression is zero, otherwise return '0'.
    fn is_zero(&mut self, item: Self::T) -> Self::T {
        let if_zero = self.leaf_const(1);
        let if_nonzero = self.leaf_const(0);
        self.if_zero(item, if_zero, if_nonzero)
    }

    /// Return the byte mask for the expression.
    fn byte_mask(&mut self, item: Self::T) -> Self::T {
        self.unknown_op1("byte_mask", item)
    }

    /// Return a bit mask for the given number of bits.
    fn bit_mask(&mut self, item: Self::T) -> Self::T {
        let all_ones = self.leaf_const(-1);
        let negated_bitmask = self.shl(all_ones, item);
        self.not(negated_bitmask)
    }

    /// Count the number of trailing zeros.
    fn trailing_zeros(&mut self, item: Self::T) -> Self::T {
        self.unknown_op1("trailing_zeros", item)
    }

    /// Count the number of leading zeros.
    fn leading_zeros(&mut self, item: Self::T) -> Self::T {
        self.unknown_op1("leading_zeros", item)
    }

    /// Count the number of ones.
    fn popcount(&mut self, item: Self::T) -> Self::T {
        self.unknown_op1("popcount", item)
    }

    /// Reverse the order of the lowest `ceil(num_bits / 8)` bytes.
    fn swap_bytes(&mut self, num_bits: u8, item: Self::T) -> Self::T {
        self.unknown_op1(&format!("swap_bytes{num_bits}"), item)
    }

    /// Add two values.
    fn add(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("add", lhs, rhs)
    }

    /// Subtract `rhs` from `lhs`.
    fn sub(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("sub", lhs, rhs)
    }

    /// Multiply two values.
    fn mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("mul", lhs, rhs)
    }

    /// Perform carryless multiplication.
    fn carryless_mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("carryless_mul", lhs, rhs)
    }

    /// Perform signed division.
    fn div(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("div", lhs, rhs)
    }

    /// Perform unsigned division.
    fn div_unsigned(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("div_unsigned", lhs, rhs)
    }

    /// Compute the signed remainder.
    fn rem(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("rem", lhs, rhs)
    }

    /// Compute the unsigned remainder.
    fn rem_unsigned(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("rem_unsigned", lhs, rhs)
    }

    /// Shift `lhs` left by `rhs` positions.
    fn shl(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("shl", lhs, rhs)
    }

    /// Shift `lhs` right by `rhs` positions.
    fn shr(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("shr", lhs, rhs)
    }

    /// Compute the bitwise AND.
    fn and(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("and", lhs, rhs)
    }

    /// Compute the bitwise OR.
    fn or(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("or", lhs, rhs)
    }

    /// Compute the bitwise XOR.
    fn xor(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("xor", lhs, rhs)
    }

    /// Return '1' if `lhs` is less than `rhs`, return '1' otherwise.
    fn cmp_lt(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("cmp_lt", lhs, rhs)
    }

    /// Crop `lhs` to `num_bits`, then rotate those bits `rhs` positions.
    fn rol(&mut self, num_bits: u8, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2(&format!("rol{num_bits}"), lhs, rhs)
    }

    /// Perform the PDEP operation.
    fn deposit_bits(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("deposit_bits", lhs, rhs)
    }

    /// Perform the PEXT operation
    fn extract_bits(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        self.unknown_op2("extract_bits", lhs, rhs)
    }

    /// If `condition` is zero, return `if_zero`. Otherwise, return `if_nonzero`.
    fn if_zero(&mut self, condition: Self::T, if_zero: Self::T, if_nonzero: Self::T) -> Self::T {
        self.unknown_op3("if_zero", condition, if_zero, if_nonzero)
    }
}

/// A term in the code generator
#[derive(Copy, Clone, Debug)]
pub enum TermOp {
    /// Crop the value to `num_bits`.
    Crop {
        /// The number of bits.
        num_bits: u8,
    },

    /// Reverse the order of the lowest `ceil(num_bits / 8)` bytes.
    SwapBytes {
        /// The number of bits.
        num_bits: u8,
    },

    /// Crop the value to `num_bits` and sign-extend it.
    SignExtend {
        /// The number of bits.
        num_bits: u8,
    },
}

impl TermOp {
    /// Applies the operation to an expression.
    pub fn apply<C: CodeGenerator>(&self, g: &mut C, item: C::T) -> C::T {
        match *self {
            TermOp::Crop {
                num_bits,
            } => g.crop(num_bits, item),
            TermOp::SwapBytes {
                num_bits,
            } => g.swap_bytes(num_bits, item),
            TermOp::SignExtend {
                num_bits,
            } => g.sign_extend(num_bits, item),
        }
    }
}

/// A partially generated term.
#[derive(Clone, Debug)]
pub struct Term<T> {
    data: T,
    num_bits: usize,
    operations: Vec<TermOp>,
}

impl<T> Term<T> {
    /// Create a new term which is just the expression `data`.
    pub fn simple(data: T) -> Self {
        Self {
            data,
            num_bits: 128,
            operations: Vec::new(),
        }
    }

    /// Create a new term with a set of operations.
    pub fn new(data: T, num_bits: usize, operations: Vec<TermOp>) -> Self {
        Self {
            data,
            num_bits,
            operations,
        }
    }

    fn optimize_operations(mut ops: Vec<TermOp>) -> Vec<TermOp> {
        'repeat: loop {
            for (index, items) in ops.windows(2).enumerate() {
                match [items[0], items[1]] {
                    [TermOp::SwapBytes {
                        num_bits: a,
                    }, TermOp::SwapBytes {
                        num_bits: b,
                    }] if a == b => {
                        ops.remove(index);
                        ops.remove(index);
                        continue 'repeat;
                    },
                    _ => (),
                }
            }

            break
        }

        ops
    }

    /// Apply all pending operations to the term, then return it.
    pub fn unwrap<C: CodeGenerator<T = T>>(self, g: &mut C) -> T {
        let operations = Self::optimize_operations(self.operations);
        let mut data = self.data;
        for op in operations.iter() {
            data = op.apply(g, data)
        }

        data
    }

    /// Return the term, if there are no pending operations.
    /// Otherwise, panic.
    pub fn unwrap_if_applied(self) -> T {
        assert!(self.operations.is_empty());
        self.data
    }

    /// Maps the expression to a new type.
    pub fn map<R>(self, map: impl FnOnce(T) -> R) -> Term<R> {
        Term {
            data: map(self.data),
            num_bits: self.num_bits,
            operations: self.operations,
        }
    }
}

/// Generates code for a computation.
pub fn codegen_computation<C: CodeGenerator>(g: &mut C, computation: &impl AsComputationRef) -> C::T {
    let result = codegen_template(
        g,
        computation.expr().ops(),
        computation.arg_interpretation(),
        computation.consts(),
    );

    let num_bits = computation.as_internal().output_type().num_bits();
    let cropped = g.crop(num_bits.try_into().unwrap(), result);
    match computation.as_internal().output_encoding() {
        OutputEncoding::UnsignedLittleEndian => g.swap_bytes(num_bits.try_into().unwrap(), cropped),
        OutputEncoding::UnsignedBigEndian => cropped,
    }
}

fn apply_fn1<C: CodeGenerator>(g: &mut C, args: &mut Vec<Term<C::T>>, mut f: impl FnMut(&mut C, C::T) -> C::T) -> Term<C::T> {
    let lhs = args.remove(0).unwrap(g);
    Term::simple(f(g, lhs))
}

fn apply_fn2<C: CodeGenerator>(
    g: &mut C, args: &mut Vec<Term<C::T>>, mut f: impl FnMut(&mut C, C::T, C::T) -> C::T,
) -> Term<C::T> {
    let lhs = args.remove(0).unwrap(g);
    let rhs = args.remove(0).unwrap(g);
    Term::simple(f(g, lhs, rhs))
}

/// Generates code for an expression template.
pub fn codegen_template<C: CodeGenerator>(g: &mut C, ops: &[Op], arg_interpretation: &[Arg], consts: &[i128]) -> C::T {
    let mut stack = Vec::<Term<C::T>>::new();

    for &op in ops.iter() {
        let mut args = stack.drain(stack.len() - op.num_args()..).collect::<Vec<_>>();
        stack.push(match op {
            Op::Hole(n) => match arg_interpretation[n as usize] {
                Arg::Input {
                    index,
                    num_bits,
                    encoding,
                } => {
                    // TODO: Eliminate byte swapping, etc. by delaying some operations until we can no longer delay them.
                    let mut val = g.leaf_arg(index as usize);
                    if matches!(encoding, ArgEncoding::SignedLittleEndian | ArgEncoding::UnsignedLittleEndian) {
                        trace!("Swapping bytes of hole {n} of {num_bits} bits");
                        val.operations.push(TermOp::SwapBytes {
                            num_bits,
                        });
                    }

                    if matches!(encoding, ArgEncoding::SignedLittleEndian | ArgEncoding::SignedBigEndian) && num_bits != 128 {
                        val.operations.push(TermOp::SignExtend {
                            num_bits,
                        });
                    }

                    val
                },
                Arg::TinyConst(c) => Term::simple(g.leaf_const(c as i128)),
                Arg::Const(index) => Term::simple(g.leaf_const(consts[index as usize])),
            },
            Op::Const(c) => Term::simple(g.leaf_const(c as i128)),
            Op::Add => apply_fn2(g, &mut args, CodeGenerator::add),
            Op::Sub => apply_fn2(g, &mut args, CodeGenerator::sub),
            Op::Mul => apply_fn2(g, &mut args, CodeGenerator::mul),
            Op::CarrylessMul => apply_fn2(g, &mut args, CodeGenerator::carryless_mul),
            Op::Div => apply_fn2(g, &mut args, CodeGenerator::div),
            Op::UnsignedDiv => apply_fn2(g, &mut args, CodeGenerator::div_unsigned),
            Op::Rem => apply_fn2(g, &mut args, CodeGenerator::rem),
            Op::UnsignedRem => apply_fn2(g, &mut args, CodeGenerator::rem_unsigned),
            Op::Shl => apply_fn2(g, &mut args, CodeGenerator::shl),
            Op::Shr => apply_fn2(g, &mut args, CodeGenerator::shr),
            Op::And => apply_fn2(g, &mut args, CodeGenerator::and),
            Op::Or => apply_fn2(g, &mut args, CodeGenerator::or),
            Op::Xor => apply_fn2(g, &mut args, CodeGenerator::xor),
            Op::CmpLt => apply_fn2(g, &mut args, CodeGenerator::cmp_lt),

            Op::Rol {
                num_bits,
            } => {
                let lhs = args.remove(0).unwrap(g);
                let rhs = args.remove(0).unwrap(g);
                Term::simple(g.rol(num_bits, lhs, rhs))
            },
            Op::Not => apply_fn1(g, &mut args, CodeGenerator::not),
            Op::Parity => apply_fn1(g, &mut args, CodeGenerator::parity),
            Op::IsZero => apply_fn1(g, &mut args, CodeGenerator::is_zero),
            Op::Crop {
                num_bits,
            } => {
                let item = args.remove(0).unwrap(g);
                Term::simple(g.crop(num_bits, item))
            },
            Op::SignExtend {
                num_bits,
            } => {
                let item = args.remove(0).unwrap(g);
                Term::simple(g.sign_extend(num_bits, item))
            },
            Op::Select {
                num_skip,
                num_take,
            } => {
                let item = args.remove(0).unwrap(g);
                Term::simple(g.select(num_skip, num_take, item))
            },
            Op::ByteMask => apply_fn1(g, &mut args, CodeGenerator::byte_mask),
            Op::BitMask => apply_fn1(g, &mut args, CodeGenerator::bit_mask),
            Op::TrailingZeros => apply_fn1(g, &mut args, CodeGenerator::trailing_zeros),
            Op::LeadingZeros => apply_fn1(g, &mut args, CodeGenerator::leading_zeros),
            Op::PopCount => apply_fn1(g, &mut args, CodeGenerator::popcount),
            Op::SwapBytes {
                num_bits,
            } => {
                let mut item = args.remove(0);
                item.operations.push(TermOp::SwapBytes {
                    num_bits,
                });
                item
            },

            Op::IfZero => {
                let condition = args.remove(0).unwrap(g);
                let if_zero = args.remove(0).unwrap(g);
                let if_nonzero = args.remove(0).unwrap(g);
                Term::simple(g.if_zero(condition, if_zero, if_nonzero))
            },
            Op::DepositBits => apply_fn2(g, &mut args, CodeGenerator::deposit_bits),
            Op::ExtractBits => apply_fn2(g, &mut args, CodeGenerator::extract_bits),
        });
    }

    stack.pop().unwrap().unwrap(g)
}

#[cfg(test)]
mod tests {
    use super::codegen_template;
    use super::sexpr::SExprCodeGen;
    use crate::semantics::default::codegen::sexpr::SExpr;
    use crate::semantics::default::computation::{Arg, ArgEncoding};
    use crate::semantics::default::ops::Op;

    #[test]
    pub fn double_byteswap_removed() {
        let mut g = SExprCodeGen::new();
        let generated = codegen_template(
            &mut g,
            &[
                Op::Hole(0),
                Op::SwapBytes {
                    num_bits: 32,
                },
            ],
            &[Arg::Input {
                index: 0,
                num_bits: 32,
                encoding: ArgEncoding::UnsignedLittleEndian,
            }],
            &[],
        );

        assert_eq!(
            generated,
            SExpr::Input {
                index: 0
            }
        )
    }
}
