//! SMT code generator.

use std::fmt::Display;
use std::ops::Not;

use crate::semantics::default::codegen::{CodeGenerator, Term};
use crate::smt::{SmtBV, SmtBool, SmtSolver};

/// A Z3 bitvector expression.
pub struct Z3Expr<'a, S: SmtSolver<'a>>(S::BV);

impl<'a, S: SmtSolver<'a>> Clone for Z3Expr<'a, S> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Z3Expr<'ctx, S> {
    /// Returns the SMT solver bitvector of the expression.
    pub fn as_bv(&self) -> &S::BV {
        &self.0
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Display for Z3Expr<'ctx, S>
where
    S::BV: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

/// A code generator that generates Z3 expressions.
pub struct Z3CodeGen<'a, 'ctx, S: SmtSolver<'ctx>> {
    context: &'a mut S,
    args: Vec<Term<Z3Expr<'ctx, S>>>,
    // unknown_ops: HashMap<String, S::FuncDecl>,
}

impl<'a, 'ctx, S: SmtSolver<'ctx>> Z3CodeGen<'a, 'ctx, S> {
    /// Creates a new SMT code generator for the provided [`SmtSolver`] and arguments.
    pub fn new(context: &'a mut S, args: Vec<S::BV>) -> Self {
        Self {
            context,
            args: args.into_iter().map(|arg| Term::simple(Z3Expr(arg))).collect(),
        }
    }

    /// Creates a new SMT code generator for the provided [`SmtSolver`] and arguments.
    pub fn new_with_terms(context: &'a mut S, args: Vec<Term<S::BV>>) -> Self {
        Self {
            context,
            args: args.into_iter().map(|arg| arg.map(Z3Expr)).collect(),
        }
    }
}

impl<'a, 'ctx, S: SmtSolver<'ctx>> CodeGenerator for Z3CodeGen<'a, 'ctx, S> {
    type T = Z3Expr<'ctx, S>;

    fn leaf_const(&mut self, value: i128) -> Self::T {
        Z3Expr(self.context.bv_from_i128(value))
    }

    fn leaf_arg(&mut self, arg_index: usize) -> Term<Self::T> {
        self.args[arg_index].clone()
    }

    fn or(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(lhs.0 | rhs.0)
    }

    fn not(&mut self, item: Self::T) -> Self::T {
        Z3Expr(item.0.not())
    }

    fn and(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(lhs.0 & rhs.0)
    }

    fn xor(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(lhs.0 ^ rhs.0)
    }

    fn crop(&mut self, num_bits: u8, item: Self::T) -> Self::T {
        self.select(0, num_bits, item)
    }

    fn shl(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let num = self.crop(7, rhs);

        Z3Expr(lhs.0.bvshl(num.0))
    }

    fn shr(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let num = self.crop(7, rhs);

        Z3Expr(lhs.0.bvashr(num.0))
    }

    fn rol(&mut self, num_bits: u8, lhs: Self::T, rhs: Self::T) -> Self::T {
        let num_bits = num_bits as u32;
        let val = lhs.0.extract(num_bits - 1, 0);
        let amount = rhs.0.extract(31, 0).bvurem(self.context.bv_from_u64(num_bits as u64, 32));
        let amount = if num_bits > 32 {
            amount.zero_ext(num_bits - 32)
        } else {
            amount.extract(num_bits - 1, 0)
        };

        assert_eq!(val.get_size(), amount.get_size());

        let result = val.bvrotl(amount);

        Z3Expr(result.zero_ext(128 - num_bits))
    }

    fn select(&mut self, num_skip: u8, num_take: u8, item: Self::T) -> Self::T {
        Z3Expr(
            item.0
                .extract((num_skip + num_take - 1) as u32, num_skip as u32)
                .zero_ext(128 - num_take as u32),
        )
    }

    fn sign_extend(&mut self, num_bits: u8, item: Self::T) -> Self::T {
        let num_bits = num_bits as u32;
        Z3Expr(item.0.extract(num_bits - 1, 0).sign_ext(128 - num_bits))
    }

    fn parity(&mut self, item: Self::T) -> Self::T {
        let b = item.0;

        let bits = [0, 1, 2, 3, 4, 5, 6, 7].map(|index| b.clone().extract(index, index));

        let parity = bits.into_iter().reduce(|acc, el| acc ^ el).unwrap();

        Z3Expr((!parity).zero_ext(127))
    }

    fn add(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(lhs.0 + rhs.0)
    }

    fn sub(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(lhs.0 - rhs.0)
    }

    fn is_zero(&mut self, item: Self::T) -> Self::T {
        let one = self.context.bv_from_i64(1, 128);
        let zero = self.context.bv_from_i64(0, 128);
        self.if_zero(item, Z3Expr(one), Z3Expr(zero))
    }

    fn if_zero(&mut self, condition: Self::T, if_zero: Self::T, if_nonzero: Self::T) -> Self::T {
        let is_zero = condition.0._eq(self.context.bv_from_i64(0, 128));

        Z3Expr(is_zero.ite_bv(if_zero.0, if_nonzero.0))
    }

    fn cmp_lt(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let is_less_than = lhs.0.bvslt(rhs.0);
        Z3Expr(is_less_than.ite_bv(self.context.bv_from_i64(1, 128), self.context.bv_from_i64(0, 128)))
    }

    fn unknown_op_any(&mut self, name: &str, _args: &[Self::T]) -> Self::T {
        panic!("Unknown operation: {name}")
        // let op = if let Some(op) = self.unknown_ops.get(name) {
        //     op
        // } else {
        //     let bv = self.context.sort_bitvector(128);// Sort::bitvector(self.context, 128);
        //     let args = repeat(&bv).take(args.len()).collect::<Vec<_>>();
        //     let new = self.context.func_decl(name, &args, &bv);

        //     self.unknown_ops.insert(name.to_string(), new);
        //     self.unknown_ops.get(name).unwrap()
        // };

        // let args = args.iter()
        //     .map(|x| &x.0)
        //     .collect::<Vec<_>>();
        // Z3Expr(op.apply(&args).as_bv().unwrap())
    }

    fn byte_mask(&mut self, item: Self::T) -> Self::T {
        let bits = [0, 1, 2, 3, 4, 5, 6, 7]
            .map(|index| index * 8 + 7)
            .map(|index| item.0.clone().extract(index, index));

        let val = bits.into_iter().reduce(|acc, el| el.concat(acc)).unwrap();

        Z3Expr(val)
    }

    fn bit_mask(&mut self, item: Self::T) -> Self::T {
        // if N > 128 then all_ones else !(all_ones << N) endif

        let all_ones = self.leaf_const(-1);

        let is_all_ones = item.0.clone().bvsge(self.context.bv_from_i64(128, 128));
        let negated_bitmask = self.shl(all_ones.clone(), item);
        let shifted_result = self.not(negated_bitmask);

        Z3Expr(is_all_ones.ite_bv(all_ones.0, shifted_result.0))
    }

    fn trailing_zeros(&mut self, item: Self::T) -> Self::T {
        Z3Expr(self.context.count_trailing_zeros(item.0))
    }

    fn leading_zeros(&mut self, item: Self::T) -> Self::T {
        Z3Expr(self.context.count_leading_zeros(item.0))
    }

    fn swap_bytes(&mut self, num_bits: u8, item: Self::T) -> Self::T {
        Z3Expr(item.0.swap_bytes_to_128bits((num_bits as usize + 7) / 8))
    }

    fn mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(lhs.0 * rhs.0)
    }

    fn div(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let zero = self.context.bv_from_u64(0, 128);
        let is_zero = rhs.0.clone()._eq(zero.clone());
        Z3Expr(is_zero.ite_bv(zero, lhs.0.bvsdiv(rhs.0)))
    }

    fn div_unsigned(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let zero = self.context.bv_from_u64(0, 128);
        let is_zero = rhs.0.clone()._eq(zero.clone());
        Z3Expr(is_zero.ite_bv(zero, lhs.0.bvudiv(rhs.0)))
    }

    fn rem(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let zero = self.context.bv_from_u64(0, 128);
        let is_zero = rhs.0.clone()._eq(zero.clone());
        Z3Expr(is_zero.ite_bv(zero, lhs.0.bvsrem(rhs.0)))
    }

    fn rem_unsigned(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let zero = self.context.bv_from_u64(0, 128);
        let is_zero = rhs.0.clone()._eq(zero.clone());
        Z3Expr(is_zero.ite_bv(zero, lhs.0.bvurem(rhs.0)))
    }

    fn deposit_bits(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(self.context.deposit_bits::<128>(lhs.0, rhs.0))
    }

    fn extract_bits(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        Z3Expr(self.context.extract_bits::<128>(lhs.0, rhs.0))
    }

    fn popcount(&mut self, item: Self::T) -> Self::T {
        let n = self.context.popcount(&item.0, 128);
        Z3Expr(self.context.bv_from_int(n, 128))
    }

    fn carryless_mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T {
        let x = lhs.0;
        let y = rhs.0;

        let one_bv1 = self.context.bv_from_i64(1, 1);

        let zeros = self.context.bv_from_i64(0, 128);
        let ones = self.context.bv_from_i64(-1, 128);

        let mut result = self.context.bv_from_i64(0, 128);
        for i in 0..128 {
            let do_xor = x.clone().extract(i, i)._eq(one_bv1.clone());
            let xor_mask = do_xor.ite_bv(ones.clone(), zeros.clone());
            let xor_value = y.clone().bvshl(self.context.bv_from_i64(i as i64, 128));
            result = result ^ (xor_value & xor_mask);
        }

        Z3Expr(result)
    }
}
