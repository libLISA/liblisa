//! This module contains glue code that implements `liblisa::smt::SmtSolver`.
//! To use this module, the feature `z3` needs to be enabled.

#[cfg(test)]
mod tests;

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not, Sub};
use std::time::Duration;

use z3::ast::{forall_const, Ast};
use z3::{Config, Context, Params, Solver};

use crate::smt::{Dynamic, SatResult, SmtBV, SmtBool, SmtInt, SmtModel, SmtModelRef, SmtSolver, SolverProvider};

/// A [`SolverProvider`] that uses a thread-local Z3 instance.
pub struct ThreadLocalZ3 {
    timeout: Duration,
}

impl ThreadLocalZ3 {
    /// Creates a new Z3 instance with the solver timeout set to `timeout`.
    pub fn new(timeout: Duration) -> Self {
        Self {
            timeout,
        }
    }
}

impl SolverProvider for ThreadLocalZ3 {
    type Solver<'a> = Z3Solver<'a>;

    fn with_solver<T>(&self, f: impl FnOnce(Self::Solver<'_>) -> T) -> T {
        Z3Solver::with_thread_local(self.timeout, f)
    }
}

/// The Z3 [`SmtSolver`].
#[derive(Clone, Debug)]
pub struct Z3Solver<'ctx> {
    context: &'ctx Context,
    solver: z3::Solver<'ctx>,
}

thread_local! {
    static CONTEXTS: RefCell<HashMap<u64, Context>> = RefCell::new(HashMap::new());
}

impl<'ctx> Z3Solver<'ctx> {
    /// Creates a new [`Z3Solver`] from the provided context.
    pub fn new(context: &'ctx Context) -> Self {
        let mut params = Params::new(context);
        params.set_bool("ctrl_c", false);

        let solver = Solver::new(context);
        solver.set_params(&params);

        Self {
            context,
            solver,
        }
    }
}

impl Z3Solver<'static> {
    /// Creates a new thread-local [`Z3Solver`].
    pub fn with_thread_local<T>(timeout: Duration, f: impl FnOnce(Z3Solver<'_>) -> T) -> T {
        let timeout = u64::try_from(timeout.as_millis()).unwrap();
        CONTEXTS.with(|contexts| {
            f(Z3Solver::new(contexts.borrow_mut().entry(timeout).or_insert_with_key(
                |&timeout| {
                    let mut config = Config::new();
                    config.set_timeout_msec(timeout);
                    Context::new(&config)
                },
            )))
        })
    }
}

impl<'ctx> SmtSolver<'ctx> for Z3Solver<'ctx> {
    type BV = BV<'ctx>;
    type Int = Int<'ctx>;
    type Bool = Bool<'ctx>;
    type ModelRef<'a>
        = ModelRef<'a, 'ctx>
    where
        Self: 'a;
    type Model = Model<'ctx>;

    fn bv_from_i64(&mut self, val: i64, size: u32) -> Self::BV {
        BV(z3::ast::BV::from_i64(self.context, val, size))
    }

    fn bv_from_u64(&mut self, val: u64, size: u32) -> Self::BV {
        BV(z3::ast::BV::from_u64(self.context, val, size))
    }

    fn int_from_i64(&mut self, val: i64) -> Self::Int {
        Int(z3::ast::Int::from_i64(self.context, val))
    }

    fn int_from_bv(&mut self, bv: Self::BV, signed: bool) -> Self::Int {
        Int(z3::ast::Int::from_bv(&bv.0, signed))
    }

    fn bv_from_int(&mut self, int: Self::Int, size: u32) -> Self::BV {
        BV(z3::ast::BV::from_int(&int.0, size))
    }

    fn new_bv_const(&mut self, name: impl AsRef<str>, size: u32) -> Self::BV {
        BV(z3::ast::BV::new_const(self.context, name.as_ref(), size))
    }

    fn check_assertions(&mut self, assertions: &[Self::Bool]) -> SatResult<Self::ModelRef<'_>> {
        self.solver.reset();

        for assertion in assertions {
            self.solver.assert(&assertion.0);
        }

        match self.solver.check() {
            z3::SatResult::Unsat => SatResult::Unsat,
            z3::SatResult::Unknown => SatResult::Unknown,
            z3::SatResult::Sat => SatResult::Sat(ModelRef(&self.solver)),
        }
    }

    fn bool_from_bool(&mut self, val: bool) -> Self::Bool {
        Bool(z3::ast::Bool::from_bool(self.context, val))
    }

    fn int_from_u64(&mut self, val: u64) -> Self::Int {
        Int(z3::ast::Int::from_u64(self.context, val))
    }

    fn forall_const(&mut self, vals: &[Dynamic<'ctx, Self>], condition: Self::Bool) -> Self::Bool {
        let bounds = vals
            .iter()
            .map(|v| match v {
                Dynamic::BV(v) => &v.0 as &dyn Ast,
                Dynamic::Int(v) => &v.0 as &dyn Ast,
                Dynamic::Bool(v) => &v.0 as &dyn Ast,
            })
            .collect::<Vec<_>>();
        Bool(forall_const(self.context, &bounds, &[], &condition.0))
    }

    fn new_bool_const(&mut self, name: impl AsRef<str>) -> Self::Bool {
        Bool(z3::ast::Bool::new_const(self.context, name.as_ref()))
    }
}

/// The Z3 model returned when assertions are satisfiable.
pub struct Model<'ctx>(z3::Model<'ctx>);

impl<'ctx> SmtModel<'ctx, Z3Solver<'ctx>> for Model<'ctx> {
    fn get_const_interp(&self, name: &BV<'ctx>) -> Option<BV<'ctx>> {
        self.0.get_const_interp(&name.0).map(BV)
    }
}

impl Debug for Model<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

/// A reference to the Z3 model returned when assertions are satisfiable.
pub struct ModelRef<'a, 'ctx>(&'a Solver<'ctx>);

impl<'ctx> SmtModelRef<'ctx, Z3Solver<'ctx>> for ModelRef<'_, 'ctx> {
    fn to_model(&self) -> Option<Model<'ctx>> {
        self.0.get_model().map(Model)
    }
}

impl Debug for ModelRef<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0.get_model(), f)
    }
}

/// A Z3 bitvector.
#[derive(Clone, Debug)]
pub struct BV<'ctx>(z3::ast::BV<'ctx>);

impl<'ctx> Display for BV<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<'ctx> SmtBV<'ctx, Z3Solver<'ctx>> for BV<'ctx> {
    fn concat(self, other: Self) -> Self {
        BV(self.0.concat(&other.0))
    }

    fn extract(self, hi: u32, lo: u32) -> Self {
        BV(self.0.extract(hi, lo))
    }

    fn zero_ext(self, num: u32) -> Self {
        BV(self.0.zero_ext(num))
    }

    fn sign_ext(self, num: u32) -> Self {
        BV(self.0.sign_ext(num))
    }

    fn bvshl(self, count: Self) -> Self {
        BV(self.0.bvshl(&count.0))
    }

    fn bvlshr(self, count: Self) -> Self {
        BV(self.0.bvlshr(&count.0))
    }

    fn bvashr(self, count: Self) -> Self {
        BV(self.0.bvashr(&count.0))
    }

    fn get_size(&self) -> u32 {
        self.0.get_size()
    }

    fn _eq(self, other: Self) -> Bool<'ctx> {
        Bool(self.0._eq(&other.0))
    }

    fn bvurem(self, n: Self) -> Self {
        BV(self.0.bvurem(&n.0))
    }

    fn bvsrem(self, n: Self) -> Self {
        BV(self.0.bvsrem(&n.0))
    }

    fn bvudiv(self, n: Self) -> Self {
        BV(self.0.bvudiv(&n.0))
    }

    fn bvsdiv(self, n: Self) -> Self {
        BV(self.0.bvsdiv(&n.0))
    }

    fn bvrotl(self, count: Self) -> Self {
        BV(self.0.bvrotl(&count.0))
    }

    fn bvslt(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvslt(&other.0))
    }

    fn bvsge(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvsge(&other.0))
    }

    fn simplify(self) -> Self {
        BV(self.0.simplify())
    }

    fn bvrotr(self, count: Self) -> Self {
        BV(self.0.bvrotr(&count.0))
    }

    fn is_identical(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }

    fn bvsgt(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvsgt(&other.0))
    }

    fn bvugt(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvugt(&other.0))
    }

    fn bvult(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvult(&other.0))
    }

    fn bvule(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvule(&other.0))
    }

    fn bvuge(self, other: Self) -> Bool<'ctx> {
        Bool(self.0.bvuge(&other.0))
    }

    fn as_u64(&self) -> Option<u64> {
        self.0.as_u64()
    }
}

impl<'ctx> Add for BV<'ctx> {
    type Output = BV<'ctx>;

    fn add(self, rhs: Self) -> Self::Output {
        BV(self.0.bvadd(&rhs.0))
    }
}

impl<'ctx> Sub for BV<'ctx> {
    type Output = BV<'ctx>;

    fn sub(self, rhs: Self) -> Self::Output {
        BV(self.0.bvsub(&rhs.0))
    }
}

impl<'ctx> Mul for BV<'ctx> {
    type Output = BV<'ctx>;

    fn mul(self, rhs: Self) -> Self::Output {
        BV(self.0.bvmul(&rhs.0))
    }
}

impl<'ctx> BitOr for BV<'ctx> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        BV(self.0.bvor(&rhs.0))
    }
}

impl<'ctx> BitAnd for BV<'ctx> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        BV(self.0.bvand(&rhs.0))
    }
}

impl<'ctx> BitXor for BV<'ctx> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        BV(self.0.bvxor(&rhs.0))
    }
}

impl<'ctx> Not for BV<'ctx> {
    type Output = Self;

    fn not(self) -> Self::Output {
        BV(self.0.not())
    }
}

/// A Z3 Int.
#[derive(Clone, Debug)]
pub struct Int<'ctx>(z3::ast::Int<'ctx>);

impl<'ctx> Display for Int<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<'ctx> SmtInt<'ctx, Z3Solver<'ctx>> for Int<'ctx> {
    fn simplify(self) -> Self {
        Int(self.0.simplify())
    }

    fn as_u64(&self) -> Option<u64> {
        self.0.as_u64()
    }

    fn _eq(self, other: Self) -> Bool<'ctx> {
        Bool(self.0._eq(&other.0))
    }

    fn is_identical(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

impl<'ctx> Add for Int<'ctx> {
    type Output = Int<'ctx>;

    fn add(self, rhs: Self) -> Self::Output {
        Int(self.0 + rhs.0)
    }
}

impl<'ctx> Sub for Int<'ctx> {
    type Output = Int<'ctx>;

    fn sub(self, rhs: Self) -> Self::Output {
        Int(self.0 - rhs.0)
    }
}

impl<'ctx> Mul for Int<'ctx> {
    type Output = Int<'ctx>;

    fn mul(self, rhs: Self) -> Self::Output {
        Int(self.0 * rhs.0)
    }
}

/// A Z3 Bool.
#[derive(Clone, Debug)]
pub struct Bool<'ctx>(z3::ast::Bool<'ctx>);

impl<'ctx> Display for Bool<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<'ctx> SmtBool<'ctx, Z3Solver<'ctx>> for Bool<'ctx> {
    fn ite_bv(self, lhs: BV<'ctx>, rhs: BV<'ctx>) -> BV<'ctx> {
        BV(self.0.ite(&lhs.0, &rhs.0))
    }

    fn simplify(self) -> Self {
        Bool(self.0.simplify())
    }

    fn _eq(self, other: Self) -> Bool<'ctx> {
        Bool(self.0._eq(&other.0))
    }

    fn as_bool(&self) -> Option<bool> {
        self.0.as_bool()
    }

    fn ite_int(self, lhs: Int<'ctx>, rhs: Int<'ctx>) -> Int<'ctx> {
        Int(self.0.ite(&lhs.0, &rhs.0))
    }

    fn ite_bool(self, lhs: Bool<'ctx>, rhs: Bool<'ctx>) -> Bool<'ctx> {
        Bool(self.0.ite(&lhs.0, &rhs.0))
    }

    fn is_identical(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

impl<'ctx> BitOr for Bool<'ctx> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Bool(self.0 | rhs.0)
    }
}

impl<'ctx> BitAnd for Bool<'ctx> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Bool(self.0 & rhs.0)
    }
}

impl<'ctx> BitXor for Bool<'ctx> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Bool(self.0 ^ rhs.0)
    }
}

impl<'ctx> Not for Bool<'ctx> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Bool(self.0.not())
    }
}
