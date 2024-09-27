use std::fmt::{Debug, Display};
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not, Sub};

/// The result of running a SAT solver on a set of assertions.
#[derive(Debug)]
pub enum SatResult<M> {
    /// The SAT solver timed out.
    Unknown,

    /// A model satisfying all assertions was found.
    Sat(M),

    /// It is not possible to satisfy all assertions.
    Unsat,
}

/// Provides [`SmtSolver`]s without having to know all of the configuration details of the individual solvers.
pub trait SolverProvider: Send + Sync {
    /// The solver that this type provides.
    type Solver<'a>: SmtSolver<'a>;

    /// Runs the function `f` with a provided solver.
    fn with_solver<T>(&self, f: impl FnOnce(Self::Solver<'_>) -> T) -> T;
}

/// An SMT solver.
pub trait SmtSolver<'a>: Sized + Debug {
    /// Bitvector expressions
    type BV: SmtBV<'a, Self>;

    /// Integer expressions
    type Int: SmtInt<'a, Self>;

    /// Boolean expressions
    type Bool: SmtBool<'a, Self>;

    /// References to models for satisfied assertions.
    type ModelRef<'r>: SmtModelRef<'a, Self>
    where
        Self: 'r;

    /// Models for satisfied assertions.
    type Model: SmtModel<'a, Self>;

    /// Creates a bitvector from an i64.
    fn bv_from_i64(&mut self, val: i64, size: u32) -> Self::BV;

    /// Creates a bitvector from an u64.
    fn bv_from_u64(&mut self, val: u64, size: u32) -> Self::BV;

    /// Creates a bitvector from an Int.
    fn bv_from_int(&mut self, int: Self::Int, size: u32) -> Self::BV;

    /// Declares a new bitvector constant.
    fn new_bv_const(&mut self, name: impl AsRef<str>, size: u32) -> Self::BV;

    /// Declares a new boolean constant.
    fn new_bool_const(&mut self, name: impl AsRef<str>) -> Self::Bool;

    /// Creates an int from an i64.
    fn int_from_i64(&mut self, val: i64) -> Self::Int;

    /// Creates an int from an u64.
    fn int_from_u64(&mut self, val: u64) -> Self::Int;

    /// Creates an int from a bitvector.
    fn int_from_bv(&mut self, bv: Self::BV, signed: bool) -> Self::Int;

    /// Creates an SMT bool from a Rust bool.
    fn bool_from_bool(&mut self, val: bool) -> Self::Bool;

    /// Creates a forall condition.
    fn forall_const(&mut self, vals: &[Dynamic<'a, Self>], condition: Self::Bool) -> Self::Bool;

    /// Runs the SMT solver on the provided assertions.
    fn check_assertions<'me>(&'me mut self, assertions: &[Self::Bool]) -> SatResult<Self::ModelRef<'me>>;

    /// Creates a bitvector from an i128.
    fn bv_from_i128(&mut self, value: i128) -> Self::BV {
        if let Ok(value) = i64::try_from(value) {
            self.bv_from_i64(value, 128)
        } else {
            let value = value as u128;
            let lower = self.bv_from_u64(value as u64, 64);
            let higher = self.bv_from_u64((value >> 64) as u64, 64);
            higher.concat(lower)
        }
    }

    /// The PEXT operation.
    fn extract_bits<const N: u32>(&mut self, src: Self::BV, mask: Self::BV) -> Self::BV {
        let mut dest = self.bv_from_i64(0, N);

        for n in 0..N {
            let mask_bit = mask.clone().extract(n, n);
            let bit = src.clone().extract(n, n);

            let index = if n > 0 {
                self.popcount(&mask, n)
            } else {
                self.int_from_i64(0)
            };

            dest = dest | (bit & mask_bit).zero_ext(N - 1).bvshl(self.bv_from_int(index, N));
        }
        dest
    }

    /// Counts the number of ones in `bv`.
    fn popcount(&mut self, bv: &Self::BV, bv_size: u32) -> Self::Int {
        let values = (0..bv_size)
            .map(|n| bv.clone().extract(n, n))
            .map(|bit| self.int_from_bv(bit, false))
            .collect::<Vec<_>>();
        values.into_iter().reduce(|a, b| a + b).unwrap()
    }

    /// The PDEP operation.
    fn deposit_bits<const N: u32>(&mut self, src: Self::BV, mask: Self::BV) -> Self::BV {
        let mut dest = None;

        for n in 0..N {
            let mask_bit = mask.clone().extract(n, n);
            let num = if n > 0 {
                self.popcount(&mask, n)
            } else {
                self.int_from_i64(0)
            };
            let bit = src.clone().bvlshr(self.bv_from_int(num, N)).extract(0, 0);

            let bit = mask_bit & bit;

            dest = Some(match dest.take() {
                Some(dest) => bit.concat(dest),
                None => bit,
            });
        }

        dest.unwrap()
    }

    /// Count the number of trailing zeros in `bv`.
    fn count_trailing_zeros(&mut self, bv: Self::BV) -> Self::BV {
        let mut result = self.bv_from_u64(0, 128);
        for size in 1..=bv.get_size() {
            let zero = self.bv_from_u64(0, size);
            result = bv
                .clone()
                .extract(size - 1, 0)
                ._eq(zero)
                .ite_bv(self.bv_from_u64(size as u64, 128), result);
        }
        result
    }

    /// Count the number of leading zeros in `bv`.
    fn count_leading_zeros(&mut self, bv: Self::BV) -> Self::BV {
        let max = bv.get_size();
        let mut result = self.bv_from_u64(0, 128);
        for size in 1..=max {
            let zero = self.bv_from_u64(0, size);
            result = bv
                .clone()
                .extract(max - 1, max - size)
                ._eq(zero)
                .ite_bv(self.bv_from_u64(size as u64, 128), result);
        }
        result
    }
}

/// Model for satisfied assertions.
pub trait SmtModel<'ctx, S: SmtSolver<'ctx>>: Debug {
    /// Obtain the value for a constant in the model.
    fn get_const_interp(&self, name: &S::BV) -> Option<S::BV>;
}

/// Reference to [`SmtModel`].
pub trait SmtModelRef<'ctx, S: SmtSolver<'ctx>>: Debug {
    /// Convert the reference into an owned model.
    fn to_model(&self) -> Option<S::Model>;
}

/// BitVector expressions in the SMT solver.
///
/// Most operation names correspond directly to the SMT functions and are not documented here.
#[allow(missing_docs)]
pub trait SmtBV<'a, S: SmtSolver<'a, BV = Self>>:
    Clone
    + Debug
    + Display
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + BitOr<Output = Self>
    + BitAnd<Output = Self>
    + BitXor<Output = Self>
    + Not<Output = Self>
    + Sized
{
    /// Returns true if both expressions are structurally identical.
    fn is_identical(&self, other: &Self) -> bool;
    fn concat(self, other: Self) -> Self;
    fn extract(self, hi: u32, lo: u32) -> Self;
    fn zero_ext(self, num: u32) -> Self;
    fn sign_ext(self, num: u32) -> Self;
    fn bvshl(self, count: Self) -> Self;
    fn bvlshr(self, count: Self) -> Self;
    fn bvashr(self, count: Self) -> Self;
    fn bvurem(self, n: Self) -> Self;
    fn bvsrem(self, n: Self) -> Self;
    fn bvudiv(self, n: Self) -> Self;
    fn bvsdiv(self, n: Self) -> Self;
    fn bvrotl(self, count: Self) -> Self;
    fn bvrotr(self, count: Self) -> Self;

    fn bvslt(self, other: Self) -> S::Bool;
    fn bvsge(self, other: Self) -> S::Bool;
    fn bvsgt(self, other: Self) -> S::Bool;
    fn bvugt(self, other: Self) -> S::Bool;
    fn bvult(self, other: Self) -> S::Bool;
    fn bvule(self, other: Self) -> S::Bool;
    fn bvuge(self, other: Self) -> S::Bool;

    /// Returns an SMT expression that performs an equality comparison between the two bitvectors.
    fn _eq(self, other: Self) -> S::Bool;

    /// Simplifies, if possible, the SMT expression.
    fn simplify(self) -> Self;

    /// Returns the size of the bitvector.
    fn get_size(&self) -> u32;

    /// Converts the bitvector to an `u64`, if possible.
    fn as_u64(&self) -> Option<u64>;

    /// Converts the bitvector into a [`Dynamic`] expression.
    fn into_dynamic(self) -> Dynamic<'a, S> {
        Dynamic::BV(self)
    }

    /// Swaps the lowest `num_bytes` in the bitvector.
    fn swap_bytes(self, num_bytes: usize) -> Self {
        (0..num_bytes as u32)
            .map(|index| self.clone().extract(index * 8 + 7, index * 8))
            .rev()
            .reduce(|acc, el| el.concat(acc))
            .unwrap()
    }

    /// Swaps the lowest `num_bytes` in the bitvector, and zero-extends to an 128-bit bitvector.
    fn swap_bytes_to_128bits(self, num_bytes: usize) -> Self {
        self.swap_bytes(num_bytes).zero_ext(128 - num_bytes as u32 * 8)
    }
}

/// Integer expressions in the SMT solver.
pub trait SmtInt<'a, S: SmtSolver<'a, Int = Self>>:
    Clone + Debug + Display + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Sized
{
    /// Returns true if both expressions are structurally identical.
    fn is_identical(&self, other: &Self) -> bool;

    /// Returns an SMT expression that performs an equality comparison between the two ints.
    fn _eq(self, other: Self) -> S::Bool;

    /// Simplifies, if possible, the SMT expression.
    fn simplify(self) -> Self;

    /// Converts the integer to an `u64`, if possible.
    fn as_u64(&self) -> Option<u64>;

    /// Converts the integer into a [`Dynamic`] expression.
    fn into_dynamic(self) -> Dynamic<'a, S> {
        Dynamic::Int(self)
    }
}

/// Boolean expressions in the SMT solver.
pub trait SmtBool<'a, S: SmtSolver<'a, Bool = Self>>:
    Clone + Debug + Display + BitOr<Output = Self> + BitAnd<Output = Self> + BitXor<Output = Self> + Not<Output = Self>
{
    /// Returns true if both expressions are structurally identical.
    fn is_identical(&self, other: &Self) -> bool;

    /// Returns an SMT expression that performs an equality comparison between the two bools.
    fn _eq(self, other: Self) -> S::Bool;

    /// Simplifies, if possible, the SMT expression.
    fn simplify(self) -> Self;

    /// Creates an If-Then-Else expression that returns bitvectors.
    ///
    /// `lhs` is returned if the boolean value is true, `rhs` if it is false.
    fn ite_bv(self, lhs: S::BV, rhs: S::BV) -> S::BV;

    /// Creates an If-Then-Else expression that returns integers.
    ///
    /// `lhs` is returned if the boolean value is true, `rhs` if it is false.
    fn ite_int(self, lhs: S::Int, rhs: S::Int) -> S::Int;

    /// Creates an If-Then-Else expression that returns booleans.
    ///
    /// `lhs` is returned if the boolean value is true, `rhs` if it is false.
    fn ite_bool(self, lhs: S::Bool, rhs: S::Bool) -> S::Bool;

    /// Creates an If-Then-Else expression that returns [`Dynamic`]s.
    ///
    /// `lhs` is returned if the boolean value is true, `rhs` if it is false.
    fn ite_dynamic(self, lhs: Dynamic<'a, S>, rhs: Dynamic<'a, S>) -> Dynamic<'a, S> {
        match (lhs, rhs) {
            (Dynamic::BV(a), Dynamic::BV(b)) => self.ite_bv(a, b).into_dynamic(),
            (Dynamic::Int(a), Dynamic::Int(b)) => self.ite_int(a, b).into_dynamic(),
            (Dynamic::Bool(a), Dynamic::Bool(b)) => self.ite_bool(a, b).into_dynamic(),
            (a, b) => panic!("ITE branches must have same sort: {a:?} vs {b:?}"),
        }
    }

    /// Converts the SMT boolean expression to a `bool`, if possible.
    fn as_bool(&self) -> Option<bool>;

    /// Converts the bool into a [`Dynamic`] expression.
    fn into_dynamic(self) -> Dynamic<'a, S> {
        Dynamic::Bool(self)
    }
}

/// An expression that is dynamically typed.
pub enum Dynamic<'a, S: SmtSolver<'a>> {
    /// A bitvector.
    BV(S::BV),

    /// An integer.
    Int(S::Int),

    /// A boolean.
    Bool(S::Bool),
}

impl<'a, S: SmtSolver<'a>> Debug for Dynamic<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BV(arg0) => f.debug_tuple("BV").field(arg0).finish(),
            Self::Int(arg0) => f.debug_tuple("Int").field(arg0).finish(),
            Self::Bool(arg0) => f.debug_tuple("Bool").field(arg0).finish(),
        }
    }
}

impl<'a, S: SmtSolver<'a>> Clone for Dynamic<'a, S> {
    fn clone(&self) -> Self {
        match self {
            Self::BV(arg0) => Self::BV(arg0.clone()),
            Self::Int(arg0) => Self::Int(arg0.clone()),
            Self::Bool(arg0) => Self::Bool(arg0.clone()),
        }
    }
}

/// The sort kind of an expression.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SortKind {
    /// A bitvector of any size.
    BV,

    /// An integer.
    Int,

    /// A boolean
    Bool,
}

/// The sort of an expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sort {
    /// A bitvector of the specified size (in bits)
    BV(u32),

    /// An integer
    Int,

    /// A boolean
    Bool,
}

impl<'a, S: SmtSolver<'a>> Dynamic<'a, S> {
    /// Creates a dynamically typed SMT expression from a boolean.
    pub fn from_bv(bv: S::BV) -> Self {
        Self::BV(bv)
    }

    /// If the expression is a bitvector, returns the bitvector.
    /// Otherwise, returns `None`.
    pub fn as_bv(self) -> Option<S::BV> {
        if let Dynamic::BV(bv) = self {
            Some(bv)
        } else {
            None
        }
    }

    /// If the expression is an integer, returns the integer.
    /// Otherwise, returns `None`.
    pub fn as_int(self) -> Option<S::Int> {
        if let Dynamic::Int(int) = self {
            Some(int)
        } else {
            None
        }
    }

    /// If the expression is a bool, returns the bool.
    /// Otherwise, returns `None`.
    pub fn as_bool(self) -> Option<S::Bool> {
        if let Dynamic::Bool(b) = self {
            Some(b)
        } else {
            None
        }
    }

    /// Returns the sort kind of the expression.
    pub fn sort_kind(&self) -> SortKind {
        match self {
            Dynamic::BV(_) => SortKind::BV,
            Dynamic::Int(_) => SortKind::Int,
            Dynamic::Bool(_) => SortKind::Bool,
        }
    }

    /// Returns the sort of the expression.
    pub fn sort(&self) -> Sort {
        match self {
            Dynamic::BV(bv) => Sort::BV(bv.get_size()),
            Dynamic::Int(_) => Sort::Int,
            Dynamic::Bool(_) => Sort::Bool,
        }
    }

    /// Simplifies, if possible, the SMT expression.
    pub fn simplify(self) -> Self {
        match self {
            Dynamic::BV(v) => Dynamic::BV(v.simplify()),
            Dynamic::Int(v) => Dynamic::Int(v.simplify()),
            Dynamic::Bool(v) => Dynamic::Bool(v.simplify()),
        }
    }

    /// Returns true if both expressions are structurally identical.
    ///
    /// Panics if the expressions are not of the same type.
    pub fn is_identical(&self, other: &Self) -> bool {
        match (self, other) {
            (Dynamic::BV(v), Dynamic::BV(w)) => v.is_identical(w),
            (Dynamic::Int(v), Dynamic::Int(w)) => v.is_identical(w),
            (Dynamic::Bool(v), Dynamic::Bool(w)) => v.is_identical(w),
            (v, w) => panic!("Cannot compare {v:?} with {w:?}"),
        }
    }

    /// Returns an SMT expression that performs an equality comparison between the two expressions.
    ///
    /// Panics if the expressions are not of the same type.
    pub fn _eq(self, other: Self) -> S::Bool {
        match (self, other) {
            (Dynamic::BV(v), Dynamic::BV(w)) => v._eq(w),
            (Dynamic::Int(v), Dynamic::Int(w)) => v._eq(w),
            (Dynamic::Bool(v), Dynamic::Bool(w)) => v._eq(w),
            (v, w) => panic!("Cannot compare {v:?} with {w:?}"),
        }
    }
}
