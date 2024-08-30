//! Defines a default [`crate::semantics::Computation`] implementation called [`computation::SynthesizedComputation`].

use std::fmt::{Debug, Display, Write};
use std::ops::Index;

use arrayvec::ArrayVec;
use serde::{Deserialize, Serialize};

use self::ops::Op;

pub mod builder;
pub mod codegen;
pub mod computation;
pub mod ops;
pub mod smtgen;

/// The maximum number of holes in a single template.
pub const MAX_TEMPLATE_ARGS: usize = 4;

#[doc(hidden)]
#[derive(Copy, Clone)]
#[cfg(target_arch = "x86_64")]
#[allow(improper_ctypes_definitions)]
pub struct FastEval {
    pub eval: extern "sysv64" fn(&[i128]) -> i128,
    pub eval_indirect: extern "sysv64" fn(&[i128], &[u16]) -> i128,
    pub eval_indirect_u64: extern "sysv64" fn(&[i128], &[u16]) -> u64,
    pub eval_indirect_bool: extern "sysv64" fn(&[i128], &[u16]) -> bool,
}

#[doc(hidden)]
#[derive(Copy, Clone)]
#[cfg(not(target_arch = "x86_64"))]
#[allow(improper_ctypes_definitions)]
pub struct FastEval {
    pub eval: extern "C" fn(&[i128]) -> i128,
    pub eval_indirect: extern "C" fn(&[i128], &[u16]) -> i128,
    pub eval_indirect_u64: extern "C" fn(&[i128], &[u16]) -> u64,
    pub eval_indirect_bool: extern "C" fn(&[i128], &[u16]) -> bool,
}

/// An [`Expr`] that always returns 1.
#[allow(improper_ctypes_definitions)]
pub const TRUE: Expr = Expr {
    ops: &[Op::Const(1)],
    fast_eval: {
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x1(_: &[i128]) -> i128 {
            1
        }
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x2(_: &[i128], _: &[u16]) -> i128 {
            1
        }
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x3(_: &[i128], _: &[u16]) -> u64 {
            1
        }
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x4(_: &[i128], _: &[u16]) -> bool {
            true
        }

        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x1(_: &[i128]) -> i128 {
            1
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x2(_: &[i128], _: &[u16]) -> i128 {
            1
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x3(_: &[i128], _: &[u16]) -> u64 {
            1
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x4(_: &[i128], _: &[u16]) -> bool {
            true
        }

        Some(&FastEval {
            eval: x1,
            eval_indirect: x2,
            eval_indirect_u64: x3,
            eval_indirect_bool: x4,
        })
    },
};

/// An [`Expr`] that always returns 0.
#[allow(improper_ctypes_definitions)]
pub const FALSE: Expr = Expr {
    ops: &[Op::Const(0)],
    fast_eval: {
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x1(_: &[i128]) -> i128 {
            0
        }
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x2(_: &[i128], _: &[u16]) -> i128 {
            0
        }
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x3(_: &[i128], _: &[u16]) -> u64 {
            0
        }
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn x4(_: &[i128], _: &[u16]) -> bool {
            false
        }

        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x1(_: &[i128]) -> i128 {
            0
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x2(_: &[i128], _: &[u16]) -> i128 {
            0
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x3(_: &[i128], _: &[u16]) -> u64 {
            0
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn x4(_: &[i128], _: &[u16]) -> bool {
            false
        }

        Some(&FastEval {
            eval: x1,
            eval_indirect: x2,
            eval_indirect_u64: x3,
            eval_indirect_bool: x4,
        })
    },
};

/// The expression used in computations.
/// Non-owned version of [`Expression`].
#[derive(Copy, Clone)]
pub struct Expr<'a> {
    ops: &'a [Op],
    fast_eval: Option<&'a FastEval>,
}

impl PartialEq for Expr<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.ops == other.ops
    }
}

impl<'a> Default for Expr<'a> {
    fn default() -> Self {
        Expr::new(&[Op::Hole(0)])
    }
}

impl<'a> Default for &'static Expr<'a> {
    fn default() -> Self {
        const E: Expr = Expr::new(&[Op::Hole(0)]);
        &E
    }
}

impl<'a> Expr<'a> {
    /// A default expression, which is the identity function.
    pub const fn const_default() -> Self {
        Expr::new(&[Op::Hole(0)])
    }

    /// A reference to the default expression, which is the identity function.
    pub const fn const_default_ref() -> &'static Self {
        const E: Expr = Expr::new(&[Op::Hole(0)]);
        &E
    }
}

impl Debug for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr").field("ops", &self.ops).finish()
    }
}

impl<'a> From<&'a [Op]> for Expr<'a> {
    fn from(ops: &'a [Op]) -> Self {
        Self::new(ops)
    }
}

impl<'a, const N: usize> From<&'a [Op; N]> for Expr<'a> {
    fn from(ops: &'a [Op; N]) -> Self {
        Self::new(ops)
    }
}

impl<'a> Expr<'a> {
    /// Counts the number of [`Op::Hole`]s in the expression.
    pub const fn count_holes(&self) -> usize {
        let mut args_seen = [false; 4096];
        let mut index = 0;
        while index < self.ops.len() {
            if let Op::Hole(n) = self.ops[index] {
                args_seen[n as usize] = true;
            }

            index += 1;
        }

        let mut num_args = 0;
        while args_seen[num_args] {
            num_args += 1;
        }

        let mut index = num_args;
        while index < args_seen.len() {
            assert!(!args_seen[index], "Arguments are not consecutive");
            index += 1;
        }

        num_args
    }

    /// Creates a new expression from the provided operations.
    pub const fn new(ops: &'a [Op]) -> Self {
        Expr {
            ops,
            fast_eval: None,
        }
    }

    /// Casts the expression to an owned expression.
    pub fn to_owned(&self) -> Expression {
        Expression {
            ops: self.ops.to_vec(),
            fast_eval: self.fast_eval.copied(),
        }
    }

    /// Evaluates the expression using the given arguments.
    /// Returns the result of the computation as an `i128`.
    #[inline]
    pub fn evaluate(&self, args: &[i128]) -> i128 {
        if let Some(eval) = self.fast_eval {
            (eval.eval)(args)
        } else {
            self.evaluate_on_stack(args)
        }
    }

    fn evaluate_on_stack(&self, args: &[i128]) -> i128 {
        let mut stack = ArrayVec::<_, 1024>::new();
        let mut top_of_stack = 0;
        for item in self.ops.iter() {
            // println!("{item:?} on {top_of_stack:X?}, {stack:X?}");
            top_of_stack = item.eval_from_stack(&|n| args[n], top_of_stack, &mut stack);
            // println!("    == {top_of_stack:X?}");
        }

        top_of_stack
    }

    /// Evaluates the expression using the given arguments.
    /// Returns the result of the computation as an `i128`.
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    #[inline]
    pub fn evaluate_indirect(&self, all_args: &[i128], mapping: &[u16]) -> i128 {
        if let Some(eval) = self.fast_eval {
            (eval.eval_indirect)(all_args, mapping)
        } else {
            self.evaluate_indirect_on_stack(&|n| all_args[mapping[n] as usize])
        }
    }

    /// Evaluates the expression using the given arguments.
    /// The expression produces an `i128`, which is then cast to an `u64` and returned.
    ///
    /// This can be faster if the `fast_eval` field is set.
    /// This allows the compiler to eliminate `i128` computations all together in some cases.
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    #[inline]
    pub fn evaluate_indirect_as_u64(&self, all_args: &[i128], mapping: &[u16]) -> u64 {
        if let Some(eval) = self.fast_eval {
            (eval.eval_indirect_u64)(all_args, mapping)
        } else {
            self.evaluate_indirect_on_stack(&|n| all_args[mapping[n] as usize]) as u64
        }
    }

    /// Evaluates the expression using the given arguments.
    /// The expression produces an `i128`, which is then cast to a `bool` and returned.
    ///
    /// This can be faster if the `fast_eval` field is set.
    /// This allows the compiler to eliminate `i128` computations all together in some cases.
    ///
    /// Performs a lookup in `mapping` to figure out which index in `all_args` should be used for an argument.
    /// For an argument `N`, `all_args[mapping[N] as usize]` is used.
    #[inline]
    pub fn evaluate_indirect_as_bool(&self, all_args: &[i128], mapping: &[u16]) -> bool {
        if let Some(eval) = self.fast_eval {
            (eval.eval_indirect_bool)(all_args, mapping)
        } else {
            self.evaluate_indirect_on_stack(&|n| all_args[mapping[n] as usize]) as u64 & 1 != 0
        }
    }

    fn evaluate_indirect_on_stack(&self, arg: &impl Fn(usize) -> i128) -> i128 {
        let mut stack = ArrayVec::<_, 1024>::new();
        let mut top_of_stack = 0;
        for item in self.ops.iter() {
            // println!("{item:?} on {top_of_stack:X?}, {stack:X?}");
            top_of_stack = item.eval_from_stack(arg, top_of_stack, &mut stack);
            // println!("    == {top_of_stack:X?}");
        }

        top_of_stack
    }

    #[doc(hidden)]
    pub const fn with_fast_eval(&self, fast_eval: &'a FastEval) -> Self {
        Expr {
            ops: self.ops,
            fast_eval: Some(fast_eval),
        }
    }

    #[doc(hidden)]
    pub const fn without_fast_eval(&self) -> Self {
        Expr {
            ops: self.ops,
            fast_eval: None,
        }
    }

    /// Returns the operations in this expression
    pub fn ops(&self) -> &[Op] {
        self.ops
    }

    /// Returns a type that can be displayed as an expression.
    /// Fills in holes with the strings in `hole_names`.
    pub fn display<'r, S: AsRef<str> + 'r, C: Index<usize, Output = S> + 'r>(&self, hole_names: C) -> impl Display + Debug + 'r
    where
        'a: 'r,
    {
        DisplayExpr {
            expr: *self,
            hole_names,
        }
    }
}

/// An owned expression.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Serialize, Deserialize)]
pub struct Expression {
    ops: Vec<Op>,

    #[serde(skip)]
    fast_eval: Option<FastEval>,
}

impl Expression {
    /// Creates a new owned expression from the operations.
    pub fn new(ops: Vec<Op>) -> Self {
        Expression {
            fast_eval: None,
            ops,
        }
    }

    /// Returns the reference type [`Expr`] for this expression.
    pub fn as_expr(&self) -> Expr<'_> {
        Expr {
            ops: &self.ops,
            fast_eval: self.fast_eval.as_ref(),
        }
    }

    /// Pushes one additional operation to the end of the list of operations that this expression performs.
    pub fn push_op(&mut self, op: Op) {
        self.ops.push(op);
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.ops == other.ops
    }
}

impl Eq for Expression {}

impl std::hash::Hash for Expression {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ops.hash(state);
    }
}

impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expression")
            .field("ops", &self.ops)
            .field("fast_eval", &self.fast_eval.map(|_| ()))
            .finish()
    }
}

struct DisplayExpr<'a, S: AsRef<str>, C: Index<usize, Output = S>> {
    expr: Expr<'a>,
    hole_names: C,
}

impl<'a, S: AsRef<str>, C: Index<usize, Output = S>> Debug for DisplayExpr<'a, S, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl<S: AsRef<str>, C: Index<usize, Output = S>> Display for DisplayExpr<'_, S, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut stack = Vec::new();
        for op in self.expr.ops.iter() {
            let mut s = String::new();
            let needs_parens = match op {
                Op::Hole(n) => {
                    write!(&mut s, "{}", self.hole_names[*n as usize].as_ref())?;
                    false
                },
                other => {
                    if let Some(infix_op) = op.as_infix() {
                        for (index, (v, needs_parens)) in stack.drain(stack.len() - op.num_args()..).enumerate() {
                            if needs_parens {
                                write!(&mut s, "({v})")?;
                            } else {
                                write!(&mut s, "{v}")?;
                            }
                            if index < op.num_args() - 1 {
                                write!(&mut s, " {infix_op} ")?;
                            }
                        }

                        true
                    } else if op.num_args() == 0 {
                        write!(&mut s, "{other}")?;

                        false
                    } else {
                        write!(&mut s, "{other}(")?;

                        for (index, (v, _)) in stack.drain(stack.len() - op.num_args()..).enumerate() {
                            write!(&mut s, "{v}")?;
                            if index < op.num_args() - 1 {
                                write!(&mut s, ", ")?;
                            }
                        }

                        write!(&mut s, ")")?;

                        false
                    }
                },
            };

            stack.push((s, needs_parens));
        }

        write!(f, "{}", stack.pop().unwrap().0)
    }
}

#[doc(inline)]
pub use crate::__private_expr as expr;

/// A helper macro that defines an [`crate::semantics::default::Expr`].
#[doc(hidden)]
#[macro_export]
macro_rules! __private_expr {
    ($template:expr) => {{
        const OPS: $crate::semantics::default::builder::OpWriter = $template.ops();
        const NUM_HOLES: usize = $crate::semantics::default::Expr::new(OPS.as_slice()).count_holes();

        // We're not actually doing FFI, we just want the performance benfits of this calling convention
        #[allow(improper_ctypes_definitions)]
        #[doc = stringify!($template)]
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn fast_eval(args: &[i128]) -> i128 {
            if args.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {args:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            // SAFETY: We checked the argument count above
            const { $template }.compute(&|n| args[n])
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn fast_eval(args: &[i128]) -> i128 {
            if args.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {args:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            // SAFETY: We checked the argument count above
            const { $template }.compute(&|n| args[n])
        }

        // We're not actually doing FFI, we just want the performance benfits of this calling convention
        #[allow(improper_ctypes_definitions)]
        #[doc = stringify!($template)]
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn fast_eval_indirect(all_args: &[i128], mapping: &[u16]) -> i128 {
            if mapping.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {mapping:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            const { $template }.compute(&|n| all_args[mapping[n] as usize])
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn fast_eval_indirect(all_args: &[i128], mapping: &[u16]) -> i128 {
            if mapping.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {mapping:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            const { $template }.compute(&|n| all_args[mapping[n] as usize])
        }

        // We're not actually doing FFI, we just want the performance benfits of this calling convention
        #[allow(improper_ctypes_definitions)]
        #[doc = stringify!($template)]
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn fast_eval_indirect_u64(all_args: &[i128], mapping: &[u16]) -> u64 {
            if mapping.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {mapping:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            const { $template }.compute(&|n| all_args[mapping[n] as usize]) as u64
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn fast_eval_indirect_u64(all_args: &[i128], mapping: &[u16]) -> u64 {
            if mapping.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {mapping:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            const { $template }.compute(&|n| all_args[mapping[n] as usize]) as u64
        }

        // We're not actually doing FFI, we just want the performance benfits of this calling convention
        #[allow(improper_ctypes_definitions)]
        #[doc = stringify!($template)]
        #[cfg(target_arch = "x86_64")]
        extern "sysv64" fn fast_eval_indirect_bool(all_args: &[i128], mapping: &[u16]) -> bool {
            if mapping.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {mapping:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            const { $template }.compute(&|n| all_args[mapping[n] as usize]) as u64 & 1 != 0
        }
        #[cfg(not(target_arch = "x86_64"))]
        extern "C" fn fast_eval_indirect_bool(all_args: &[i128], mapping: &[u16]) -> bool {
            if mapping.len() < NUM_HOLES {
                panic!(
                    "Not enough arguments provided for {}: Got {mapping:X?}, but need {NUM_HOLES}",
                    stringify!($template)
                );
            }

            const { $template }.compute(&|n| all_args[mapping[n] as usize]) as u64 & 1 != 0
        }

        const {
            $crate::semantics::default::Expr::new(OPS.as_slice()).with_fast_eval(&$crate::semantics::default::FastEval {
                eval: fast_eval,
                eval_indirect: fast_eval_indirect,
                eval_indirect_u64: fast_eval_indirect_u64,
                eval_indirect_bool: fast_eval_indirect_bool,
            })
        }
    }};
}

#[cfg(test)]
mod tests {
    use crate::semantics::default::ops::Op;
    use crate::semantics::default::Expr;

    #[test]
    pub fn bit_set() {
        // expr!(or(hole::<0>(), shl(hole::<2>(), hole::<1>().crop::<3>())))
        let expr = Expr::new(&[
            Op::Hole(0),
            Op::Hole(2),
            Op::Hole(1),
            Op::Crop {
                num_bits: 3,
            },
            Op::Shl,
            Op::Or,
        ]);

        assert_eq!(expr.evaluate(&[0x123450, 3, 1]), 0x123458);
        assert_eq!(expr.evaluate(&[0xFFFD5744FE9EAB63, 0x3FFE16F32426, 1]), 0xFFFD5744FE9EAB63);
    }

    #[test]
    pub fn arg_order_cmplt() {
        // expr!(less_than(hole::<0>(), hole::<1>()))
        let expr = Expr::new(&[Op::Hole(0), Op::Hole(1), Op::CmpLt]);

        assert_eq!(expr.evaluate(&[10, 4]), 0);
        assert_eq!(expr.evaluate(&[4, 10]), 1);

        println!("{}", expr.display(["A", "B"]));
    }
}
