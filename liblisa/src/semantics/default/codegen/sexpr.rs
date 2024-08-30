//! S-expression code generator.

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use super::{CodeGenerator, Term};

/// An S-expression representation for the [`SExprCodeGen`] code generator.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum SExpr {
    /// A constant value.
    Const {
        /// A string representation of the constant.
        /// Is printed without any escaping.
        data: String,
    },

    /// An input
    Input {
        /// The index of the input.
        index: usize,
    },

    /// Applies an operation to the arguments.
    ///
    /// Generates a string of the form `"(op arg0 arg1 arg2 ...)"`
    App {
        /// The name of the operation.
        /// Is printed without any escaping.
        op: String,

        /// The arguments of the operation.
        args: Vec<SExpr>,
    },
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SExpr::Const {
                data,
            } => write!(f, "{data}"),
            SExpr::Input {
                index,
            } => write!(f, "arg{index}"),
            SExpr::App {
                op,
                args,
            } => write!(f, "({op} {})", args.iter().join(" ")),
        }
    }
}

/// A code generator that generates S-expressions.
pub struct SExprCodeGen;

impl SExprCodeGen {
    /// Creates a new [`SExprCodeGen`].
    pub fn new() -> Self {
        Self
    }

    fn f(name: &str, args: &[SExpr]) -> SExpr {
        SExpr::App {
            op: name.to_string(),
            args: args.to_vec(),
        }
    }
}

impl Default for SExprCodeGen {
    fn default() -> Self {
        SExprCodeGen
    }
}

impl CodeGenerator for SExprCodeGen {
    type T = SExpr;

    fn leaf_const(&mut self, value: i128) -> Self::T {
        SExpr::Const {
            data: format!("#x{:032X}", value as u128),
        }
    }

    fn leaf_arg(&mut self, arg_index: usize) -> Term<Self::T> {
        Term::simple(SExpr::Input {
            index: arg_index,
        })
    }

    fn unknown_op_any(&mut self, name: &str, args: &[Self::T]) -> Self::T {
        Self::f(name, args)
    }
}
