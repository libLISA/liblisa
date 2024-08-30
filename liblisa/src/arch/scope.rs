//! Defines [`Scope`], which can be used to specify which instructions should be enumerated.

use std::fmt::Debug;

use serde::{Deserialize, Serialize};

/// Defines an instruction scope for an architecture.
/// This can be used to limit which parts of the instruction space are enumerated.
pub trait Scope: Clone + Debug + Send + Sync {
    /// Returns true if and only if `instr` should be enumerated.
    fn is_instr_in_scope(&self, instr: &[u8]) -> bool;
}

/// A [`Scope`] that considers every instruction in-scope.
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub struct FullScope;

impl Scope for FullScope {
    fn is_instr_in_scope(&self, _instr: &[u8]) -> bool {
        true
    }
}
