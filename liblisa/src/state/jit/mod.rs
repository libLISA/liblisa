//! Efficient just-in-time generation of CPU states.
//!
//! Cloning and manipulating CPU states can be slow, especially if they do not fit in CPU cache.
//! Sometimes it is more efficient to generate a state on-the-fly by modifying an existing state, rather than cloning the state and keeping multiple copies in memory.
//! This module defines various ways to generate states just-in-time from a base state.

use crate::arch::Arch;
use crate::state::{AsSystemState, SystemState};

mod complex;
mod gpreg;
mod simple;

pub use complex::*;
pub use gpreg::*;
pub use simple::*;

/// A wrapper that implements [`AsSystemState`] and can either contain a [`SimpleJitState`], [`ComplexJitState`] or a normal [`SystemState`].
#[derive(Clone)]
pub enum MaybeJitState<'j, A: Arch> {
    /// Simple JIT state.
    SimpleJit(SimpleJitState<'j, A>),

    /// Complex JIT state.
    ComplexJit(ComplexJitState<'j, A>),

    /// Normal [`SystemState`].
    Normal(SystemState<A>),
}

impl<'j, A: Arch> std::fmt::Debug for MaybeJitState<'j, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.as_system_state().as_ref(), f)
    }
}

impl<'j, A: Arch> From<SystemState<A>> for MaybeJitState<'j, A> {
    fn from(value: SystemState<A>) -> Self {
        Self::Normal(value)
    }
}

impl<'j, A: Arch> From<SimpleJitState<'j, A>> for MaybeJitState<'j, A> {
    fn from(value: SimpleJitState<'j, A>) -> Self {
        Self::SimpleJit(value)
    }
}

impl<'j, A: Arch> From<ComplexJitState<'j, A>> for MaybeJitState<'j, A> {
    fn from(value: ComplexJitState<'j, A>) -> Self {
        Self::ComplexJit(value)
    }
}

impl<'j, A: Arch> AsSystemState<A> for MaybeJitState<'j, A> {
    type Output<'a> = MaybeRef<'a, A>
        where Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        match self {
            MaybeJitState::SimpleJit(jit) => MaybeRef::Ref(jit.as_system_state()),
            MaybeJitState::ComplexJit(jit) => MaybeRef::ComplexRef(jit.as_system_state()),
            MaybeJitState::Normal(state) => MaybeRef::Normal(state),
        }
    }

    fn num_memory_mappings(&self) -> usize {
        match self {
            MaybeJitState::SimpleJit(v) => v.num_memory_mappings(),
            MaybeJitState::ComplexJit(v) => v.num_memory_mappings(),
            MaybeJitState::Normal(v) => v.num_memory_mappings(),
        }
    }
}

impl<'j, A: Arch> AsSystemState<A> for &'_ MaybeJitState<'j, A> {
    type Output<'a> = MaybeRef<'a, A>
        where Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        match self {
            MaybeJitState::SimpleJit(jit) => MaybeRef::Ref(jit.as_system_state()),
            MaybeJitState::ComplexJit(jit) => MaybeRef::ComplexRef(jit.as_system_state()),
            MaybeJitState::Normal(state) => MaybeRef::Normal(state),
        }
    }

    fn num_memory_mappings(&self) -> usize {
        match self {
            MaybeJitState::SimpleJit(v) => v.num_memory_mappings(),
            MaybeJitState::ComplexJit(v) => v.num_memory_mappings(),
            MaybeJitState::Normal(v) => v.num_memory_mappings(),
        }
    }
}

/// A reference to a [`MaybeJitState`].
pub enum MaybeRef<'a, A: Arch> {
    /// Reference of [`MaybeJitState::SimpleJit`]
    Ref(SimpleStateRef<'a, A>),

    /// Reference of [`MaybeJitState::ComplexJit`]
    ComplexRef(ComplexStateRef<'a, A>),

    /// Reference of [`MaybeJitState::Normal`]
    Normal(&'a SystemState<A>),
}

impl<A: Arch> AsRef<SystemState<A>> for MaybeRef<'_, A> {
    fn as_ref(&self) -> &SystemState<A> {
        match self {
            MaybeRef::Ref(r) => r.as_ref(),
            MaybeRef::ComplexRef(r) => r.as_ref(),
            MaybeRef::Normal(v) => v,
        }
    }
}
