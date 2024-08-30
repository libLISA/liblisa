//! Defines tests for liblisa::compare.
//!
//! Normally, tests would be defined in liblisa itself.
//! However, for comparison an SMT solver is needed to run.
//! We cannot have liblisa depend on liblisa_z3, because liblisa_z3 itself also depends on liblisa.
//! Therefore, tests that require an SMT solver are defined here instead.

mod computations;
mod equivalence;
