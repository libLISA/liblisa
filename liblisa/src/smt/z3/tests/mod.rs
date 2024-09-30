//! Defines tests for liblisa::compare.
//!
//! Normally, tests would be defined in liblisa itself.
//! However, for comparison an SMT solver is needed to run.
//! We cannot have liblisa depend on liblisa_z3, because liblisa_z3 itself also depends on liblisa.
//! Therefore, tests that require an SMT solver are defined here instead.

mod computations;
mod equivalence;

use std::time::Duration;

use crate::smt::z3::Z3Solver;
use crate::smt::{SatResult, SmtBV, SmtBVArray, SmtSolver};

#[test]
pub fn array_store_select_equals() {
    Z3Solver::with_thread_local(Duration::from_secs(900), |mut context| {
        let arr = context.new_bv_array_const("mem", 64, 8);
        let arr = arr.store(context.bv_from_u64(15, 64), context.bv_from_u64(42, 8));

        let eq = !arr.select(context.bv_from_u64(15, 64))._eq(context.bv_from_u64(42, 8));

        assert!(matches!(context.check_assertions(&[eq]), SatResult::Unsat));
    });
}
