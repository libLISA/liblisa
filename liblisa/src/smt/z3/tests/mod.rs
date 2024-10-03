//! Defines tests for liblisa::compare.
//!
//! Normally, tests would be defined in liblisa itself.
//! However, for comparison an SMT solver is needed to run.
//! We cannot have liblisa depend on liblisa_z3, because liblisa_z3 itself also depends on liblisa.
//! Therefore, tests that require an SMT solver are defined here instead.

mod computations;
mod equivalence;

use std::time::Duration;

use crate::arch::x64::{GpReg, X64Arch, X64Reg};
use crate::encoding::dataflows::Size;
use crate::semantics::default::smtgen::{FilledLocation, Sizes, StorageLocations};
use crate::smt::z3::Z3Solver;
use crate::smt::{SatResult, SmtBV, SmtBVArray, SmtSolver};
use crate::state::Location;

#[test]
pub fn array_store_select_equals() {
    Z3Solver::with_thread_local(Duration::from_secs(900), |mut context| {
        let arr = context.new_bv_array_const("mem", 64, 8);
        let arr = arr.store(context.bv_from_u64(15, 64), context.bv_from_u64(42, 8));

        let eq = !arr.select(context.bv_from_u64(15, 64))._eq(context.bv_from_u64(42, 8));

        assert!(matches!(context.check_assertions(&[eq]), SatResult::Unsat));
    });
}

#[test]
pub fn zero_register_is_zero() {
    // Verify that the value of a zero register returned by StorageLocations is, in fact, always zero.
    Z3Solver::with_thread_local(Duration::from_secs(900), |mut context| {
        let mut s = StorageLocations::<X64Arch, _>::new(&mut context);
        let key = FilledLocation::Concrete(Location::Reg(X64Reg::GpReg(GpReg::Riz)));
        
        // StorageLocations::get
        let riz = s.get(&mut context, key, &Sizes::default());
        let eq = !riz._eq(context.bv_from_u64(0, 64));
        assert!(matches!(context.check_assertions(&[eq]), SatResult::Unsat));

        // StorageLocations::get_sized
        let riz = s.get_sized(&mut context, key, &Sizes::default(), Size::qword(), false);
        let eq = !riz._eq(context.bv_from_u64(0, 64));
        assert!(matches!(context.check_assertions(&[eq]), SatResult::Unsat));

        // StorageLocations::get_raw
        let riz = s.get_raw(&mut context, key, &Sizes::default());
        let eq = !riz._eq(context.bv_from_u64(0, 64));
        assert!(matches!(context.check_assertions(&[eq]), SatResult::Unsat));
    });
}
