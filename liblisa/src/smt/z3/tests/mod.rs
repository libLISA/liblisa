//! Defines tests for liblisa::compare.
//!
//! Normally, tests would be defined in liblisa itself.
//! However, for comparison an SMT solver is needed to run.
//! We cannot have liblisa depend on liblisa_z3, because liblisa_z3 itself also depends on liblisa.
//! Therefore, tests that require an SMT solver are defined here instead.

mod computations;
mod equivalence;

use std::time::Duration;

use crate::arch::fake::{FakeArch, FakeReg, FakeState};
use crate::arch::x64::{GpReg, X64Arch, X64Reg};
use crate::encoding::bitpattern::Bit;
use crate::encoding::dataflows::{
    AccessKind, AddressComputation, Dataflow, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses, Size,
};
use crate::encoding::Encoding;
use crate::semantics::default::computation::{Arg, ArgEncoding, OutputEncoding, SynthesizedComputation};
use crate::semantics::default::ops::Op;
use crate::semantics::default::smtgen::{FilledLocation, Sizes, StorageLocations, Z3Model};
use crate::semantics::default::Expression;
use crate::semantics::IoType;
use crate::smt::z3::Z3Solver;
use crate::smt::{SatResult, SmtBV, SmtBVArray, SmtSolver};
use crate::state::{Addr, Location, MemoryState, Permissions, SystemState};
use crate::Instruction;

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
        #[allow(deprecated)]
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

#[test]
pub fn identity_function_should_be_identical() {
    use FakeReg::*;
    let instr = Instruction::new(&[0x00]);
    let encoding = Encoding {
        bits: vec![Bit::Fixed(0); 8],
        errors: vec![false; 8],
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: MemoryAccesses {
                instr,
                memory: vec![
                    MemoryAccess {
                        kind: AccessKind::Executable,
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
                        size: 2..2,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    },
                    MemoryAccess {
                        kind: AccessKind::InputOutput,
                        inputs: Inputs::sorted(vec![Dest::Reg(R1, Size::qword()).into()]),
                        size: 8..8,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    },
                    MemoryAccess {
                        kind: AccessKind::InputOutput,
                        inputs: Inputs::sorted(vec![Dest::Reg(R2, Size::qword()).into()]),
                        size: 8..8,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    },
                ],
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Mem(2, Size::new(0, 7)),
                inputs: Inputs::sorted(vec![Dest::Mem(1, Size::new(0, 7)).into()]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0)]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 64,
                        encoding: ArgEncoding::UnsignedLittleEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Bytes {
                        num_bytes: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    // Ensure that the semantics execute the way we expect
    let mut state = SystemState::new(
        FakeState::default(),
        MemoryState::new(
            [
                (Addr::new(0), Permissions::Execute, vec![0x00]),
                (Addr::new(0), Permissions::ReadWrite, vec![1, 2, 3, 4, 5, 6, 7, 8]),
                (Addr::new(0), Permissions::ReadWrite, vec![0; 8]),
            ]
            .into_iter(),
        ),
    );
    encoding.dataflows.execute(&mut state);

    assert_eq!(state.memory().get(2).2, vec![1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(state.memory().get(2).2, vec![1, 2, 3, 4, 5, 6, 7, 8]);

    Z3Solver::with_thread_local(Duration::from_secs(900), |mut context| {
        let mut storage = StorageLocations::<FakeArch, _>::new(&mut context);
        let model = Z3Model::of(&encoding, &mut storage, &mut context);
        let concrete = model.compute_concrete_outputs(&encoding, &mut storage, &mut context);

        println!();

        for item in model.constraints() {
            println!("constraint: {item}");
        }

        assert_eq!(concrete.intermediate_values_needed(), &[] as &[usize]);

        println!();

        let output = concrete
            .concrete_outputs()
            .iter()
            .find(|o| o.target() == Dest::Mem(2, Size::new(0, 7)))
            .expect("should have Mem2 output");

        let m2 = context.new_bv_const("m2_out", 64);

        let m1 = context.new_bv_const("m1_in", 64);
        let m1_val = storage
            .get_sized(
                &mut context,
                FilledLocation::Concrete(Location::Memory(1)),
                &Sizes::from_encoding(&encoding),
                Size::new(0, 7),
                true,
            )
            .extract(63, 0);
        let assertions = [
            m1.clone()._eq(m1_val.clone()),
            m2.clone()._eq(output.smt().cloned().unwrap()),
            !m1._eq(m2),
        ];

        let result = context.check_assertions(&assertions);
        match result {
            SatResult::Unknown => unreachable!(),
            SatResult::Sat(model) => panic!("found case where input m1 is not equal to output m2: {model:#?}"),
            SatResult::Unsat => (),
        }
    });
}

#[test]
pub fn test_pdep() {
    Z3Solver::with_thread_local(Duration::from_secs(900), |mut context| {
        fn test<'ctx, S: SmtSolver<'ctx>>(context: &mut S, source: u64, mask: u64, expected: u64) {
            let source_bv = context.new_bv_const("source", 64);
            let mask_bv = context.new_bv_const("mask", 64);
            let result_bv = context.new_bv_const("result", 64);
            let result_val = context.deposit_bits::<64>(source_bv.clone(), mask_bv.clone());

            let source_val = context.bv_from_u64(source, 64);
            let mask_val = context.bv_from_u64(mask, 64);
            let expected_val = context.bv_from_u64(expected, 64);
            match context.check_assertions(&[
                source_bv.clone()._eq(source_val),
                mask_bv.clone()._eq(mask_val),
                result_bv.clone()._eq(result_val),
                !result_bv.clone()._eq(expected_val),
            ]) {
                SatResult::Unknown => todo!(),
                SatResult::Sat(model) => panic!("implementation incorrect: {model:?}, expected {expected:X?}"),
                SatResult::Unsat => (),
            }
        }

        test(&mut context, 0xffff_ffff_ffff_ffff, 0x123456789abcdef, 0x123456789abcdef);
        test(
            &mut context,
            0xaaaa_aaaa_aaaa_aaaa,
            0x0000_fffe_ffff_0078,
            0x0000_5554_aaaa_0050,
        );
    });
}
