//! Implements an [`UndefProvider`] for the [`X64Arch`] architecture, using `xed`.
//!
//! Note: to use this module, you must enable the `x64-undef` feature.
//! This feature will pull in the `xed-sys` dependency.

use rusty_xed::{AddressWidth, MachineMode, Xed, XedError};

use crate::arch::undef::{RegOrMem, UndefProvider, UndefinedOutput, UndefinedOutputs};
use crate::arch::x64::{X64Arch, X64Flag, X64Reg, X87Reg};
use crate::encoding::dataflows::Size;
use crate::semantics::default::computation::{Arg, ArgEncoding, AsComputationRef, OutputEncoding, SynthesizedComputation};
use crate::semantics::default::ops::Op;
use crate::semantics::default::{Expr, Expression};
use crate::semantics::IoType;

mod xed_convert;

use xed_convert::convert_operand;

/// Error produced by [`IntelUndefWithXed`].
#[derive(Clone, Debug, thiserror::Error)]
pub enum UdError {
    /// Indicates an unimplemented floating point condition is needed to express when the value is undefined.
    #[error("an unsupported floating point condition is needed to express when a value might be undefined")]
    FloatingPointCondition,

    /// Indicates that the instruction is a system instruction, for which we do not model enough state to be able to determine whether it is undefined.
    #[error("this instruction's outputs might be undefined depending on system configuration")]
    SystemInstruction,

    /// Indicates that disassembly through `xed` failed.
    #[error("xed: {}", .0)]
    Xed(XedError),
}

const X87_80BFP_MANTISSA_BITS: usize = 64;
const X87_80BFP_EXPONENT_BITS: usize = 15;
const X87_80BFP_EXPONENT_BIAS: i64 = 16383;

fn f80_is_real_number() -> SynthesizedComputation {
    SynthesizedComputation::new(
        Expression::new(vec![
            // exponent != ALL_ONES
            Op::Hole(0),
            Op::Select {
                num_skip: X87_80BFP_MANTISSA_BITS.try_into().unwrap(),
                num_take: X87_80BFP_EXPONENT_BITS.try_into().unwrap(),
            },
            Op::Hole(1),
            Op::Xor,
            Op::IsZero,
            Op::Not,
            // exponent == ALL_ZEROS || bit[63] != 0
            Op::Hole(0),
            Op::Select {
                num_skip: X87_80BFP_MANTISSA_BITS.try_into().unwrap(),
                num_take: X87_80BFP_EXPONENT_BITS.try_into().unwrap(),
            },
            Op::IsZero,
            Op::Hole(0),
            Op::Select {
                num_skip: (X87_80BFP_MANTISSA_BITS - 1).try_into().unwrap(),
                num_take: 1,
            },
            Op::IsZero,
            Op::Not,
            Op::Or,
            Op::And,
        ]),
        vec![
            Arg::Input {
                index: 0,
                encoding: ArgEncoding::UnsignedLittleEndian,
                num_bits: 80,
            },
            Arg::Const(0),
        ],
        vec![(1 << X87_80BFP_EXPONENT_BITS) - 1],
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    )
}

fn abs_exponent_geq(exponent_val: i64) -> SynthesizedComputation {
    f80_is_real_number().and(&SynthesizedComputation::new(
        Expression::new(vec![
            // exponent >= high_exclusive
            // == !(exponent < high_exclusive)
            Op::Hole(0),
            Op::Select {
                num_skip: X87_80BFP_MANTISSA_BITS.try_into().unwrap(),
                num_take: X87_80BFP_EXPONENT_BITS.try_into().unwrap(),
            },
            Op::Hole(1),
            Op::CmpLt,
            Op::Not,
        ]),
        vec![
            Arg::Input {
                index: 0,
                encoding: ArgEncoding::UnsignedLittleEndian,
                num_bits: 80,
            },
            Arg::Const(0),
        ],
        vec![exponent_val as i128 + X87_80BFP_EXPONENT_BIAS as i128],
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    ))
}

fn abs_fp80_greater_than(exponent_val: i64, mantissa_val: u64) -> SynthesizedComputation {
    abs_exponent_geq(exponent_val + 1).or(&f80_is_real_number().and(&SynthesizedComputation::new(
        Expression::new(vec![
            // exponent == exponent_val && mantissa > mantissa_val
            Op::Hole(0),
            Op::Select {
                num_skip: X87_80BFP_MANTISSA_BITS.try_into().unwrap(),
                num_take: X87_80BFP_EXPONENT_BITS.try_into().unwrap(),
            },
            Op::Hole(1),
            Op::Xor,
            Op::IsZero,
            Op::Hole(0),
            Op::Select {
                num_skip: 0,
                num_take: X87_80BFP_MANTISSA_BITS.try_into().unwrap(),
            },
            Op::Hole(2),
            Op::CmpLt,
            Op::Not,
            Op::And,
        ]),
        vec![
            Arg::Input {
                index: 0,
                encoding: ArgEncoding::UnsignedLittleEndian,
                num_bits: 80,
            },
            Arg::Const(0),
            Arg::Const(1),
        ],
        vec![
            exponent_val as i128 + X87_80BFP_EXPONENT_BIAS as i128,
            mantissa_val as i128 + 1,
        ],
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    )))
}

/// Provides an implementation of [`UndefProvider`] for the [`X64Arch`] architecture.
/// Relies on the `xed` disassembler.
pub struct IntelUndefWithXed;

impl UndefProvider<X64Arch> for IntelUndefWithXed {
    type Error = UdError;

    fn undefined_outputs_of(&self, instr: &[u8]) -> Result<UndefinedOutputs<X64Arch>, Self::Error> {
        let xed = Xed::new(MachineMode::Long64, AddressWidth::Width64b);
        let instr = xed.decode(instr).map_err(UdError::Xed)?;

        let r = UndefinedOutputs::new();

        // (val & mask) != 0 && ((val & mask) ^ 1) != 0
        const MASKED_NOT_ZERO_NOT_ONE: Expr = Expr::new(&[
            Op::Hole(0),
            Op::Hole(1),
            Op::And,
            Op::IsZero,
            Op::Not,
            Op::Hole(0),
            Op::Hole(1),
            Op::And,
            Op::Const(1),
            Op::Xor,
            Op::IsZero,
            Op::Not,
            Op::And,
        ]);

        // (val & mask) != 0
        const MASKED_NOT_ZERO: Expr = Expr::new(&[Op::Hole(0), Op::Hole(1), Op::And, Op::IsZero, Op::Not]);

        // !((val & mask) < threshold) == (val & mask) >= threshold
        const MASKED_GT_EQ: Expr = Expr::new(&[Op::Hole(0), Op::Hole(1), Op::And, Op::Hole(2), Op::CmpLt, Op::Not]);

        use rusty_xed::XedIClass::*;
        use X64Flag::*;
        Ok(match instr.iclass() {
            // Simple general purpose flags
            Aaa | Aas => r.with([ Of, Sf, Zf, Pf ]),
            Aad | Aam => r.with([ Of, Af, Cf ]),
            And | AndLock | Or | OrLock | Test | Xor | XorLock => r.with([ Af ]),
            Andn |
            Blcfill | Blci | Blcic | Blcmsk | Blcs |
            Blsfill | Blsi | Blsic | Blsmsk | Blsr |
            Bzhi | T1mskc | Tzmsk => r.with([ Af, Pf ]),
            Bextr | BextrXop => r.with([ Af, Sf, Pf ]),
            Bt | Btc | BtcLock | Btr | BtrLock | Bts | BtsLock => r.with([ Of, Sf, Af, Pf ]),
            Daa | Das => r.with([ Of ]),
            Div | Idiv | MovCr | MovDr => r.with([ Cf, Of, Sf, Zf, Af, Pf ]),
            Mul | Imul => r.with([ Sf, Zf, Af, Pf ]),
            Lzcnt => r.with([ Of, Sf, Pf, Af ]),

            // Simple FP flags
            Fabs | Fadd | Faddp |
            Fbstp | Fchs | Fcmovb | Fcmovbe | Fcmove | Fcmovnb | Fcmovnbe | Fcmovne | Fcmovnu | Fcmovu |
            Fdecstp |
            Fdiv | Fdivp | Fdivr | Fdivrp |
            Fiadd | Fpatan | Frndint | Fscale | Fsqrt | Fst | Fstp |
            // TODO: Assuming FSTPNCE behaves like FSTP, but I have no idea what it actually is
            Fstpnce |
            Fsub | Fsubp | Fsubr | Fsubrp | Fxch | Fxtract | Fyl2x |
            Fidiv | Fidivr | Fild | Fimul | Fincstp | Fist | Fistp | Fisttp | Fisub | Fisubr | Fld | Fld1 |
            Fldl2e | Fldl2t | Fldlg2 | Fldln2 | Fldpi | Fldz | Fmul | Fmulp => r.with([ ConditionCode(0), ConditionCode(2), ConditionCode(3) ]),
            Ffree |
            // https://www.pagetable.com/?p=16 -- "FFREEP – the assembly instruction that never existed"
            Ffreep |
            Fldcw | Fnclex | Fnop | Fnstcw | Fnstenv | Fnstsw => r.with([ ConditionCode(0), ConditionCode(1), ConditionCode(2), ConditionCode(3) ]),
            Fptan | Fsin | Fsincos => r.with([ ConditionCode(0), ConditionCode(2), ConditionCode(3) ]),

            // Complex general purpose instructions
            Bsf | Bsr => {
                let dest = convert_operand(instr.operands().get(0).unwrap(), &instr);
                let source = convert_operand(instr.operands().get(1).unwrap(), &instr);
                r.with([ Cf, Of, Sf, Af, Pf ])
                    .with(UndefinedOutput::from_target(dest)
                        .only_if_zero(source)
                    )
            },
            Bswap => {
                // result is undef when bswap references a 16-bit register
                // This happens when the 66 operand size override prefix is used
                let val = instr.operands().get(0).unwrap();
                if val.operand_size_bits() < 32 {
                    let reg = xed_convert::convert_reg(val.reg().unwrap());
                    assert_eq!(reg.num_bytes(), 2);
                    r.with(reg)
                } else {
                    r
                }
            },

            // Complex floating point instructions
            Fbld => {
                let mut ops = Vec::new();
                for n in (0..80).step_by(4) {
                    ops.extend([
                        Op::Hole(0),
                        Op::Select { num_skip: n, num_take: 4 },
                        Op::Const(10),
                        Op::CmpLt,
                    ]);
                    if n != 0 {
                        ops.push(Op::And);
                    }
                }
                ops.extend([
                    Op::Hole(1),
                    Op::Hole(2),
                    Op::Xor,
                    Op::IsZero,
                ]);

                // TODO: We can describe st(0) as: mmx7 is undefined if top == 0 && condition, mmx6 is undefined if top == 7 && condition, etc..
                let mut r = r.with([ ConditionCode(0), ConditionCode(2), ConditionCode(3) ]);
                for n in 0..8 {
                    let input = RegOrMem::new_reg(X64Reg::X87(X87Reg::Fpr(n as u8)), Size::new(0, 9));
                    // attempting to load an invalid encoding produces an undefined result
                    let condition = SynthesizedComputation::new(
                        Expression::new(ops.clone()),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: 80 },
                            Arg::Input { index: 1, encoding: ArgEncoding::UnsignedBigEndian, num_bits: 3 },
                            Arg::Const((n + 7) & 0x7)
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );

                    r = r.with(UndefinedOutput::from_target(input.clone())
                        .with_condition(condition, vec![ input.clone(), RegOrMem::new_reg(X64Reg::X87(X87Reg::TopOfStack), Size::new(0, 0)) ])
                    );
                }

                r
            },
            F2xm1 => {
                let mut r = r.with([ ConditionCode(0), ConditionCode(2), ConditionCode(3) ]);

                let base_condition = abs_fp80_greater_than(0, 0x8000_0000_0000_0000);
                for n in 0..8 {
                    // result is undefined if source value is outside -1.0..1.0 range
                    let target = RegOrMem::new_reg(X64Reg::X87(X87Reg::Fpr(n as u8)), Size::new(0, 9));
                    let condition = base_condition.and(&SynthesizedComputation::new(
                        Expression::new(vec! [
                            Op::Hole(0),
                            Op::Hole(1),
                            Op::Xor,
                            Op::IsZero,
                        ]),
                        vec![
                            Arg::Input { index: 1, encoding: ArgEncoding::UnsignedBigEndian, num_bits: 3 },
                            Arg::Const(n)
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    ));

                    r = r.with(UndefinedOutput::from_target(target.clone())
                        .with_condition(condition, vec![ target, RegOrMem::new_reg(X64Reg::X87(X87Reg::TopOfStack), Size::new(0, 0)) ])
                    );
                }

                r
            },
            Fcos => {
                let mut r = r.with([ ConditionCode(0), ConditionCode(3) ]);

                let base_condition = abs_exponent_geq(62);
                for n in 0..8 {
                    // c1 undefined if outside range (−2**63 < source operand < +2**63 )
                    let target = RegOrMem::new_reg(X64Reg::X87(X87Reg::Fpr(n as u8)), Size::new(0, 9));
                    let condition = base_condition.and(&SynthesizedComputation::new(
                        Expression::new(vec! [
                            Op::Hole(0),
                            Op::Hole(1),
                            Op::Xor,
                            Op::IsZero,
                        ]),
                        vec![
                            Arg::Input { index: 1, encoding: ArgEncoding::UnsignedBigEndian, num_bits: 3 },
                            Arg::Const(n)
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    ));

                    r = r.with(UndefinedOutput::from_target(target.clone())
                        .with_condition(condition, vec![ target, RegOrMem::new_reg(X64Reg::X87(X87Reg::TopOfStack), Size::new(0, 0)) ])
                    );
                }

                r
            },
            Fyl2xp1 => {
                let mut r = r.with([ ConditionCode(0), ConditionCode(2), ConditionCode(3) ]);

                let base_condition = abs_fp80_greater_than(-2, 0x95F6_1998_0C43_36F7);
                for n in 0..8 {
                    // result is undefined if source value is outside -(1-sqrt(2)/2)..(1-sqrt(2)/2) range
                    let target = RegOrMem::new_reg(X64Reg::X87(X87Reg::Fpr(n as u8)), Size::new(0, 9));
                    let condition = base_condition.and(&SynthesizedComputation::new(
                        Expression::new(vec! [
                            Op::Hole(0),
                            Op::Hole(1),
                            Op::Xor,
                            Op::IsZero,
                        ]),
                        vec![
                            Arg::Input { index: 1, encoding: ArgEncoding::UnsignedBigEndian, num_bits: 3 },
                            Arg::Const(n)
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    ));

                    r = r.with(UndefinedOutput::from_target(target.clone())
                        .with_condition(condition, vec![ target, RegOrMem::new_reg(X64Reg::X87(X87Reg::TopOfStack), Size::new(0, 0)) ])
                    );
                }

                r
            },
            Rcl | Rcr | Rol | Ror => {
                let val = instr.operands().get(0).unwrap();
                let count_op = instr.operands().get(1).unwrap();

                let mask = match val.operand_size_bits() {
                    8 | 16 | 32 => 0x1f,
                    64 => 0x3f,
                    other => panic!("rcl/rcr/rol/ror on {other} bits?"),
                };

                if let Some(value) = count_op.imm_value() {
                    let count = value & mask as u64;
                    if (count != 0 || matches!(instr.iclass(), Rol | Ror)) && count != 1 {
                        r.with([ Of ])
                    } else {
                        r
                    }
                } else {
                    let count = convert_operand(count_op, &instr);

                    // OF undefined if N != 1 and N != 0
                    let condition = SynthesizedComputation::new(
                        MASKED_NOT_ZERO_NOT_ONE.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );
                    r.with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(Of))
                            .with_condition(condition, vec![ count ])
                    )
                }
            },
            Salc | Sar => {
                let val = instr.operands().get(0).unwrap();
                let count_op = instr.operands().get(1).unwrap();

                let mask = match val.operand_size_bits() {
                    8 | 16 | 32 => 0x1f,
                    64 => 0x3f,
                    other => panic!("rcl/rcr/rol/ror on {other} bits?"),
                };

                if let Some(value) = count_op.imm_value() {
                    let count = value & mask as u64;
                    let mut r = r;
                    if count > 1 {
                        r = r.with([ Of ]);
                    }

                    if count != 0 {
                        r = r.with([ Af ]);
                    }

                    r
                } else {
                    let count = convert_operand(count_op, &instr);
                    // OF is undefined if count > 1
                    let of_condition = SynthesizedComputation::new(
                        MASKED_NOT_ZERO_NOT_ONE.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );
                    // AF is undefined if count != 0
                    let af_condition = SynthesizedComputation::new(
                        MASKED_NOT_ZERO.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );
                    r.with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Of))
                            .with_condition(of_condition, vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Af))
                            .with_condition(af_condition, vec![ count ])
                    )
                }
            },
            Shl | Shr => {
                let val = instr.operands().get(0).unwrap();
                let count_op = instr.operands().get(1).unwrap();

                let mask = match val.operand_size_bits() {
                    8 | 16 | 32 => 0x1f,
                    64 => 0x3f,
                    other => panic!("rcl/rcr/rol/ror on {other} bits?"),
                };

                if let Some(value) = count_op.imm_value() {
                    let count = value & mask as u64;
                    let mut r = r;
                    if count > 1 {
                        r = r.with([ Of ]);
                    }

                    if count != 0 {
                        r = r.with([ Af ]);
                    }

                    if count >= val.operand_size_bits() as u64 {
                        r = r.with([ Cf ]);
                    }

                    r
                } else {
                    let count = convert_operand(count_op, &instr);

                    // OF is undefined if count > 1
                    let of_condition = SynthesizedComputation::new(
                        MASKED_NOT_ZERO_NOT_ONE.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );
                    // AF is undefined if count != 0
                    let af_condition = SynthesizedComputation::new(
                        MASKED_NOT_ZERO.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );
                    // CF is undefined if count >= destination operand size
                    let cf_condition = SynthesizedComputation::new(
                        MASKED_GT_EQ.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                            Arg::TinyConst(val.operand_size_bits().try_into().unwrap()),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );
                    r.with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Of))
                            .with_condition(of_condition, vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Af))
                            .with_condition(af_condition, vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Cf))
                            .with_condition(cf_condition, vec![ count ])
                    )
                }
            },
            Shld | Shrd => {
                let val1 = instr.operands().get(0).unwrap();
                let val2 = instr.operands().get(0).unwrap();
                let count_op = instr.operands().get(2).unwrap();

                assert_eq!(val1.operand_size_bits(), val2.operand_size_bits());
                let mask = match val2.operand_size_bits() {
                    8 | 16 | 32 => 0x1f,
                    64 => 0x3f,
                    other => panic!("rcl/rcr/rol/ror on {other} bits?"),
                };

                if let Some(value) = count_op.imm_value() {
                    let count = value & mask as u64;
                    let mut r = r;
                    if count > 1 {
                        r = r.with([ Of ]);
                    }

                    if count != 0 {
                        r = r.with([ Af ]);
                    }

                    if count >= val1.operand_size_bits() as u64 {
                        r = r.with([ Cf, Of, Sf, Zf, Af, Pf ])
                            .with(convert_operand(val1, &instr));
                    }

                    r
                } else {
                    let count = convert_operand(count_op, &instr);
                    // [ result, Cf, Of, Sf, Zf, Af, Pf ] undefined if count is greater than operand size
                    let result_invalid_condition = SynthesizedComputation::new(
                        MASKED_GT_EQ.to_owned(),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                            Arg::TinyConst(val2.operand_size_bits().try_into().unwrap()),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );

                    // of undefined if count > 1 or if count is greater than operand size
                    let of_condition = SynthesizedComputation::new(
                        Expression::new(MASKED_GT_EQ.ops().iter()
                            .copied()
                            .chain(MASKED_NOT_ZERO_NOT_ONE.ops().iter().copied())
                            .chain([ Op::Or ])
                            .collect()
                        ),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                            Arg::TinyConst(val2.operand_size_bits().try_into().unwrap()),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );

                    // af undefined for count != 0 or if count is greater than operand size
                    let af_condition = SynthesizedComputation::new(
                        Expression::new(MASKED_GT_EQ.ops().iter()
                            .copied()
                            .chain(MASKED_NOT_ZERO.ops().iter().copied())
                            .chain([ Op::Or ])
                            .collect()
                        ),
                        vec![
                            Arg::Input { index: 0, encoding: ArgEncoding::UnsignedBigEndian, num_bits: (count.num_bytes() * 8).try_into().unwrap() },
                            Arg::TinyConst(mask),
                            Arg::TinyConst(val2.operand_size_bits().try_into().unwrap()),
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer { num_bits: 1 },
                    );

                    r.with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Cf))
                            .with_condition(result_invalid_condition.clone(), vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Of))
                            .with_condition(of_condition, vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Sf))
                            .with_condition(result_invalid_condition.clone(), vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Zf))
                            .with_condition(result_invalid_condition.clone(), vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Af))
                            .with_condition(af_condition, vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(RegOrMem::from_flag(X64Flag::Pf))
                            .with_condition(result_invalid_condition.clone(), vec![ count.clone() ])
                    ).with(
                        UndefinedOutput::from_target(convert_operand(val1, &instr))
                            .with_condition(result_invalid_condition.clone(), vec![ count.clone() ])
                    )
                }
            },
            Tzcnt => {
                let dest = convert_operand(instr.operands().get(0).unwrap(), &instr);
                let source = convert_operand(instr.operands().get(1).unwrap(), &instr);
                r.with([ Of, Sf, Pf, Af ])
                    .with(UndefinedOutput::from_target(dest)
                        .only_if_zero(source)
                    )
            },

            // Not supported: system-level instructions
            Lar => {
                // If operand size is 32 or higher, Bits 19:16 are undefined
                return Err(UdError::SystemInstruction)
            },
            Xgetbv => {
                // If fewer than 64 bits are implemented in the XCR being read, the values returned to EDX:EAX in unimplemented bit locations are undefined

                return Err(UdError::SystemInstruction)
            },
            Rdmsr => {
                // If fewer than 64 bits are implemented in the MSR being read, the values returned to EDX:EAX in unimplemented bit locations are undefined.

                return Err(UdError::SystemInstruction)
            }
            _ => r
        })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use rustc_apfloat::ieee::X87DoubleExtended;
    use rustc_apfloat::Float;
    use rusty_xed::{Xed, XedIClass};

    use super::{abs_exponent_geq, abs_fp80_greater_than, IntelUndefWithXed, RegOrMem, UndefinedOutputs};
    use crate::arch::x64::{GpReg, X64Reg};
    use crate::encoding::dataflows::{AddrTerm, AddrTermSize, AddressComputation, Size};
    use crate::semantics::{Computation, ARG_NAMES};
    use crate::state::random::randomized_bytes;
    use crate::value::{AsValue, Value};

    #[test]
    pub fn bsf_mem_condition() {
        // bsf    rax,QWORD PTR [rdx+rcx*4]
        let result = UndefinedOutputs::of(&[0x48, 0x0F, 0xBC, 0x04, 0x8A], &IntelUndefWithXed).unwrap();
        assert!(
            result.iter().any(|o| {
                o.target()
                    == &RegOrMem::Reg {
                        reg: X64Reg::GpReg(GpReg::Rax),
                        size: Size::qword(),
                    }
                    && o.condition()
                        .map(|c| c.display(ARG_NAMES).to_string() == "IsZero(ube(A))")
                        .unwrap_or(false)
                    && o.inputs()
                        == [RegOrMem::Memory {
                            calculation: AddressComputation {
                                offset: 0,
                                terms: [
                                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                                    AddrTerm::single(AddrTermSize::U64, 0, 4),
                                    AddrTerm::default(),
                                    AddrTerm::default(),
                                ],
                            },
                            inputs: vec![
                                RegOrMem::Reg {
                                    reg: X64Reg::GpReg(GpReg::Rdx),
                                    size: Size::qword(),
                                },
                                RegOrMem::Reg {
                                    reg: X64Reg::GpReg(GpReg::Rcx),
                                    size: Size::qword(),
                                },
                            ],
                            num_bytes: 8,
                        }]
            }),
            "Found: {result:#?}"
        );

        // bsf    r11d,DWORD PTR [rdx+r9*8+0x12321]
        let result = UndefinedOutputs::of(&[0x46, 0x0F, 0xBC, 0x9C, 0xCA, 0x21, 0x23, 0x01, 0x00], &IntelUndefWithXed).unwrap();
        assert!(
            result.iter().any(|o| {
                o.target()
                    == &RegOrMem::Reg {
                        reg: X64Reg::GpReg(GpReg::R11),
                        size: Size::new(0, 3),
                    }
                    && o.condition()
                        .map(|c| c.display(ARG_NAMES).to_string() == "IsZero(ube(A))")
                        .unwrap_or(false)
                    && o.inputs()
                        == [RegOrMem::Memory {
                            calculation: AddressComputation {
                                offset: 0x12321,
                                terms: [
                                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                                    AddrTerm::single(AddrTermSize::U64, 0, 8),
                                    AddrTerm::default(),
                                    AddrTerm::default(),
                                ],
                            },
                            inputs: vec![
                                RegOrMem::Reg {
                                    reg: X64Reg::GpReg(GpReg::Rdx),
                                    size: Size::qword(),
                                },
                                RegOrMem::Reg {
                                    reg: X64Reg::GpReg(GpReg::R9),
                                    size: Size::qword(),
                                },
                            ],
                            num_bytes: 4,
                        }]
            }),
            "Found: {result:#?}"
        )
    }

    #[test]
    pub fn test_x87_abs_exponent_greater_than() {
        let computation = abs_exponent_geq(63);
        let mut r = StdRng::seed_from_u64(0);
        let mut num_smaller = 0;
        let mut num_geq = 0;
        for _ in 0..100_000_000 {
            let bytes = randomized_bytes(&mut r, 10);
            let computation_result = computation.evaluate(&[Value::Bytes(&bytes)]);
            let nval = bytes.iter().rev().fold(0u128, |acc, val| (acc << 8) | *val as u128);

            let bit63 = (nval >> 63) & 1;
            let exp = (nval >> 64) & 0x7fff;
            if bit63 == 0 && exp != 0 {
                // exponent = anything non-zero, bit63 = 0:
                // Unnormal. Only generated on the 8087 and 80287. The 80387 and later treat this as an invalid operand.
                continue
            }

            let fval = X87DoubleExtended::from_bits(nval);
            let exp = fval.ilogb();

            let is_geq = exp >= 63 && !fval.is_nan() && !fval.is_infinite();

            if is_geq {
                num_geq += 1;
            } else {
                num_smaller += 1;
            }

            // TODO: This doesn't actually verify much somehow. Maybe our random values are bad?
            assert_eq!(
                is_geq,
                computation_result.unwrap_num() != 0,
                "Value: {bytes:02X?} val={fval}; Computation result: {computation_result:?}; Category: {:?}",
                fval.category()
            );
        }

        assert!(num_geq >= 10_000);
        assert!(num_smaller >= 10_000);
    }

    #[test]
    pub fn test_x87_abs_fp80_geq() {
        let computation = abs_fp80_greater_than(0, 0x8000_0000_0000_0000);
        let mut r = StdRng::seed_from_u64(0);
        let low = X87DoubleExtended::from_str("-1").unwrap();
        let high = X87DoubleExtended::from_str("1").unwrap();
        println!("Computation: {}", computation.display(ARG_NAMES));
        for _ in 0..100_000_000 {
            let bytes = randomized_bytes(&mut r, 10);
            let computation_result = computation.evaluate(&[Value::Bytes(&bytes)]);
            let nval = bytes.iter().rev().fold(0u128, |acc, val| (acc << 8) | *val as u128);

            let bit63 = (nval >> 63) & 1;
            let exp = (nval >> 64) & 0x7fff;
            if bit63 == 0 && exp != 0 {
                // exponent = anything non-zero, bit63 = 0:
                // Unnormal. Only generated on the 8087 and 80287. The 80387 and later treat this as an invalid operand.
                continue
            }

            let fval = X87DoubleExtended::from_bits(nval);

            let abs_is_geq = (fval < low || fval > high) && !fval.is_nan() && !fval.is_infinite();

            // TODO: This doesn't actually verify much somehow. Maybe our random values are bad?
            assert_eq!(
                abs_is_geq,
                computation_result.unwrap_num() != 0,
                "Value: {bytes:02X?} <=> 0x{nval:X} (bit63={bit63}, exp={exp}) val={fval}; Computation result: {computation_result:?}; abs_exponent_geq(0) = {:?}",
                abs_exponent_geq(0).evaluate(&[Value::Bytes(&bytes)])
            );
        }
    }

    #[test]
    pub fn test_x87_fyl2xp1_condition() {
        let computation = abs_fp80_greater_than(-2, 0x95F6_1998_0C43_36F7);
        let mut r = StdRng::seed_from_u64(0);
        let low = X87DoubleExtended::from_str("-0.2928932188134524755991556378951509607151640623115259634116601310").unwrap();
        let high = X87DoubleExtended::from_str("0.2928932188134524755991556378951509607151640623115259634116601310").unwrap();
        println!("Computation: {}", computation.display(ARG_NAMES));
        for _ in 0..100_000_000 {
            let bytes = randomized_bytes(&mut r, 10);
            let computation_result = computation.evaluate(&[Value::Bytes(&bytes)]);
            let nval = bytes.iter().rev().fold(0u128, |acc, val| (acc << 8) | *val as u128);

            let bit63 = (nval >> 63) & 1;
            let exp = (nval >> 64) & 0x7fff;
            if bit63 == 0 && exp != 0 {
                // exponent = anything non-zero, bit63 = 0:
                // Unnormal. Only generated on the 8087 and 80287. The 80387 and later treat this as an invalid operand.
                continue
            }

            let fval = X87DoubleExtended::from_bits(nval);

            let abs_is_geq = (fval < low || fval > high) && !fval.is_nan() && !fval.is_infinite();

            // TODO: This doesn't actually verify much somehow. Maybe our random values are bad?
            assert_eq!(
                abs_is_geq,
                computation_result.unwrap_num() != 0,
                "Value: {bytes:02X?} <=> 0x{nval:X} (bit63={bit63}, exp={exp}) val={fval}; Computation result: {computation_result:?}; abs_exponent_geq(0) = {:?}",
                abs_exponent_geq(0).evaluate(&[Value::Bytes(&bytes)])
            );
        }
    }

    #[test]
    pub fn mov_cr_dr_must_not_decode_to_generic_mov() {
        let xed = Xed::new(rusty_xed::MachineMode::Long64, rusty_xed::AddressWidth::Width64b);

        for instr in [
            // mov crX, r64
            [0x0F, 0x22, 0xC0].as_slice(), // cr0
            &[0x0F, 0x22, 0xD0],           // cr2
            &[0x0F, 0x22, 0xD8],           // cr3
            &[0x0F, 0x22, 0xE0],           // cr4
            &[0x44, 0x0F, 0x22, 0xC0],     // cr8
            // mov r64, crX
            &[0x0F, 0x20, 0xC0],       // cr0
            &[0x0F, 0x20, 0xD0],       // cr2
            &[0x0F, 0x20, 0xD8],       // cr3
            &[0x0F, 0x20, 0xE0],       // cr4
            &[0x44, 0x0F, 0x20, 0xC0], // cr8
        ] {
            println!("Instr: {instr:02X?}");
            assert_eq!(xed.decode(instr).unwrap().iclass(), XedIClass::MovCr);
        }

        for instr in [
            // mov drX, r64
            &[0x0F, 0x23, 0xC0],
            &[0x0F, 0x23, 0xC8],
            &[0x0F, 0x23, 0xD0],
            &[0x0F, 0x23, 0xD8],
            &[0x0F, 0x23, 0xE0],
            &[0x0F, 0x23, 0xE8],
            &[0x0F, 0x23, 0xF0],
            &[0x0F, 0x23, 0xF8],
            // mov r64, crX
            &[0x0F, 0x21, 0xC0],
            &[0x0F, 0x21, 0xC8],
            &[0x0F, 0x21, 0xD0],
            &[0x0F, 0x21, 0xD8],
            &[0x0F, 0x21, 0xE0],
            &[0x0F, 0x21, 0xE8],
            &[0x0F, 0x21, 0xF0],
            &[0x0F, 0x21, 0xF8],
        ] {
            println!("Instr: {instr:02X?}");
            assert_eq!(xed.decode(instr).unwrap().iclass(), XedIClass::MovDr);
        }
    }
}
