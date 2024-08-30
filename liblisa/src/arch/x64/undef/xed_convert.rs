use rusty_xed::{DecodedInstr, MemoryAccess, Operand, OperandName, XedReg};

use crate::arch::undef::RegOrMem;
use crate::arch::x64::{X64Arch, X64Reg, X87Reg, XmmReg};
use crate::encoding::dataflows::{AddrTerm, AddrTermSize, AddressComputation, Size};

pub fn convert_reg(reg: XedReg) -> RegOrMem<X64Arch> {
    use X64Reg::*;

    use crate::arch::x64::GpReg::*;

    const B: Size = Size::new(0, 0);
    const BH: Size = Size::new(1, 1);
    const W: Size = Size::new(0, 1);
    const D: Size = Size::new(0, 3);
    const Q: Size = Size::new(0, 7);
    const SIZE_XMM: Size = Size::new(0, 15);
    const SIZE_YMM: Size = Size::new(0, 31);
    const SIZE_ZMM: Size = Size::new(0, 63);
    const ST_SIZE: Size = Size::new(0, 9);

    match reg {
        XedReg::Flags => RegOrMem::new_reg(GpReg(RFlags), W),
        XedReg::Eflags => RegOrMem::new_reg(GpReg(RFlags), D),
        XedReg::Rflags => RegOrMem::new_reg(GpReg(RFlags), Q),
        XedReg::Ax => RegOrMem::new_reg(GpReg(Rax), W),
        XedReg::Cx => RegOrMem::new_reg(GpReg(Rcx), W),
        XedReg::Dx => RegOrMem::new_reg(GpReg(Rdx), W),
        XedReg::Bx => RegOrMem::new_reg(GpReg(Rbx), W),
        XedReg::Sp => RegOrMem::new_reg(GpReg(Rsp), W),
        XedReg::Bp => RegOrMem::new_reg(GpReg(Rbp), W),
        XedReg::Si => RegOrMem::new_reg(GpReg(Rsi), W),
        XedReg::Di => RegOrMem::new_reg(GpReg(Rdi), W),
        XedReg::R8W => RegOrMem::new_reg(GpReg(R8), W),
        XedReg::R9W => RegOrMem::new_reg(GpReg(R9), W),
        XedReg::R10W => RegOrMem::new_reg(GpReg(R10), W),
        XedReg::R11W => RegOrMem::new_reg(GpReg(R11), W),
        XedReg::R12W => RegOrMem::new_reg(GpReg(R12), W),
        XedReg::R13W => RegOrMem::new_reg(GpReg(R13), W),
        XedReg::R14W => RegOrMem::new_reg(GpReg(R14), W),
        XedReg::R15W => RegOrMem::new_reg(GpReg(R15), W),
        XedReg::Eax => RegOrMem::new_reg(GpReg(Rax), D),
        XedReg::Ecx => RegOrMem::new_reg(GpReg(Rcx), D),
        XedReg::Edx => RegOrMem::new_reg(GpReg(Rdx), D),
        XedReg::Ebx => RegOrMem::new_reg(GpReg(Rbx), D),
        XedReg::Esp => RegOrMem::new_reg(GpReg(Rsp), D),
        XedReg::Ebp => RegOrMem::new_reg(GpReg(Rbp), D),
        XedReg::Esi => RegOrMem::new_reg(GpReg(Rsi), D),
        XedReg::Edi => RegOrMem::new_reg(GpReg(Rdi), D),
        XedReg::R8D => RegOrMem::new_reg(GpReg(R8), D),
        XedReg::R9D => RegOrMem::new_reg(GpReg(R9), D),
        XedReg::R10D => RegOrMem::new_reg(GpReg(R10), D),
        XedReg::R11D => RegOrMem::new_reg(GpReg(R11), D),
        XedReg::R12D => RegOrMem::new_reg(GpReg(R12), D),
        XedReg::R13D => RegOrMem::new_reg(GpReg(R13), D),
        XedReg::R14D => RegOrMem::new_reg(GpReg(R14), D),
        XedReg::R15D => RegOrMem::new_reg(GpReg(R15), D),
        XedReg::Rax => RegOrMem::new_reg(GpReg(Rax), Q),
        XedReg::Rcx => RegOrMem::new_reg(GpReg(Rcx), Q),
        XedReg::Rdx => RegOrMem::new_reg(GpReg(Rdx), Q),
        XedReg::Rbx => RegOrMem::new_reg(GpReg(Rbx), Q),
        XedReg::Rsp => RegOrMem::new_reg(GpReg(Rsp), Q),
        XedReg::Rbp => RegOrMem::new_reg(GpReg(Rbp), Q),
        XedReg::Rsi => RegOrMem::new_reg(GpReg(Rsi), Q),
        XedReg::Rdi => RegOrMem::new_reg(GpReg(Rdi), Q),
        XedReg::R8 => RegOrMem::new_reg(GpReg(R8), Q),
        XedReg::R9 => RegOrMem::new_reg(GpReg(R9), Q),
        XedReg::R10 => RegOrMem::new_reg(GpReg(R10), Q),
        XedReg::R11 => RegOrMem::new_reg(GpReg(R11), Q),
        XedReg::R12 => RegOrMem::new_reg(GpReg(R12), Q),
        XedReg::R13 => RegOrMem::new_reg(GpReg(R13), Q),
        XedReg::R14 => RegOrMem::new_reg(GpReg(R14), Q),
        XedReg::R15 => RegOrMem::new_reg(GpReg(R15), Q),
        XedReg::Al => RegOrMem::new_reg(GpReg(Rax), B),
        XedReg::Cl => RegOrMem::new_reg(GpReg(Rcx), B),
        XedReg::Dl => RegOrMem::new_reg(GpReg(Rdx), B),
        XedReg::Bl => RegOrMem::new_reg(GpReg(Rbx), B),
        XedReg::Spl => RegOrMem::new_reg(GpReg(Rsp), B),
        XedReg::Bpl => RegOrMem::new_reg(GpReg(Rbp), B),
        XedReg::Sil => RegOrMem::new_reg(GpReg(Rsi), B),
        XedReg::Dil => RegOrMem::new_reg(GpReg(Rdi), B),
        XedReg::R8B => RegOrMem::new_reg(GpReg(R8), B),
        XedReg::R9B => RegOrMem::new_reg(GpReg(R9), B),
        XedReg::R10B => RegOrMem::new_reg(GpReg(R10), B),
        XedReg::R11B => RegOrMem::new_reg(GpReg(R11), B),
        XedReg::R12B => RegOrMem::new_reg(GpReg(R12), B),
        XedReg::R13B => RegOrMem::new_reg(GpReg(R13), B),
        XedReg::R14B => RegOrMem::new_reg(GpReg(R14), B),
        XedReg::R15B => RegOrMem::new_reg(GpReg(R15), B),
        XedReg::Ah => RegOrMem::new_reg(GpReg(Rax), BH),
        XedReg::Ch => RegOrMem::new_reg(GpReg(Rcx), BH),
        XedReg::Dh => RegOrMem::new_reg(GpReg(Rdx), BH),
        XedReg::Bh => RegOrMem::new_reg(GpReg(Rbx), BH),
        XedReg::Rip => RegOrMem::new_reg(GpReg(Rip), Q),
        XedReg::Eip => RegOrMem::new_reg(GpReg(Rip), D),
        XedReg::Ip => RegOrMem::new_reg(GpReg(Rip), W),
        XedReg::Mmx0 => RegOrMem::new_reg(X87(X87Reg::Fpr(0)), ST_SIZE),
        XedReg::Mmx1 => RegOrMem::new_reg(X87(X87Reg::Fpr(1)), ST_SIZE),
        XedReg::Mmx2 => RegOrMem::new_reg(X87(X87Reg::Fpr(2)), ST_SIZE),
        XedReg::Mmx3 => RegOrMem::new_reg(X87(X87Reg::Fpr(3)), ST_SIZE),
        XedReg::Mmx4 => RegOrMem::new_reg(X87(X87Reg::Fpr(4)), ST_SIZE),
        XedReg::Mmx5 => RegOrMem::new_reg(X87(X87Reg::Fpr(5)), ST_SIZE),
        XedReg::Mmx6 => RegOrMem::new_reg(X87(X87Reg::Fpr(6)), ST_SIZE),
        XedReg::Mmx7 => RegOrMem::new_reg(X87(X87Reg::Fpr(7)), ST_SIZE),
        XedReg::Fs => RegOrMem::new_reg(GpReg(FsBase), Q),
        XedReg::Gs => RegOrMem::new_reg(GpReg(GsBase), Q),
        // TODO: What's the difference between [FG]s and [FG]sBase?
        XedReg::Fsbase => RegOrMem::new_reg(GpReg(FsBase), Q),
        XedReg::Gsbase => RegOrMem::new_reg(GpReg(GsBase), Q),
        XedReg::Xmm0 => RegOrMem::new_reg(Xmm(XmmReg::Reg(0)), SIZE_XMM),
        XedReg::Xmm1 => RegOrMem::new_reg(Xmm(XmmReg::Reg(1)), SIZE_XMM),
        XedReg::Xmm2 => RegOrMem::new_reg(Xmm(XmmReg::Reg(2)), SIZE_XMM),
        XedReg::Xmm3 => RegOrMem::new_reg(Xmm(XmmReg::Reg(3)), SIZE_XMM),
        XedReg::Xmm4 => RegOrMem::new_reg(Xmm(XmmReg::Reg(4)), SIZE_XMM),
        XedReg::Xmm5 => RegOrMem::new_reg(Xmm(XmmReg::Reg(5)), SIZE_XMM),
        XedReg::Xmm6 => RegOrMem::new_reg(Xmm(XmmReg::Reg(6)), SIZE_XMM),
        XedReg::Xmm7 => RegOrMem::new_reg(Xmm(XmmReg::Reg(7)), SIZE_XMM),
        XedReg::Xmm8 => RegOrMem::new_reg(Xmm(XmmReg::Reg(8)), SIZE_XMM),
        XedReg::Xmm9 => RegOrMem::new_reg(Xmm(XmmReg::Reg(9)), SIZE_XMM),
        XedReg::Xmm10 => RegOrMem::new_reg(Xmm(XmmReg::Reg(10)), SIZE_XMM),
        XedReg::Xmm11 => RegOrMem::new_reg(Xmm(XmmReg::Reg(11)), SIZE_XMM),
        XedReg::Xmm12 => RegOrMem::new_reg(Xmm(XmmReg::Reg(12)), SIZE_XMM),
        XedReg::Xmm13 => RegOrMem::new_reg(Xmm(XmmReg::Reg(13)), SIZE_XMM),
        XedReg::Xmm14 => RegOrMem::new_reg(Xmm(XmmReg::Reg(14)), SIZE_XMM),
        XedReg::Xmm15 => RegOrMem::new_reg(Xmm(XmmReg::Reg(15)), SIZE_XMM),
        XedReg::Xmm16 => RegOrMem::new_reg(Xmm(XmmReg::Reg(16)), SIZE_XMM),
        XedReg::Xmm17 => RegOrMem::new_reg(Xmm(XmmReg::Reg(17)), SIZE_XMM),
        XedReg::Xmm18 => RegOrMem::new_reg(Xmm(XmmReg::Reg(18)), SIZE_XMM),
        XedReg::Xmm19 => RegOrMem::new_reg(Xmm(XmmReg::Reg(19)), SIZE_XMM),
        XedReg::Xmm20 => RegOrMem::new_reg(Xmm(XmmReg::Reg(20)), SIZE_XMM),
        XedReg::Xmm21 => RegOrMem::new_reg(Xmm(XmmReg::Reg(21)), SIZE_XMM),
        XedReg::Xmm22 => RegOrMem::new_reg(Xmm(XmmReg::Reg(22)), SIZE_XMM),
        XedReg::Xmm23 => RegOrMem::new_reg(Xmm(XmmReg::Reg(23)), SIZE_XMM),
        XedReg::Xmm24 => RegOrMem::new_reg(Xmm(XmmReg::Reg(24)), SIZE_XMM),
        XedReg::Xmm25 => RegOrMem::new_reg(Xmm(XmmReg::Reg(25)), SIZE_XMM),
        XedReg::Xmm26 => RegOrMem::new_reg(Xmm(XmmReg::Reg(26)), SIZE_XMM),
        XedReg::Xmm27 => RegOrMem::new_reg(Xmm(XmmReg::Reg(27)), SIZE_XMM),
        XedReg::Xmm28 => RegOrMem::new_reg(Xmm(XmmReg::Reg(28)), SIZE_XMM),
        XedReg::Xmm29 => RegOrMem::new_reg(Xmm(XmmReg::Reg(29)), SIZE_XMM),
        XedReg::Xmm30 => RegOrMem::new_reg(Xmm(XmmReg::Reg(30)), SIZE_XMM),
        XedReg::Xmm31 => RegOrMem::new_reg(Xmm(XmmReg::Reg(31)), SIZE_XMM),
        XedReg::Ymm0 => RegOrMem::new_reg(Xmm(XmmReg::Reg(0)), SIZE_YMM),
        XedReg::Ymm1 => RegOrMem::new_reg(Xmm(XmmReg::Reg(1)), SIZE_YMM),
        XedReg::Ymm2 => RegOrMem::new_reg(Xmm(XmmReg::Reg(2)), SIZE_YMM),
        XedReg::Ymm3 => RegOrMem::new_reg(Xmm(XmmReg::Reg(3)), SIZE_YMM),
        XedReg::Ymm4 => RegOrMem::new_reg(Xmm(XmmReg::Reg(4)), SIZE_YMM),
        XedReg::Ymm5 => RegOrMem::new_reg(Xmm(XmmReg::Reg(5)), SIZE_YMM),
        XedReg::Ymm6 => RegOrMem::new_reg(Xmm(XmmReg::Reg(6)), SIZE_YMM),
        XedReg::Ymm7 => RegOrMem::new_reg(Xmm(XmmReg::Reg(7)), SIZE_YMM),
        XedReg::Ymm8 => RegOrMem::new_reg(Xmm(XmmReg::Reg(8)), SIZE_YMM),
        XedReg::Ymm9 => RegOrMem::new_reg(Xmm(XmmReg::Reg(9)), SIZE_YMM),
        XedReg::Ymm10 => RegOrMem::new_reg(Xmm(XmmReg::Reg(10)), SIZE_YMM),
        XedReg::Ymm11 => RegOrMem::new_reg(Xmm(XmmReg::Reg(11)), SIZE_YMM),
        XedReg::Ymm12 => RegOrMem::new_reg(Xmm(XmmReg::Reg(12)), SIZE_YMM),
        XedReg::Ymm13 => RegOrMem::new_reg(Xmm(XmmReg::Reg(13)), SIZE_YMM),
        XedReg::Ymm14 => RegOrMem::new_reg(Xmm(XmmReg::Reg(14)), SIZE_YMM),
        XedReg::Ymm15 => RegOrMem::new_reg(Xmm(XmmReg::Reg(15)), SIZE_YMM),
        XedReg::Ymm16 => RegOrMem::new_reg(Xmm(XmmReg::Reg(16)), SIZE_YMM),
        XedReg::Ymm17 => RegOrMem::new_reg(Xmm(XmmReg::Reg(17)), SIZE_YMM),
        XedReg::Ymm18 => RegOrMem::new_reg(Xmm(XmmReg::Reg(18)), SIZE_YMM),
        XedReg::Ymm19 => RegOrMem::new_reg(Xmm(XmmReg::Reg(19)), SIZE_YMM),
        XedReg::Ymm20 => RegOrMem::new_reg(Xmm(XmmReg::Reg(20)), SIZE_YMM),
        XedReg::Ymm21 => RegOrMem::new_reg(Xmm(XmmReg::Reg(21)), SIZE_YMM),
        XedReg::Ymm22 => RegOrMem::new_reg(Xmm(XmmReg::Reg(22)), SIZE_YMM),
        XedReg::Ymm23 => RegOrMem::new_reg(Xmm(XmmReg::Reg(23)), SIZE_YMM),
        XedReg::Ymm24 => RegOrMem::new_reg(Xmm(XmmReg::Reg(24)), SIZE_YMM),
        XedReg::Ymm25 => RegOrMem::new_reg(Xmm(XmmReg::Reg(25)), SIZE_YMM),
        XedReg::Ymm26 => RegOrMem::new_reg(Xmm(XmmReg::Reg(26)), SIZE_YMM),
        XedReg::Ymm27 => RegOrMem::new_reg(Xmm(XmmReg::Reg(27)), SIZE_YMM),
        XedReg::Ymm28 => RegOrMem::new_reg(Xmm(XmmReg::Reg(28)), SIZE_YMM),
        XedReg::Ymm29 => RegOrMem::new_reg(Xmm(XmmReg::Reg(29)), SIZE_YMM),
        XedReg::Ymm30 => RegOrMem::new_reg(Xmm(XmmReg::Reg(30)), SIZE_YMM),
        XedReg::Ymm31 => RegOrMem::new_reg(Xmm(XmmReg::Reg(31)), SIZE_YMM),
        XedReg::Zmm0 => RegOrMem::new_reg(Xmm(XmmReg::Reg(0)), SIZE_ZMM),
        XedReg::Zmm1 => RegOrMem::new_reg(Xmm(XmmReg::Reg(1)), SIZE_ZMM),
        XedReg::Zmm2 => RegOrMem::new_reg(Xmm(XmmReg::Reg(2)), SIZE_ZMM),
        XedReg::Zmm3 => RegOrMem::new_reg(Xmm(XmmReg::Reg(3)), SIZE_ZMM),
        XedReg::Zmm4 => RegOrMem::new_reg(Xmm(XmmReg::Reg(4)), SIZE_ZMM),
        XedReg::Zmm5 => RegOrMem::new_reg(Xmm(XmmReg::Reg(5)), SIZE_ZMM),
        XedReg::Zmm6 => RegOrMem::new_reg(Xmm(XmmReg::Reg(6)), SIZE_ZMM),
        XedReg::Zmm7 => RegOrMem::new_reg(Xmm(XmmReg::Reg(7)), SIZE_ZMM),
        XedReg::Zmm8 => RegOrMem::new_reg(Xmm(XmmReg::Reg(8)), SIZE_ZMM),
        XedReg::Zmm9 => RegOrMem::new_reg(Xmm(XmmReg::Reg(9)), SIZE_ZMM),
        XedReg::Zmm10 => RegOrMem::new_reg(Xmm(XmmReg::Reg(10)), SIZE_ZMM),
        XedReg::Zmm11 => RegOrMem::new_reg(Xmm(XmmReg::Reg(11)), SIZE_ZMM),
        XedReg::Zmm12 => RegOrMem::new_reg(Xmm(XmmReg::Reg(12)), SIZE_ZMM),
        XedReg::Zmm13 => RegOrMem::new_reg(Xmm(XmmReg::Reg(13)), SIZE_ZMM),
        XedReg::Zmm14 => RegOrMem::new_reg(Xmm(XmmReg::Reg(14)), SIZE_ZMM),
        XedReg::Zmm15 => RegOrMem::new_reg(Xmm(XmmReg::Reg(15)), SIZE_ZMM),
        XedReg::Zmm16 => RegOrMem::new_reg(Xmm(XmmReg::Reg(16)), SIZE_ZMM),
        XedReg::Zmm17 => RegOrMem::new_reg(Xmm(XmmReg::Reg(17)), SIZE_ZMM),
        XedReg::Zmm18 => RegOrMem::new_reg(Xmm(XmmReg::Reg(18)), SIZE_ZMM),
        XedReg::Zmm19 => RegOrMem::new_reg(Xmm(XmmReg::Reg(19)), SIZE_ZMM),
        XedReg::Zmm20 => RegOrMem::new_reg(Xmm(XmmReg::Reg(20)), SIZE_ZMM),
        XedReg::Zmm21 => RegOrMem::new_reg(Xmm(XmmReg::Reg(21)), SIZE_ZMM),
        XedReg::Zmm22 => RegOrMem::new_reg(Xmm(XmmReg::Reg(22)), SIZE_ZMM),
        XedReg::Zmm23 => RegOrMem::new_reg(Xmm(XmmReg::Reg(23)), SIZE_ZMM),
        XedReg::Zmm24 => RegOrMem::new_reg(Xmm(XmmReg::Reg(24)), SIZE_ZMM),
        XedReg::Zmm25 => RegOrMem::new_reg(Xmm(XmmReg::Reg(25)), SIZE_ZMM),
        XedReg::Zmm26 => RegOrMem::new_reg(Xmm(XmmReg::Reg(26)), SIZE_ZMM),
        XedReg::Zmm27 => RegOrMem::new_reg(Xmm(XmmReg::Reg(27)), SIZE_ZMM),
        XedReg::Zmm28 => RegOrMem::new_reg(Xmm(XmmReg::Reg(28)), SIZE_ZMM),
        XedReg::Zmm29 => RegOrMem::new_reg(Xmm(XmmReg::Reg(29)), SIZE_ZMM),
        XedReg::Zmm30 => RegOrMem::new_reg(Xmm(XmmReg::Reg(30)), SIZE_ZMM),
        XedReg::Zmm31 => RegOrMem::new_reg(Xmm(XmmReg::Reg(31)), SIZE_ZMM),
        XedReg::X87Tag => RegOrMem::new_reg(X87(X87Reg::TagWord), B),

        XedReg::St0 | XedReg::St1 | XedReg::St2 | XedReg::St3 | XedReg::St4 | XedReg::St5 | XedReg::St6 | XedReg::St7 => {
            todo!("ST(n) depends on the value of TOP")
        },
        XedReg::Stackpush | XedReg::Stackpop => todo!("Cannot translate stack pushes and pops to a register"),
        XedReg::X87Push | XedReg::X87Pop | XedReg::X87Pop2 => todo!("Cannot translate x87 push/pops to a register"),

        XedReg::X87Control
        | XedReg::X87Status
        | XedReg::X87Opcode
        | XedReg::X87Lastcs
        | XedReg::X87Lastip
        | XedReg::X87Lastds
        | XedReg::X87Lastdp => todo!("various x87 registers"),

        XedReg::Es | XedReg::Cs | XedReg::Ss | XedReg::Ds => todo!("ES/CS/SS/DS are 0 in x64"),
        other => unimplemented!("{other:?} is not mapped by libLISA"),
    }
}

pub fn convert_memory_operand(operand: Operand, access: MemoryAccess<'_>) -> RegOrMem<X64Arch> {
    assert!(access.segment_reg().is_none());
    assert_eq!(operand.operand_size_bits() % 8, 0);

    let mut calculation = AddressComputation {
        offset: access.memory_displacement(),
        terms: [
            AddrTerm::default(),
            AddrTerm::default(),
            AddrTerm::default(),
            AddrTerm::default(),
        ],
    };
    let mut inputs = Vec::new();
    if let Some(reg) = access.base_reg() {
        let loc = convert_reg(reg);
        calculation.terms[inputs.len()] = AddrTerm::single(
            match loc.num_bytes() {
                8 => AddrTermSize::U64,
                other => todo!("Term size {other}"),
            },
            0,
            1,
        );
        inputs.push(loc);
    }

    if let Some(reg) = access.index_reg() {
        let loc = convert_reg(reg);
        calculation.terms[inputs.len()] = AddrTerm::single(
            match loc.num_bytes() {
                8 => AddrTermSize::U64,
                other => todo!("Term size {other}"),
            },
            0,
            access.scale().try_into().unwrap(),
        );
        inputs.push(loc);
    }

    RegOrMem::Memory {
        calculation,
        inputs,
        num_bytes: operand.operand_size_bits() / 8,
    }
}

pub fn convert_operand(operand: Operand, instr: &DecodedInstr) -> RegOrMem<X64Arch> {
    if operand.is_reg() {
        convert_reg(operand.reg().unwrap())
    } else {
        match operand.name() {
            OperandName::Mem0 => convert_memory_operand(operand, instr.memory_accesses().get(0).unwrap()),
            OperandName::Mem1 => convert_memory_operand(operand, instr.memory_accesses().get(1).unwrap()),
            other => todo!("Convert operand with name {other:?}"),
        }
    }
}
