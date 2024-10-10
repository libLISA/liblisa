#![doc(html_no_source)]

use std::cell::RefCell;
use std::iter::{once, repeat_with};
use std::ops::{Range, RangeInclusive};
use std::sync::Arc;

use itertools::Itertools;
use liblisa::arch::x64::{GpReg, X64Arch, X64Flag, X64State, X87};
use liblisa::arch::{Arch, CpuState};
use liblisa::oracle::{MappableArea, Observation, Oracle, OracleError, OracleSource};
use liblisa::state::{Addr, AsSystemState, MemoryState, Page, SystemState};
use liblisa::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};
use liblisa::utils::MapRotated;
use log::warn;
use nix::sched::CpuSet;

use crate::vm::{
    CpuFeatures, DebugRegs, ExtendedRegs, ExtendedRegsWriter, GpRegs, ObservationRequest, Permissions, ResultMemoryAccess, St,
    Vm, VmObserver, XsaveLegacyArea, YmmRegs,
};

#[doc(hidden = "public for benchmarks and tests; use the [`liblisa::Oracle`] interface instead")]
pub mod vm;

#[cfg(test)]
pub mod selftest;

/// Helper function that provides a [`VmOracle`].
pub fn with_oracle<T>(f: impl FnOnce(VmOracle) -> T) -> T {
    let mut vm = Vm::start(1).unwrap();
    f(VmOracle::new(vm.first_observer_only(), Arc::new(vm)))
}

const TRAP_FLAG: u64 = 1 << 8;
#[inline]
fn gpregs_from_x64state(state: &X64State, use_trap_flag: bool) -> GpRegs {
    GpRegs {
        rax: CpuState::<X64Arch>::gpreg(state, GpReg::Rax),
        rbx: CpuState::<X64Arch>::gpreg(state, GpReg::Rbx),
        rcx: CpuState::<X64Arch>::gpreg(state, GpReg::Rcx),
        rdx: CpuState::<X64Arch>::gpreg(state, GpReg::Rdx),
        rbp: CpuState::<X64Arch>::gpreg(state, GpReg::Rbp),
        rsi: CpuState::<X64Arch>::gpreg(state, GpReg::Rsi),
        rdi: CpuState::<X64Arch>::gpreg(state, GpReg::Rdi),
        r8: CpuState::<X64Arch>::gpreg(state, GpReg::R8),
        r9: CpuState::<X64Arch>::gpreg(state, GpReg::R9),
        r10: CpuState::<X64Arch>::gpreg(state, GpReg::R10),
        r11: CpuState::<X64Arch>::gpreg(state, GpReg::R11),
        r12: CpuState::<X64Arch>::gpreg(state, GpReg::R12),
        r13: CpuState::<X64Arch>::gpreg(state, GpReg::R13),
        r14: CpuState::<X64Arch>::gpreg(state, GpReg::R14),
        r15: CpuState::<X64Arch>::gpreg(state, GpReg::R15),
        exception_id: 0,
        error_code: 0,
        rip: CpuState::<X64Arch>::gpreg(state, GpReg::Rip),
        rsp: CpuState::<X64Arch>::gpreg(state, GpReg::Rsp),
        access_address: 0,
        rflags: ((CpuState::<X64Arch>::flag(state, X64Flag::Cf) as u64)
            | ((CpuState::<X64Arch>::flag(state, X64Flag::Pf) as u64) << 2)
            | ((CpuState::<X64Arch>::flag(state, X64Flag::Af) as u64) << 4)
            | ((CpuState::<X64Arch>::flag(state, X64Flag::Zf) as u64) << 6)
            | ((CpuState::<X64Arch>::flag(state, X64Flag::Sf) as u64) << 7)
            | ((CpuState::<X64Arch>::flag(state, X64Flag::Of) as u64) << 11))
            | if use_trap_flag { TRAP_FLAG } else { 0 },
        fs_base: CpuState::<X64Arch>::gpreg(state, GpReg::FsBase),
        gs_base: CpuState::<X64Arch>::gpreg(state, GpReg::GsBase),
    }
}

#[inline]
fn state_from_gpregs(state: &GpRegs) -> X64State {
    let mut result = X64State::default();

    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rax, state.rax);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rbx, state.rbx);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rcx, state.rcx);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rdx, state.rdx);

    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rbp, state.rbp);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rsi, state.rsi);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rdi, state.rdi);

    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R8, state.r8);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R9, state.r9);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R10, state.r10);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R11, state.r11);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R12, state.r12);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R13, state.r13);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R14, state.r14);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::R15, state.r15);

    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rip, state.rip);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::Rsp, state.rsp);

    CpuState::<X64Arch>::set_flag(&mut result, X64Flag::Cf, state.rflags & 1 == 1);
    CpuState::<X64Arch>::set_flag(&mut result, X64Flag::Pf, (state.rflags >> 2) & 1 == 1);
    CpuState::<X64Arch>::set_flag(&mut result, X64Flag::Af, (state.rflags >> 4) & 1 == 1);
    CpuState::<X64Arch>::set_flag(&mut result, X64Flag::Zf, (state.rflags >> 6) & 1 == 1);
    CpuState::<X64Arch>::set_flag(&mut result, X64Flag::Sf, (state.rflags >> 7) & 1 == 1);
    CpuState::<X64Arch>::set_flag(&mut result, X64Flag::Of, (state.rflags >> 11) & 1 == 1);

    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::FsBase, state.fs_base);
    CpuState::<X64Arch>::set_gpreg(&mut result, GpReg::GsBase, state.gs_base);

    result
}

/// An [`Oracle`] that uses a virtual machine and communication via shared memory to observe instruction execution.
pub struct VmOracle {
    observer: VmObserver,

    // Reference to the VM to prevent it from being killed
    _vm: Arc<Vm>,
}

struct BatchSystemStateObservation<const GPREG_ONLY: bool, S: AsSystemState<X64Arch>> {
    index_translation: Box<[u8]>,
    trap_flag_used: bool,
    state: S,
    reserved_range: Range<u64>,
}

const DIVIDE_BY_ZERO_EXCEPTION: u64 = 0x0;
const TRAP_EXCEPTION: u64 = 0x1;
const BREAKPOINT_EXCEPTION: u64 = 0x3;
const INVALID_OPCODE_EXCEPTION: u64 = 0x6;
const PAGE_FAULT_EXCEPTION: u64 = 0xe;
const X87_FP_EXCEPTION: u64 = 0x10;
const SIMD_FP_EXCEPTION: u64 = 0x13;
const ERROR_CODE_INSTRUCTION_FETCH: u64 = 1 << 4;
const TIMEOUT_EXCEPTION: u64 = 0xffff_ffff_ffff_ffff;

fn bits_to_bytes<const N: usize>(bits: u8) -> u64 {
    assert!(N > 0 && N <= 8);

    (0..N)
        .map(|index| (bits as u64 & (1 << index)) << (7 * index))
        .reduce(|a, b| a | b)
        .unwrap()
}

fn bytes_to_bits<const N: usize>(bytes: u64) -> u8 {
    assert!(N > 0 && N <= 8);

    (0..N)
        .map(|index| ((bytes & (1 << (8 * index))) >> (7 * index)) as u8)
        .reduce(|a, b| a | b)
        .unwrap()
}

fn split_status_word(fsw: u16) -> (u64, u32, u8) {
    let exception_flags = bits_to_bytes::<8>(fsw as u8);

    let c = fsw as u32 >> 8;
    let condition_codes = (c & 1) | ((c & 0b10) << 7) | ((c & 0b100) << 14) | ((c & 0b100_0000) << 18);
    let top_of_stack = (c >> 3) as u8 & 0b111;

    (exception_flags, condition_codes, top_of_stack)
}

fn combine_status_word(exception_flags: u64, condition_codes: u32, top_of_stack: u8) -> u16 {
    let e = bytes_to_bits::<8>(exception_flags) as u64;
    let c = condition_codes as u64;
    let t = top_of_stack as u64;
    (e | ((c & 0x1) << 8) | ((c & 0x100) << 1) | ((c & 0x1_0000) >> 6) | ((c & 0x100_0000) >> 10) | ((t & 0b111) << 11)) as u16
}

fn split_control_word(fcw: u16) -> (u64, u8, u8, u8) {
    let f = (fcw & 0x3f) as u8;
    let exception_masks = bits_to_bytes::<6>(f);

    let c = (fcw >> 8) as u8;
    let precision_control = c & 0b11;
    let rounding_control = (c >> 2) & 0b11;
    let infinity = (c >> 4) & 1;

    (exception_masks, precision_control, rounding_control, infinity)
}

fn combine_control_word(exception_masks: u64, precision_control: u8, rounding_control: u8, infinity: u8) -> u16 {
    (bytes_to_bits::<6>(exception_masks) as u64
        | (0x1_0000_0000_0000 >> 42)
        | ((precision_control as u64 & 0b11) << 8)
        | ((rounding_control as u64 & 0b11) << 10)
        | ((infinity as u64 & 1) << 12)) as u16
}

fn split_mxcsr(mxcsr: u32) -> (u64, u64, u8, u8, u8) {
    let exception_flags = bits_to_bytes::<6>(mxcsr as u8);
    let daz = (mxcsr >> 6) as u8 & 1;
    let exception_masks = bits_to_bytes::<6>((mxcsr >> 7) as u8);
    let rounding_control = (mxcsr >> 13) as u8 & 0b11;
    let flush_to_zero = (mxcsr >> 15) as u8 & 1;

    (exception_flags, exception_masks, daz, rounding_control, flush_to_zero)
}

fn combine_mxcsr(exception_flags: u64, exception_masks: u64, daz: u8, rounding_control: u8, flush_to_zero: u8) -> u32 {
    bytes_to_bits::<6>(exception_flags) as u32
        | ((daz as u32 & 1) << 6)
        | ((bytes_to_bits::<6>(exception_masks) as u32) << 7)
        | ((rounding_control as u32 & 0b11) << 13)
        | ((flush_to_zero as u32 & 1) << 15)
}

#[allow(clippy::too_many_arguments)]
fn setup_observe<const GPREGS_ONLY: bool>(
    features: CpuFeatures, index_translation: &mut [u8], state: &SystemState<X64Arch>, gpregs: &mut GpRegs,
    mut extended_regs: ExtendedRegsWriter<'_>, alloc: &mut crate::vm::PageAllocator<'_>, mapper: crate::vm::MemoryMapper,
    reserved_range: &Range<u64>, force_trap_flag: bool,
) -> bool {
    let mut trap_flag_used = state.use_trap_flag || force_trap_flag;
    let rip = CpuState::<X64Arch>::gpreg(state.cpu(), GpReg::Rip);
    // Force use of the trap flag if the page right after does not have a canonical address
    if (0x7FFF_FFFF_F000..0xFFFF_FFFF_FFFF).contains(&rip) {
        trap_flag_used = true;
    }

    // Force use of the trap flag if we've allocated some data on the page directly after the executable page
    let after_executable_page: Page<X64Arch> = Addr::new(rip).page::<X64Arch>().first_address_after_page().page();
    for (addr, ..) in state.memory().iter().skip(1) {
        if addr.page() == after_executable_page {
            trap_flag_used = true;
        }
    }

    // Force use of the trap flag if we cannot allocate a page after the executable page
    trap_flag_used |= reserved_range.contains(&after_executable_page.start_addr().as_u64());

    // trap_flag_used must not be modified from this point on
    let trap_flag_used = trap_flag_used;
    *gpregs = gpregs_from_x64state(state.cpu(), trap_flag_used);

    if !GPREGS_ONLY {
        let x87 = &state.cpu().x87;
        extended_regs.set_legacy(XsaveLegacyArea {
            xmm: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
                .map(|index| u128::from_le_bytes(state.cpu().xmm[index][0..16].try_into().unwrap())),
            // default: 0x37F -> everything masked, pc=11,rc=00,x=0
            control_word: combine_control_word(0x0101_0101_0101, 0b11, 0, 0),
            status_word: combine_status_word(x87.exception_flags, x87.condition_codes, x87.top_of_stack),
            tag_word: x87.tag_word,
            st: x87.fpr.map_rotated(x87.top_of_stack as usize, St::new),
            // default: 0x1f80 -> exceptionflags=000000, daz=0, exceptionmasks=11111, rc=00, ftz=0
            mxcsr: combine_mxcsr(state.cpu().xmm_exception_flags, 0x0101_0101_0101, state.cpu().xmm_daz, 0, 0),
            ..Default::default()
        });

        if features.avx2_available() {
            extended_regs.set_ymm(YmmRegs {
                ymm_hi128: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
                    .map(|index| u128::from_le_bytes(state.cpu().xmm[index][16..32].try_into().unwrap())),
            });
        }
    }

    let mut mapped = FixedBitmapU64::<2>::default();
    let mut n = 0;
    let alloc = RefCell::new(alloc);
    let memory_entries = state.memory().iter().enumerate().filter_map(|(index, (addr, ..))| {
        let page = addr.page::<X64Arch>();

        // This is complicated because there might be multiple mappings to the same page.
        // We need to map those at the same time, to the same page frame.
        if !mapped.get(index) {
            let entries = state
                .memory()
                .iter()
                .enumerate()
                .filter(|(_, (addr, ..))| addr.page() == page)
                .map(|(index, (addr, _, data))| {
                    mapped.set(index);
                    index_translation[index] = n as u8;
                    (addr.as_u64(), &data[..])
                });

            let perms = state
                .memory()
                .iter()
                .filter(|(addr, ..)| addr.page() == page)
                .map(|(_, perms, _)| perms)
                .fold(None, |acc, item| match (acc, item) {
                    (None, perms) => Some(match perms {
                        liblisa::state::Permissions::Read => Permissions::Read,
                        liblisa::state::Permissions::ReadWrite => Permissions::ReadWrite,
                        liblisa::state::Permissions::Execute => Permissions::Executable,
                    }),
                    (Some(Permissions::Executable), liblisa::state::Permissions::Execute) => Some(Permissions::Executable),
                    (Some(Permissions::Read), liblisa::state::Permissions::Read) => Some(Permissions::Read),
                    (Some(Permissions::Read), liblisa::state::Permissions::ReadWrite) => Some(Permissions::ReadWrite),
                    (Some(Permissions::ReadWrite), liblisa::state::Permissions::ReadWrite) => Some(Permissions::ReadWrite),
                    // TODO: These below shouldn't be occurring, but occurs for example when analyzing [FFB424E8000000].
                    (Some(Permissions::Executable), liblisa::state::Permissions::Read) => Some(Permissions::Executable),
                    (Some(Permissions::Read), liblisa::state::Permissions::Execute) => Some(Permissions::Executable),
                    // TODO: [660F6F05C7E90100] tries to place R/W/X on single page.
                    other => panic!("Unexpected permissions combination: {other:?} for state: {state:X?}"),
                })
                .unwrap();

            if reserved_range.contains(&page.start_addr().as_u64()) {
                panic!("Observation tries to map reserved range: {state:?}");
            }

            let mut alloc = alloc.borrow_mut();
            let result = Some(if trap_flag_used || perms != Permissions::Executable {
                alloc.allocate_multi_page(page.start_addr().as_u64(), entries, perms)
            } else {
                alloc.fill_and_allocate_multi_page(page.start_addr().as_u64(), entries, perms)
            });
            drop(alloc);

            n += 1;

            result
        } else {
            None
        }
    });
    if trap_flag_used {
        mapper.set(memory_entries);
    } else {
        mapper.set(
            memory_entries.chain(
                repeat_with(|| {
                    alloc.borrow_mut().fill_and_allocate_page(
                        after_executable_page.start_addr().as_u64(),
                        &[0xCC],
                        Permissions::Executable,
                    )
                })
                .take(1),
            ),
        );
    }

    // println!("Prepared with trap_flag_used={trap_flag_used} and extra page on {:X}", after_executable_page.start_addr().as_u64());

    trap_flag_used
}

fn complete_observation<const GPREG_ONLY: bool>(
    features: CpuFeatures, before: &SystemState<X64Arch>, index_translation: &[u8], gpregs: &GpRegs,
    extended_regs: &ExtendedRegs, new_memory: ResultMemoryAccess, trap_flag_used: bool,
) -> Result<SystemState<X64Arch>, OracleError> {
    // println!("Completing with trap_flag_used={trap_flag_used}");
    let expected_exception = if trap_flag_used {
        TRAP_EXCEPTION
    } else {
        BREAKPOINT_EXCEPTION
    };

    let result = if gpregs.exception_id == expected_exception {
        let memory = before.memory().iter().enumerate().map(|(index, (addr, perms, old_data))| {
            if *perms == liblisa::state::Permissions::ReadWrite {
                let offset = (addr.as_u64() & 0b1111_1111_1111) as usize;
                let mem_index = index_translation[index] as usize;
                (*addr, *perms, new_memory[mem_index][offset..offset + old_data.len()].to_vec())
            } else {
                (*addr, *perms, old_data.clone())
            }
        });

        Ok(SystemState::new(
            {
                let mut cpu: X64State = state_from_gpregs(gpregs);

                if !trap_flag_used {
                    let corrected_rip = CpuState::<X64Arch>::gpreg(&cpu, GpReg::Rip).wrapping_sub(1);
                    CpuState::<X64Arch>::set_gpreg(&mut cpu, GpReg::Rip, corrected_rip);
                }

                if !GPREG_ONLY {
                    let legacy_area = &extended_regs.legacy_area();
                    let xmm = &legacy_area.xmm;
                    // TODO: Better interface for this; Don't use fixed offset
                    if features.avx2_available() {
                        let ymm = unsafe { extended_regs.component::<YmmRegs>(576) };
                        for (index, (lo, hi)) in xmm.iter().zip(ymm.ymm_hi128.iter()).enumerate() {
                            let lo = lo.to_le_bytes();
                            let hi = hi.to_le_bytes();
                            let target = &mut cpu.xmm[index];
                            target[0..16].copy_from_slice(&lo);
                            target[16..32].copy_from_slice(&hi);
                        }
                    } else {
                        for (index, lo) in xmm.iter().enumerate() {
                            let lo = lo.to_le_bytes();
                            let target = &mut cpu.xmm[index];
                            target[0..16].copy_from_slice(&lo);
                            target[16..32].copy_from_slice(&before.cpu().xmm[index][16..32]);
                        }
                    }

                    let y = &mut cpu;
                    (y.xmm_exception_flags, _, y.xmm_daz, _, _) = split_mxcsr(legacy_area.mxcsr);

                    let (exception_flags, condition_codes, top_of_stack) = split_status_word(legacy_area.status_word);
                    let (..) = split_control_word(legacy_area.control_word);
                    cpu.x87 = X87 {
                        fpr: legacy_area.st.map_rotated(8 - top_of_stack as usize, |item| item.bytes()),
                        top_of_stack,
                        exception_flags,
                        condition_codes,
                        tag_word: legacy_area.tag_word,
                    };
                }

                cpu
            },
            MemoryState::new(memory),
        ))
    } else {
        Err(match gpregs.exception_id {
            _ if !trap_flag_used && gpregs.rip != CpuState::<X64Arch>::gpreg(before.cpu(), GpReg::Rip) => {
                // TODO: Remove this error now that we can handle it!
                warn!(
                    "Multiple instructions executed from: {:?} to {:#X?} (trap_flag_used={}) resulting memory = {:02X?}",
                    before,
                    gpregs,
                    trap_flag_used,
                    new_memory.iter().collect::<Vec<_>>()
                );
                OracleError::MultipleInstructionsExecuted
            },
            // Trap exception while we didn't use the trap flag. Maybe it's the int 1 instruction? (in which case, we should force use of the trap flag)
            TRAP_EXCEPTION => OracleError::MultipleInstructionsExecuted,
            INVALID_OPCODE_EXCEPTION => OracleError::InvalidInstruction,
            PAGE_FAULT_EXCEPTION if gpregs.error_code & ERROR_CODE_INSTRUCTION_FETCH == ERROR_CODE_INSTRUCTION_FETCH => {
                OracleError::InstructionFetchMemoryAccess(Addr::new(gpregs.access_address))
            },
            PAGE_FAULT_EXCEPTION => OracleError::MemoryAccess(Addr::new(gpregs.access_address)),
            DIVIDE_BY_ZERO_EXCEPTION | SIMD_FP_EXCEPTION | X87_FP_EXCEPTION => OracleError::ComputationError,
            TIMEOUT_EXCEPTION => OracleError::Timeout,
            _ => OracleError::GeneralFault,
        })
    };

    result
}

impl<const GPREGS_ONLY: bool, S: AsSystemState<X64Arch>> ObservationRequest for BatchSystemStateObservation<GPREGS_ONLY, S> {
    type Result = (S, Result<SystemState<X64Arch>, OracleError>);

    fn setup(
        &mut self, features: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: crate::vm::DebugRegsWriter<'_>,
        extended_regs: ExtendedRegsWriter<'_>, alloc: &mut crate::vm::PageAllocator<'_>, mapper: crate::vm::MemoryMapper<'_>,
    ) {
        self.trap_flag_used = setup_observe::<GPREGS_ONLY>(
            features,
            &mut self.index_translation,
            self.state.as_system_state().as_ref(),
            gpregs,
            extended_regs,
            alloc,
            mapper,
            &self.reserved_range,
            false,
        );
    }

    fn result(
        self, features: CpuFeatures, gpregs: &GpRegs, _debug_regs: &DebugRegs, extended_regs: &ExtendedRegs,
        memory: ResultMemoryAccess,
    ) -> Self::Result {
        let result = complete_observation::<GPREGS_ONLY>(
            features,
            self.state.as_system_state().as_ref(),
            &self.index_translation,
            gpregs,
            extended_regs,
            memory,
            self.trap_flag_used,
        );
        (self.state, result)
    }
}

struct MemoryAccessDebugScan<'r> {
    state: &'r SystemState<X64Arch>,
    reserved_range: Range<u64>,
    region: RangeInclusive<u64>,
}

impl ObservationRequest for MemoryAccessDebugScan<'_> {
    type Result = Result<[Option<u64>; 4], OracleError>;

    fn setup(
        &mut self, features: CpuFeatures, gpregs: &mut GpRegs, debug_regs: crate::vm::DebugRegsWriter<'_>,
        extended_regs: ExtendedRegsWriter<'_>, alloc: &mut crate::vm::PageAllocator<'_>, mapper: crate::vm::MemoryMapper<'_>,
    ) {
        setup_observe::<false>(
            features,
            &mut [0; 80],
            self.state,
            gpregs,
            extended_regs,
            alloc,
            mapper,
            &self.reserved_range,
            true,
        );
        let step = (*self.region.end() - *self.region.start() + 1) / 4;
        debug_regs.set(DebugRegs {
            dr0: *self.region.start(),
            dr1: *self.region.start() + step,
            dr2: *self.region.start() + step * 2,
            dr3: *self.region.start() + step * 3,
            dr6: 0,
            dr7: match step {
                8 => 0b1011_1011_1011_1011_0000_0000_1111_1111,
                1 => 0b0011_0011_0011_0011_0000_0000_1111_1111,
                _ => panic!("Step size not supported: {step}"),
            },
        });
    }

    fn result(
        self, _features: CpuFeatures, gpregs: &GpRegs, debug_regs: &DebugRegs, _extended_regs: &ExtendedRegs,
        _memory: ResultMemoryAccess,
    ) -> Self::Result {
        if gpregs.exception_id == TRAP_EXCEPTION {
            // println!("dr6 = {:X} for {:X?}", debug_regs.dr6, self.region);
            let step = (*self.region.end() - *self.region.start() + 1) / 4;
            let results = [0, 1, 2, 3].map(|i| {
                if (debug_regs.dr6 >> i) & 1 != 0 {
                    let full_range = self.region.start() + step * i..=self.region.start() + step * i + (step - 1);
                    Some(*full_range.start())
                } else {
                    None
                }
            });

            Ok(results)
        } else {
            // TODO: Store a reference outcome and just compare with that instead
            println!("Found: {gpregs:?} {debug_regs:?} when doing memory scan for {:?}", self.state);
            // for data in _memory.iter() {
            //     // let offset = (addr.as_u64() & 0b1111_1111_1111) as usize;
            //     // let mem_index = self.index_translation[index];
            //     // let data = &_memory[mem_index][offset..offset + old_data.len()];

            //     println!("Memory: {:02X?}", data);
            // }

            Err(OracleError::Unreliable)
            // panic!("Did not encounter a trap exception after executing the instruction. Resulting GpRegs: {:#X?} Make sure you've set the trap flag. Memory access scanning (careful observation) does not support executing more than one instruction at the same time.", gpregs);
        }
    }
}

/// The [`MappableArea`] that can be mapped by [`VmOracle`].
#[derive(Clone)]
pub struct VmMappableArea {
    reserved_range: Range<u64>,
}

impl std::fmt::Debug for VmMappableArea {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:X}..0x{:X}", self.reserved_range.start, self.reserved_range.end)
    }
}

impl MappableArea for VmMappableArea {
    fn can_map(&self, addr: Addr) -> bool {
        let addr = addr.as_u64();
        if (addr >> 48) == 0xffff * ((addr >> 47) & 1) {
            !self.reserved_range.contains(&addr)
        } else {
            false
        }
    }
}

impl Oracle<X64Arch> for VmOracle {
    type MappableArea = VmMappableArea;
    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool = false;

    fn mappable_area(&self) -> Self::MappableArea {
        VmMappableArea {
            reserved_range: self.observer.reserved_range(),
        }
    }

    fn page_size(&mut self) -> u64 {
        4096
    }

    fn observe(&mut self, before: &SystemState<X64Arch>) -> Result<SystemState<X64Arch>, OracleError> {
        self.batch_observe_iter(once(before)).next().unwrap().1
    }

    fn scan_memory_accesses(&mut self, before: &SystemState<X64Arch>) -> Result<Vec<Addr>, OracleError> {
        let reserved_range = self.observer.reserved_range();
        let page_size = Oracle::<X64Arch>::page_size(self);
        let mut pages_seen = Vec::new();
        let results = self.observer.batch_iter(
            before
                .memory()
                .iter()
                .filter_map(|(mapped_addr, ..)| {
                    let page_address = mapped_addr.align_to_page_start(X64Arch::PAGE_BITS);
                    if pages_seen.contains(&page_address) {
                        None
                    } else {
                        pages_seen.push(page_address);
                        Some(page_address)
                    }
                })
                .flat_map(|page_address| {
                    (page_address.as_u64()..=(page_address + (page_size - 1)).as_u64())
                        .step_by(32)
                        .map(|addr| MemoryAccessDebugScan {
                            state: before,
                            reserved_range: reserved_range.clone(),
                            region: addr..=addr + 31,
                        })
                }),
        );

        let found_big = results
            .map_ok(|addrs| IntoIterator::into_iter(addrs).flatten())
            .flatten_ok()
            .collect::<Result<Vec<_>, _>>()?;

        let results = self.observer.batch_iter(found_big.into_iter().flat_map(|addr| {
            [
                MemoryAccessDebugScan {
                    state: before,
                    reserved_range: reserved_range.clone(),
                    region: addr..=addr + 3,
                },
                MemoryAccessDebugScan {
                    state: before,
                    reserved_range: reserved_range.clone(),
                    region: addr + 4..=addr + 7,
                },
            ]
        }));

        results
            .map_ok(|addrs| IntoIterator::into_iter(addrs).flatten())
            .flatten_ok()
            .map_ok(Addr::new)
            .collect::<Result<Vec<_>, _>>()
    }

    fn debug_dump(&mut self) {
        self.observer.debug_dump();
        println!("{:#?}", self.observer);
    }

    fn restart(&mut self) {
        // TODO: Do we need this?
    }

    fn kill(self) {
        drop(self)
    }

    fn batch_observe_iter<'a, S: AsSystemState<X64Arch> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, X64Arch>> {
        let reserved_range = self.observer.reserved_range();
        self.observer.batch_iter(CreateRequests::<false, _, _> {
            iter: states.into_iter(),
            reserved_range,
        })
    }

    fn batch_observe_gpreg_only_iter<'a, S: AsSystemState<X64Arch> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, X64Arch>> {
        let reserved_range = self.observer.reserved_range();
        self.observer.batch_iter(CreateRequests::<true, _, _> {
            iter: states.into_iter(),
            reserved_range,
        })
    }
}

struct CreateRequests<const GPREG_ONLY: bool, S: AsSystemState<X64Arch>, I: Iterator<Item = S>> {
    iter: I,
    reserved_range: Range<u64>,
}

impl<const GPREG_ONLY: bool, S: AsSystemState<X64Arch>, I: Iterator<Item = S>> Iterator for CreateRequests<GPREG_ONLY, S, I> {
    type Item = BatchSystemStateObservation<GPREG_ONLY, S>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|state| BatchSystemStateObservation {
            index_translation: vec![0; state.num_memory_mappings()].into_boxed_slice(),
            state,
            reserved_range: self.reserved_range.clone(),
            trap_flag_used: false,
        })
    }
}

impl VmOracle {
    pub fn new(observer: VmObserver, vm: Arc<Vm>) -> VmOracle {
        VmOracle {
            observer,
            _vm: vm,
        }
    }
}

/// Implements [`OracleSource`] and returns [`VmOracle`]s.
pub struct VmOracleSource {
    affinity: Option<CpuSet>,
    num: usize,
}

impl VmOracleSource {
    pub fn new(affinity: Option<CpuSet>, num: usize) -> Self {
        Self {
            affinity,
            num,
        }
    }
}

impl OracleSource for VmOracleSource {
    type Oracle = VmOracle;

    fn start(&self) -> Vec<Self::Oracle> {
        let mut o = Vm::options();
        if let Some(affinity) = self.affinity {
            o.set_affinity(affinity);
        }

        let mut vm = o.start(self.num).unwrap();
        let observers = vm.observers().collect::<Vec<_>>();

        let vm = Arc::new(vm);
        observers
            .into_iter()
            .map(|observer| VmOracle::new(observer, vm.clone()))
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::split_status_word;
    use crate::{bits_to_bytes, bytes_to_bits, combine_control_word, combine_status_word};

    #[test]
    pub fn test_bytes_bits_conversion() {
        let cases = [
            (0x0000_0000_0000_0000, 0b00000000),
            (0x0000_0000_0000_0001, 0b00000001),
            (0x0000_0000_0000_0100, 0b00000010),
            (0x0000_0000_0001_0000, 0b00000100),
            (0x0000_0000_0100_0000, 0b00001000),
            (0x0000_0001_0000_0000, 0b00010000),
            (0x0000_0100_0000_0000, 0b00100000),
            (0x0001_0000_0000_0000, 0b01000000),
            (0x0100_0000_0000_0000, 0b10000000),
            (0x0100_0101_0001_0000, 0b10110100),
            (0x0101_0101_0101_0101, 0b11111111),
        ];

        for (bytes, bits) in cases {
            let r = bytes_to_bits::<8>(bytes);
            assert_eq!(r, bits, "bytes({bytes:X}) should be bits({bits:b}) but found bits({r:b})");

            let r = bits_to_bytes::<8>(bits);
            assert_eq!(r, bytes, "bits({bits:b}) should be bytes({bytes:X}) but found bytes({r:X})");
        }
    }

    #[test]
    pub fn test_split_status_word() {
        for fsw in 0..=u16::MAX / 2 {
            let (a, b, c) = split_status_word(fsw);
            let new_fsw = combine_status_word(a, b, c);
            assert_eq!(fsw, new_fsw);
        }
    }

    #[test]
    pub fn test_combine_control_word() {
        let r = combine_control_word(0x0101_0101_0101, 0b11, 0, 0);
        println!("{r:X?}");
        assert_eq!(r, 0x37F);
    }
}
