use core::{arch::{asm, naked_asm}, ptr};
use liblisa_x64_observer_shmqueue::regs::GpRegs;

use crate::gdt;

const MSR_FS_BASE: u32 = 0xC000_0100;
const MSR_GS_BASE: u32 = 0xC000_0101;

unsafe fn msr_get(msr: u32) -> u64 {
    let a: u32;
    let b: u32;
    asm!(
        "wrmsr",
        in("ecx") msr,
        out("edx") a,
        out("eax") b,
    );

    ((a as u64) << 32) | (b as u64)
}
 
unsafe fn msr_set(msr: u32, val: u64) {
    asm!(
        "wrmsr",
        in("ecx") msr,
        in("edx") (val >> 32) as u32,
        in("eax") val as u32,
    );
}

fn set_fsgs(fs: u64, gs: u64) {
    unsafe {
        msr_set(MSR_FS_BASE, fs);
        msr_set(MSR_GS_BASE, gs);
    }
}

#[derive(Default)]
#[repr(C, packed)]
pub struct KernelGpRegs {
    rsp: u64,
    rbp: u64,
    rbx: u64,
    rip: u64,
}

pub static mut RESTORE_STATE: KernelGpRegs = KernelGpRegs {
    rsp: 0,
    rbp: 0,
    rbx: 0,
    rip: 0,
};

pub unsafe fn jmp_to_usermode(regs: &mut GpRegs) {
    const INTERRUPT_ENABLE_FLAG: u64 = 0x200;

    GPREGS_WRITE_TARGET = regs as *mut _;
    // serial_println!("Approximate target RIP = 0x{:x}", x86_64::registers::read_rip() + 40u64);

    let (cs_idx, ds_idx) = gdt::set_usermode_segs();

    set_fsgs(regs.fs_base, regs.gs_base);

    asm!(
        // ===========================================
        // STEP 1: backup current registers (rsp, rbp, rbx, return rip)
        // ===========================================
        "lea r8, 2f[rip]", // load the jump offset
        "mov [rip + {restore_state} + 0x00], rsp",
        "mov [rip + {restore_state} + 0x08], rbp",
        "mov [rip + {restore_state} + 0x10], rbx",
        "mov [rip + {restore_state} + 0x18], r8",

        // ===========================================
        // STEP 2: Prepare the stack for the jump to userspace
        // ===========================================
        "push rax", // new stack segment
        "push rsi", // new rsp
        "push r12", // new rflags
        "push rdx", // new code segment
        "push rdi", // new rip

        // ===========================================
        // STEP 3: Load registers
        // ===========================================
        // We use r15 to store the pointer to the GpRegs structure, so rbx needs to be set last
        "mov r15, [rip + {target}]",

        "mov rax, [r15 + {rax_offset}]",
        "mov rbx, [r15 + {rbx_offset}]",
        "mov rcx, [r15 + {rcx_offset}]",
        "mov rdx, [r15 + {rdx_offset}]",
        // 0x20: rsp is pushed above and handled by iret
        "mov rbp, [r15 + {rbp_offset}]",
        "mov rsi, [r15 + {rsi_offset}]",
        "mov rdi, [r15 + {rdi_offset}]",
        "mov r8, [r15 + {r8_offset}]",
        "mov r9, [r15 + {r9_offset}]",
        "mov r10, [r15 + {r10_offset}]",
        "mov r11, [r15 + {r11_offset}]",
        "mov r12, [r15 + {r12_offset}]",
        "mov r13, [r15 + {r13_offset}]",
        "mov r14, [r15 + {r14_offset}]",

        // set r15 last
        "mov r15, [r15 + {r15_offset}]",

        "iretq",
        "2:",

        target = sym GPREGS_WRITE_TARGET,
        restore_state = sym RESTORE_STATE,
        rax_offset = const memoffset::offset_of!(GpRegs, rax),
        rbx_offset = const memoffset::offset_of!(GpRegs, rbx),
        rcx_offset = const memoffset::offset_of!(GpRegs, rcx),
        rdx_offset = const memoffset::offset_of!(GpRegs, rdx),
        rbp_offset = const memoffset::offset_of!(GpRegs, rbp),
        rsi_offset = const memoffset::offset_of!(GpRegs, rsi),
        rdi_offset = const memoffset::offset_of!(GpRegs, rdi),
        r8_offset = const memoffset::offset_of!(GpRegs, r8),
        r9_offset = const memoffset::offset_of!(GpRegs, r9),
        r10_offset = const memoffset::offset_of!(GpRegs, r10),
        r11_offset = const memoffset::offset_of!(GpRegs, r11),
        r12_offset = const memoffset::offset_of!(GpRegs, r12),
        r13_offset = const memoffset::offset_of!(GpRegs, r13),
        r14_offset = const memoffset::offset_of!(GpRegs, r14),
        r15_offset = const memoffset::offset_of!(GpRegs, r15),
        inout("rdi") (*GPREGS_WRITE_TARGET).rip => _,
        inout("rsi") (*GPREGS_WRITE_TARGET).rsp => _,
        inout("rdx") cs_idx => _,
        inout("rax") ds_idx => _,
        inout("r12") (*GPREGS_WRITE_TARGET).rflags | INTERRUPT_ENABLE_FLAG => _,

        // clobber all the other registers
        out("rcx") _,
        out("r8") _,
        out("r9") _,
        out("r10") _,
        out("r11") _,
        out("r13") _,
        out("r14") _,
        out("r15") _,

        // can't clobber rsp, rbp, rip
    );

    RESTORE_STATE.rsp = 0;
}

static mut GPREGS_WRITE_TARGET: *mut GpRegs = ptr::null_mut();

#[macro_export]
macro_rules! generate_interrupt_entry {
    ($id:literal: $name:ident) => {
        #[naked]
        unsafe extern "C" fn $name() {
            naked_asm!(
                "cld",
                "push 0",
                "push {id}",
                "jmp {c}",
                id = const $id,
                c = sym crate::userspace::handle_interrupt,
            )
        }
    };
    ($id:literal: $name:ident => $kernel_handler:path) => {
        #[naked]
        unsafe extern "C" fn $name() {
            fn _verify() {
                let _: extern "x86-interrupt" fn(stack_frame: InterruptStackFrame) = $kernel_handler;
            }

            naked_asm!(
                // If we're currently not in userspace, bail out to the kernel handler
                "cmp qword ptr [rip + {RESTORE_STATE}], 0",
                "jnz 3f",
                "jmp {handler}",

                "3:",
                "cld",
                "push 0",
                "push {id}",
                "jmp {c}",
                id = const $id,
                c = sym crate::userspace::handle_interrupt,
                RESTORE_STATE = sym crate::userspace::RESTORE_STATE,
                handler = sym $kernel_handler,
            )
        }
    };
    ($id:literal(with_error=$error_ty:ty): $name:ident => $kernel_handler:path) => {
        #[naked]
        unsafe extern "C" fn $name() {
            fn _verify() {
                let _: extern "x86-interrupt" fn(stack_frame: InterruptStackFrame, error_code: $error_ty) = $kernel_handler;
            }

            naked_asm!(
                // If we're currently not in userspace, bail out to the kernel handler
                "cmp qword ptr [rip + {RESTORE_STATE}], 0",
                "jnz 3f",
                "jmp {handler}",

                "3:",
                "push {id}",
                "jmp {c}",
                id = const $id,
                c = sym crate::userspace::handle_interrupt,
                RESTORE_STATE = sym crate::userspace::RESTORE_STATE,
                handler = sym $kernel_handler,
            )
        }
    }
}

#[no_mangle]
#[naked]
pub unsafe extern "C" fn handle_interrupt() {
    // When entering this function, the stack should look like:
    // - [pop'd] original rbx
    // - [+0x00] exception_id
    // - [+0x08] error_code
    // - [+0x10] rip
    // - [+0x18] cs
    // - [+0x20] rflags
    // - [+0x28] rsp
    // - [+0x30] ss
    naked_asm!(
        // push rbx so we have a scratch register for the GpRegs pointer.
        // rbx will point to the memory region where we store the GPREGS.
        "push rbx",
        "mov rbx, [rip + {target}]",

        // store rax
        "mov [rbx + {rax_offset}], rax",

        // store rbx
        "pop rax",
        "mov [rbx + {rbx_offset}], rax",
        "mov [rbx + {rcx_offset}], rcx",
        "mov [rbx + {rdx_offset}], rdx",
        "mov [rbx + {rbp_offset}], rbp",
        "mov [rbx + {rsi_offset}], rsi",
        "mov [rbx + {rdi_offset}], rdi",

        "mov [rbx + {r8_offset}], r8",
        "mov [rbx + {r9_offset}], r9",
        "mov [rbx + {r10_offset}], r10",
        "mov [rbx + {r11_offset}], r11",
        "mov [rbx + {r12_offset}], r12",
        "mov [rbx + {r13_offset}], r13",
        "mov [rbx + {r14_offset}], r14",
        "mov [rbx + {r15_offset}], r15",

        // Pull the special registers from the stack
        // Loads and stores below are ordered so that memory is accessed in a cache-friendly way
        // Here we are interleaving multiple different operations.
        // The aim is to not have a data-dependency between two consecutive instructions.
        // This should allow the CPU to schedule operations more efficiently
        "mov rax, [rsp + 0x00]", // rax = exception ID
        "mov rcx, [rsp + 0x08]", // rcx = error code
        "mov rdx, [rsp + 0x10]", // rdx = RIP
        "mov rdi, [rsp + 0x20]", // rdi = rflags
        "mov rsi, [rsp + 0x28]", // rsi = rsp

        "mov [rbx + {exception_id_offset}], rax",
        "mov [rbx + {error_code_offset}], rcx",
        "mov [rbx + {rip_offset}], rdx",
        "mov [rbx + {rsp_offset}], rsi",

        "cmp rax, 0xE",
        "jnz 5f",
        // only set access_address when we actually encounter a memory access error
        // otherwise cr2 might still contain old data
        "mov rcx, cr2",
        "mov [rbx + {access_address_offset}], rcx",
        "5:",

        // special case rflags:
        "mov [rbx + {rflags_offset}], rdi",

        // Restore original rsp, rbp & rbx and jump back to original rip
        "mov rsp, [rip + {restore_state} + 0x00]",
        "mov rbp, [rip + {restore_state} + 0x08]",
        "mov rbx, [rip + {restore_state} + 0x10]",
        "jmp [rip + {restore_state} + 0x18]",

        target = sym GPREGS_WRITE_TARGET,
        restore_state = sym RESTORE_STATE,
        rax_offset = const memoffset::offset_of!(GpRegs, rax),
        rbx_offset = const memoffset::offset_of!(GpRegs, rbx),
        rcx_offset = const memoffset::offset_of!(GpRegs, rcx),
        rdx_offset = const memoffset::offset_of!(GpRegs, rdx),
        rsp_offset = const memoffset::offset_of!(GpRegs, rsp),
        rbp_offset = const memoffset::offset_of!(GpRegs, rbp),
        rsi_offset = const memoffset::offset_of!(GpRegs, rsi),
        rdi_offset = const memoffset::offset_of!(GpRegs, rdi),
        r8_offset = const memoffset::offset_of!(GpRegs, r8),
        r9_offset = const memoffset::offset_of!(GpRegs, r9),
        r10_offset = const memoffset::offset_of!(GpRegs, r10),
        r11_offset = const memoffset::offset_of!(GpRegs, r11),
        r12_offset = const memoffset::offset_of!(GpRegs, r12),
        r13_offset = const memoffset::offset_of!(GpRegs, r13),
        r14_offset = const memoffset::offset_of!(GpRegs, r14),
        r15_offset = const memoffset::offset_of!(GpRegs, r15),
    
        rip_offset = const memoffset::offset_of!(GpRegs, rip),
        rflags_offset = const memoffset::offset_of!(GpRegs, rflags),
        exception_id_offset = const memoffset::offset_of!(GpRegs, exception_id),
        error_code_offset = const memoffset::offset_of!(GpRegs, error_code),
        access_address_offset = const memoffset::offset_of!(GpRegs, access_address),
    )
}