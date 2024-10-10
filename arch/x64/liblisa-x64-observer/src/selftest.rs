use std::fmt::Debug;
use std::iter::{self, once, repeat};
use std::time::Duration;

use liblisa_x64_observer_shmqueue::frame::command::{ExtendedRegs, Permissions};
use liblisa_x64_observer_shmqueue::regs::{DebugRegs, GpRegs, XsaveLegacyArea};
use rand::Rng;

use crate::vm::{
    CpuFeatures, DebugRegsWriter, ExtendedRegsWriter, MemoryMapper, ObservationRequest, PageAllocator, ResultMemoryAccess, Vm,
};

#[derive(Clone)]
pub struct TestCase<'instr> {
    name: &'static str,
    input: GpRegs,
    expected_output: GpRegs,
    instr: &'instr [u8],
    mem: Vec<(u64, &'static [u8], &'static [u8], Permissions)>,
    debug_regs: Option<(DebugRegs, DebugRegs)>,
    xmm: Option<([u128; 16], [u128; 16])>,
}

impl Default for TestCase<'_> {
    fn default() -> Self {
        Self {
            name: "<MISSING NAME>",
            input: Default::default(),
            expected_output: Default::default(),
            instr: &[0xCC],
            mem: Default::default(),
            debug_regs: Default::default(),
            xmm: Default::default(),
        }
    }
}

pub struct DisplayDiff {
    left: u64,
    right: u64,
}

impl Debug for DisplayDiff {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:x} <=> 0x{:x}", self.left, self.right)
    }
}

pub struct DiffGpRegs<'r> {
    left: &'r GpRegs,
    right: &'r GpRegs,
}

impl<'r> DiffGpRegs<'r> {
    pub fn new(left: &'r GpRegs, right: &'r GpRegs) -> Self {
        DiffGpRegs {
            left,
            right,
        }
    }
}

pub struct DiffDebugRegs<'r> {
    left: &'r DebugRegs,
    right: &'r DebugRegs,
}

impl<'r> DiffDebugRegs<'r> {
    pub fn new(left: &'r DebugRegs, right: &'r DebugRegs) -> Self {
        DiffDebugRegs {
            left,
            right,
        }
    }
}

macro_rules! diff_fields {
    ($debug:ident ($left:expr => $right:expr) in [$($field:ident),* $(,)*]) => {
        let left = $left;
        let right = $right;
        $(
            if left.$field != right.$field {
                $debug.field(stringify!($field), &DisplayDiff {
                    left: left.$field,
                    right: right.$field,
                });
            }
        )*
    };
}

impl Debug for DiffGpRegs<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut w = f.debug_struct("GpRegs");

        diff_fields!(w (self.left => self.right) in [
            rax, rbx, rcx, rdx,
            rsp, rbp, rsi, rdi,
            r8, r9, r10, r11,
            r12, r13, r14, r15,
            rip, rflags,
            exception_id,
            error_code,
            access_address,
        ]);

        w.finish()
    }
}

impl Debug for DiffDebugRegs<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut w = f.debug_struct("DebugRegs");

        diff_fields!(w (self.left => self.right) in [
            dr0, dr1, dr2, dr3,
            dr6, dr7,
        ]);

        w.finish()
    }
}

impl ObservationRequest for TestCase<'_> {
    type Result = ();

    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, debug_regs: DebugRegsWriter, mut extended_regs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mappings: MemoryMapper,
    ) {
        *gpregs = self.input;
        mappings.set(
            once(alloc.allocate_page(self.input.rip, self.instr, Permissions::Executable)).chain(
                self.mem
                    .iter()
                    .map(|&(addr, data, _, perms)| alloc.allocate_page(addr, data, perms)),
            ),
        );

        if let Some((initial, _)) = self.debug_regs {
            debug_regs.set(initial);
        }

        if let Some((initial, _)) = self.xmm {
            extended_regs.set_legacy(XsaveLegacyArea {
                xmm: initial,
                ..Default::default()
            });
        }
    }

    fn result(
        self, _: CpuFeatures, gpregs: &GpRegs, debug_regs: &DebugRegs, extended_regs: &ExtendedRegs, memory: ResultMemoryAccess,
    ) {
        if &self.expected_output != gpregs {
            std::thread::sleep(Duration::from_secs(5));
            panic!(
                "Error in \"{}\":\nObservation of {:02X?} produced incorrect results. State change:{:#X?}",
                self.name,
                self.instr,
                DiffGpRegs::new(&self.expected_output, gpregs)
            );
        }

        assert_eq!(&self.expected_output, gpregs);

        const PAGE_OFFSET_MASK: u64 = 0b1111_1111_1111;
        for ((addr, _, expected, _), page) in self.mem.iter().zip(memory.iter().skip(1)) {
            let offset = addr & PAGE_OFFSET_MASK;
            let actual = &page[offset as usize..offset as usize + expected.len()];

            if *expected != actual {
                panic!(
                    "Error in \"{}\":\nExpected memory at 0x{:X} to be {:02?} but found {:02?}",
                    self.name, addr, expected, actual
                );
            }
        }

        if let Some((_, expected)) = &self.debug_regs {
            if expected != debug_regs {
                panic!(
                    "Error in \"{}\":\nObservation of {:02X?} produced incorrect results in debug registers. State change:{:#X?}",
                    self.name,
                    self.instr,
                    DiffDebugRegs::new(expected, debug_regs)
                );
            }
        }

        if let Some((_, expected)) = &self.xmm {
            if expected != &extended_regs.legacy_area().xmm {
                panic!(
                    "Error in \"{}\":\nObservation of {:02X?} produced incorrect results in XMM registers. State change:{:#X?}",
                    self.name,
                    self.instr,
                    (expected, extended_regs.legacy_area().xmm)
                );
            }
        }
    }
}

const CARRY_FLAG: u64 = 1 << 0;
const PARITY_FLAG: u64 = 1 << 2;
const AUXILIARY_CARRY_FLAG: u64 = 1 << 4;
const SIGN_FLAG: u64 = 1 << 7;
const TRAP_FLAG: u64 = 1 << 8;
const DEFAULT_FLAGS: u64 = 0x302;

const DIVIDE_BY_ZERO_EXCEPTION: u64 = 0x0;
const TRAP_EXCEPTION: u64 = 0x1;
const BREAKPOINT_EXCEPTION: u64 = 0x3;
// const BOUND_RANGE_EXCEEDED_EXCEPTION: u64 = 0x5;
const INVALID_OPCODE_EXCEPTION: u64 = 0x6;
const STACK_SEGMENT_FAULT: u64 = 0xc;
const GENERAL_PROTECTION_FAULT_EXCEPTION: u64 = 0xd;
const PAGE_FAULT_EXCEPTION: u64 = 0xe;
const TIMEOUT_EXCEPTION: u64 = 0xffffffff_ffffffff;
// const FLOATING_POINT_EXCEPTION: u64 = 0x10;
// Needs CR0.AM=1 and RFLAGS.AC=1: const ALIGNMENT_CHECK_EXCEPTION: u64 = 0x11;
// const SIMD_FLOATING_POINT_EXCEPTION: u64 = 0x13;

#[test]
// Verify that we can map executable code anywhere except for the reserved region.
pub fn exec_memory_mapping() {
    let mut vm = Vm::start(1).unwrap();
    vm.first_observer_only().batch(
        [
            TestCase {
                // add rax, rbx
                name: "Execute from positive memory",
                instr: &[0x48, 0x01, 0xD8],
                input: GpRegs {
                    rax: 0x10,
                    rbx: 0x1234321,
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234331,
                    rbx: 0x1234321,
                    rip: 0x1003,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // add rax, rbx
                name: "Execute from negative memory",
                instr: &[0x48, 0x01, 0xD8],
                input: GpRegs {
                    rax: 0x1122334455667788,
                    rbx: 0x8877665544332211,
                    rip: 0xffffffff12340000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x9999999999999999,
                    rbx: 0x8877665544332211,
                    rip: 0xffffffff12340003,
                    rflags: DEFAULT_FLAGS | PARITY_FLAG | SIGN_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // add rax, rbx
                name: "Execute instruction aligned near the end of the page",
                instr: &[0x48, 0x01, 0xD8],
                input: GpRegs {
                    rax: 0x10,
                    rbx: 0x20,
                    rip: 0xffd,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x30,
                    rbx: 0x20,
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS | PARITY_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}

#[test]
// Verify that we can map executable code anywhere except for the reserved region.
pub fn memory_modify() {
    let mut vm = Vm::start(1).unwrap();
    let mut o = vm.first_observer_only();
    let reserved_range = o.reserved_range();
    o.batch(
        [
            TestCase {
                // mov qword ptr [rax], rbx
                name: "write to ReadWrite memory is OK",
                instr: &[0x48, 0x89, 0x18],
                input: GpRegs {
                    rax: 0x1234000,
                    rbx: 0x1122334455667788,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234000,
                    rbx: 0x1122334455667788,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234000,
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    Permissions::ReadWrite,
                )],
                ..Default::default()
            },
            TestCase {
                // mov qword ptr [rax], rbx
                name: "write at offset is OK",
                instr: &[0x48, 0x89, 0x18],
                input: GpRegs {
                    rax: 0x1234999,
                    rbx: 0x1122334455667788,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234999,
                    rbx: 0x1122334455667788,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234999,
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    Permissions::ReadWrite,
                )],
                ..Default::default()
            },
            TestCase {
                // mov qword ptr [rax], rbx
                name: "write to Read memory gives #PF",
                instr: &[0x48, 0x89, 0x18],
                input: GpRegs {
                    rax: 0x1234000,
                    rbx: 0x1122334455667788,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234000,
                    rbx: 0x1122334455667788,
                    rflags: 0x10302,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    error_code: 0x7,
                    access_address: 0x1234000,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234000,
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    Permissions::Read,
                )],
                ..Default::default()
            },
            TestCase {
                // mov qword ptr [rax], rbx
                name: "write to Executable memory gives #PF",
                instr: &[0x48, 0x89, 0x18],
                input: GpRegs {
                    rax: 0x800,
                    rbx: 0x1122334455667788,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x800,
                    rbx: 0x1122334455667788,
                    rflags: 0x10302,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    error_code: 0x7,
                    access_address: 0x800,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234000,
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    Permissions::Read,
                )],
                ..Default::default()
            },
            TestCase {
                // mov rbx, qword ptr [rax]
                name: "read from ReadWrite memory is OK",
                instr: &[0x48, 0x8B, 0x18],
                input: GpRegs {
                    rax: 0x1234000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234000,
                    rbx: 0x1122334455667788,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234000,
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    Permissions::ReadWrite,
                )],
                ..Default::default()
            },
            TestCase {
                // mov rbx, qword ptr [rax]
                name: "read from Read memory is OK",
                instr: &[0x48, 0x8B, 0x18],
                input: GpRegs {
                    rax: 0x1234000,
                    rbx: 0xcccc_cccc_cccc_cccc,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234000,
                    rbx: 0x1122334455667788,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234000,
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    Permissions::Read,
                )],
                ..Default::default()
            },
            TestCase {
                // mov rbx, qword ptr [rax]
                name: "read at offset is OK",
                instr: &[0x48, 0x8B, 0x18],
                input: GpRegs {
                    rax: 0x1234999,
                    rbx: 0xcccc_cccc_cccc_cccc,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234999,
                    rbx: 0x1122334455667788,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x1234999,
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
                    Permissions::Read,
                )],
                ..Default::default()
            },
            TestCase {
                // mov qword ptr [rax], rbx
                name: "write to reserved region gives #PF",
                instr: &[0x48, 0x89, 0x18],
                input: GpRegs {
                    rax: reserved_range.start,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: reserved_range.start,
                    rflags: 0x10302,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    access_address: reserved_range.start,
                    error_code: 0x6,
                    ..Default::default()
                },
                mem: vec![],
                ..Default::default()
            },
            TestCase {
                // mov rbx, qword ptr [rax]
                name: "read from reserved region gives #PF",
                instr: &[0x48, 0x8B, 0x18],
                input: GpRegs {
                    rax: reserved_range.start,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: reserved_range.start,
                    rflags: 0x10302,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    access_address: reserved_range.start,
                    error_code: 0x4,
                    ..Default::default()
                },
                mem: vec![],
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}

/// Make sure we can map pages anywhere in the address space
/// The address space is too big to try all pages.
/// We select 10 million random addresses and test them.
#[test]
pub fn memory_accessible() {
    let mut vm = Vm::start(1).unwrap();
    let mut o = vm.first_observer_only();
    let reserved_range = o.reserved_range();
    let page_range = 0xffff_8000_0000_0000u64 as i64..0x0000_7fff_ffff_ffff_i64;
    let mut rng = rand::thread_rng();

    o.batch(
        repeat(()).take(10_000_000).map(move |_| {
            let mut addr;
            loop {
                addr = rng.gen_range(page_range.clone()) as u64;
                if !reserved_range.contains(&addr) && !reserved_range.contains(&(addr + 1)) {
                    break;
                }
            }

            TestCase {
                // add rax, rbx
                name: "Can execute from anywhere in the non-reserved address space",
                instr: &[0xCC],
                input: GpRegs {
                    rip: addr,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: addr + 1,
                    rflags: DEFAULT_FLAGS,
                    exception_id: BREAKPOINT_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            }
        }),
        &mut Vec::new(),
    );
}

#[test]
pub fn exceptions() {
    let mut vm = Vm::start(1).unwrap();
    vm.first_observer_only().batch(
        [
            TestCase {
                // div rbx
                name: "Can intercept #DIV",
                instr: &[0x48, 0xF7, 0xF3],
                input: GpRegs {
                    ..Default::default()
                },
                expected_output: GpRegs {
                    exception_id: DIVIDE_BY_ZERO_EXCEPTION,
                    rflags: 0x10202,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // nop
                name: "Can intercept #DB",
                instr: &[0x90],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // int3
                name: "Can intercept #BP",
                instr: &[0xcc],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1,
                    rflags: DEFAULT_FLAGS,
                    exception_id: BREAKPOINT_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // an invalid opcode
                name: "Can intercept #UD",
                instr: &[0xce],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rflags: 0x10302,
                    exception_id: INVALID_OPCODE_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // mov cr0, rax
                name: "Can intercept #GP",
                instr: &[0x0F, 0x22, 0xC0],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rflags: 0x10302,
                    exception_id: GENERAL_PROTECTION_FAULT_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // mov    rax,QWORD PTR [rax+0x10000]
                name: "Can intercept #PF",
                instr: &[0x48, 0x8B, 0x80, 0x00, 0x00, 0x01, 0x00],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rflags: 0x10302,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    error_code: 0x4,
                    access_address: 0x10000,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // add    BYTE PTR [rsp+rax*1],al
                name: "Can intercept #SS",
                instr: &[0x00, 0x04, 0x04],
                input: GpRegs {
                    rsp: 0x12341234_12341234,
                    rax: 0xabcd,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rsp: 0x12341234_12341234,
                    rax: 0xabcd,
                    rflags: 0x10302,
                    exception_id: STACK_SEGMENT_FAULT,
                    ..Default::default()
                },
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}

#[test]
pub fn registers() {
    let mut vm = Vm::start(1).unwrap();
    vm.first_observer_only().batch(
        [
            TestCase {
                // sub rax, 1
                name: "rax is observed correctly",
                instr: &[0x48, 0x83, 0xE8, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rcx, 1
                name: "rcx is observed correctly",
                instr: &[0x48, 0x83, 0xE9, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rcx: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rdx, 1
                name: "rdx is observed correctly",
                instr: &[0x48, 0x83, 0xEA, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rdx: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rbx, 1
                name: "rbx is observed correctly",
                instr: &[0x48, 0x83, 0xEB, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rbx: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rsp, 1
                name: "rsp is observed correctly",
                instr: &[0x48, 0x83, 0xEC, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rsp: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rbp, 1
                name: "rbp is observed correctly",
                instr: &[0x48, 0x83, 0xED, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rbp: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rsi, 1
                name: "rsi is observed correctly",
                instr: &[0x48, 0x83, 0xEE, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rsi: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub rdi, 1
                name: "rdi is observed correctly",
                instr: &[0x48, 0x83, 0xEF, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rdi: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r8, 1
                name: "r8 is observed correctly",
                instr: &[0x49, 0x83, 0xE8, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r8: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r9, 1
                name: "r9 is observed correctly",
                instr: &[0x49, 0x83, 0xE9, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r9: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r10, 1
                name: "r10 is observed correctly",
                instr: &[0x49, 0x83, 0xEA, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r10: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r11, 1
                name: "r11 is observed correctly",
                instr: &[0x49, 0x83, 0xEB, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r11: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r12, 1
                name: "r12 is observed correctly",
                instr: &[0x49, 0x83, 0xEC, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r12: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r13, 1
                name: "r13 is observed correctly",
                instr: &[0x49, 0x83, 0xED, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r13: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r14, 1
                name: "r14 is observed correctly",
                instr: &[0x49, 0x83, 0xEE, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r14: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // sub r15, 1
                name: "r15 is observed correctly",
                instr: &[0x49, 0x83, 0xEF, 0x01],
                input: GpRegs {
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    r15: u64::MAX,
                    rip: 0x4,
                    rflags: DEFAULT_FLAGS | CARRY_FLAG | PARITY_FLAG | AUXILIARY_CARRY_FLAG | SIGN_FLAG | TRAP_FLAG,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}

#[test]
pub fn debug_registers() {
    let mut vm = Vm::start(1).unwrap();
    vm.first_observer_only().batch(
        [
            // Make sure the execution breakpoints trigger as we expect
            TestCase {
                // int3
                name: "#TF on execute breakpoint of size 1",
                instr: &[0xCC],
                input: GpRegs {
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on execution
                        dr7: 0b0000_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff0ff1,
                        dr7: 0b0000_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                ..Default::default()
            },
            TestCase {
                // int3
                name: "no #TF on execute breakpoint of size 2",
                instr: &[0xCC],
                input: GpRegs {
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1001,
                    rflags: DEFAULT_FLAGS,
                    exception_id: BREAKPOINT_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on execution
                        dr7: 0b0100_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff0ff0,
                        dr7: 0b0100_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                ..Default::default()
            },
            TestCase {
                // int3
                name: "no #TF on execute breakpoint of size 4",
                instr: &[0xCC],
                input: GpRegs {
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1001,
                    rflags: DEFAULT_FLAGS,
                    exception_id: BREAKPOINT_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on execution
                        dr7: 0b1100_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff0ff0,
                        dr7: 0b1100_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                ..Default::default()
            },
            TestCase {
                // int3
                name: "no #TF on execute breakpoint of size 8",
                instr: &[0xCC],
                input: GpRegs {
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1001,
                    rflags: DEFAULT_FLAGS,
                    exception_id: BREAKPOINT_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on execution
                        dr7: 0b1000_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff0ff0,
                        dr7: 0b1000_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                ..Default::default()
            },
            // Make sure write watchpoints work as expected
            // watchpoint of size 1
            TestCase {
                // mov [rax], al
                name: "#TF on write watchpoint of size 1 (writing 1 byte)",
                instr: &[0x88, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on write
                        dr7: 0b0001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff4ff1,
                        dr7: 0b0001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], al
                name: "no #TF for different address on write watchpoint of size 1 (writing 1 byte)",
                instr: &[0x88, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1234000,
                        // Enable DR0 breakpoint at 0x1234000 (size 1) triggering on write
                        dr7: 0b0001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1234000,
                        dr6: 0xffff4ff0,
                        dr7: 0b0001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], ax
                name: "#TF on write watchpoint of size 1 (writing 2 bytes)",
                instr: &[0x66, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1001,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b0001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1001,
                        dr6: 0xffff4ff1,
                        dr7: 0b0001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], eax
                name: "#TF on write watchpoint of size 1 (writing 4 bytes)",
                instr: &[0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1003,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b0001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1003,
                        dr6: 0xffff4ff1,
                        dr7: 0b0001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], rax
                name: "#TF on write watchpoint of size 1 (writing 8 bytes)",
                instr: &[0x48, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1007,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b0101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1007,
                        dr6: 0xffff4ff1,
                        dr7: 0b0101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            // watchpoint of size 2
            TestCase {
                // mov [rax], al
                name: "#TF on write watchpoint of size 2 (writing 1 byte)",
                instr: &[0x88, 0x00],
                input: GpRegs {
                    rax: 0x1001,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1001,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on write
                        dr7: 0b0101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff4ff1,
                        dr7: 0b0101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x01], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], ax
                name: "#TF on write watchpoint of size 2 (writing 2 bytes)",
                instr: &[0x66, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1001,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b0101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1001,
                        dr6: 0xffff4ff1,
                        dr7: 0b0101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], eax
                name: "#TF on write watchpoint of size 2 (writing 4 bytes)",
                instr: &[0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1003,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b0101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1003,
                        dr6: 0xffff4ff1,
                        dr7: 0b0101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], rax
                name: "#TF on write watchpoint of size 2 (writing 8 bytes)",
                instr: &[0x48, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1007,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b0101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1007,
                        dr6: 0xffff4ff1,
                        dr7: 0b0101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            // watchpoint of size 4
            TestCase {
                // mov [rax], al
                name: "#TF on write watchpoint of size 4 (writing 1 byte)",
                instr: &[0x88, 0x00],
                input: GpRegs {
                    rax: 0x1003,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1003,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on write
                        dr7: 0b1101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff4ff1,
                        dr7: 0b1101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], ax
                name: "#TF on write watchpoint of size 4 (writing 2 bytes)",
                instr: &[0x66, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1001,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b1101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1001,
                        dr6: 0xffff4ff1,
                        dr7: 0b1101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], eax
                name: "#TF on write watchpoint of size 4 (writing 4 bytes)",
                instr: &[0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1003,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b1101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1003,
                        dr6: 0xffff4ff1,
                        dr7: 0b1101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], rax
                name: "#TF on write watchpoint of size 4 (writing 8 bytes)",
                instr: &[0x48, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1007,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b1101_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1007,
                        dr6: 0xffff4ff1,
                        dr7: 0b1101_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            // watchpoint of size 8
            TestCase {
                // mov [rax], al
                name: "#TF on write watchpoint of size 8 (writing 1 byte)",
                instr: &[0x88, 0x00],
                input: GpRegs {
                    rax: 0x1007,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1007,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on write
                        dr7: 0b1001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff4ff1,
                        dr7: 0b1001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], ax
                name: "#TF on write watchpoint of size 8 (writing 2 bytes)",
                instr: &[0x66, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1001,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b1001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1001,
                        dr6: 0xffff4ff1,
                        dr7: 0b1001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], eax
                name: "#TF on write watchpoint of size 8 (writing 4 bytes)",
                instr: &[0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1003,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b1001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1003,
                        dr6: 0xffff4ff1,
                        dr7: 0b1001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov [rax], rax
                name: "#TF on write watchpoint of size 8 (writing 8 bytes)",
                instr: &[0x48, 0x89, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1007,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on write
                        dr7: 0b1001_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1007,
                        dr6: 0xffff4ff1,
                        dr7: 0b1001_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0x10], Permissions::ReadWrite)],
                ..Default::default()
            },
            // Make sure read/write watchpoints work as expected
            // watchpoint of size 1
            TestCase {
                // mov al, [rax]
                name: "#TF on read watchpoint of size 1 (writing 1 byte)",
                instr: &[0x8a, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1000,
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1000,
                        // Enable DR0 breakpoint at 0x1000 (size 1) triggering on read/write
                        dr7: 0b0011_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1000,
                        dr6: 0xffff4ff1,
                        dr7: 0b0011_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov ax, [rax]
                name: "#TF on read watchpoint of size 1 (reading 2 bytes)",
                instr: &[0x66, 0x8b, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1001,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on read/write
                        dr7: 0b0011_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1001,
                        dr6: 0xffff4ff1,
                        dr7: 0b0011_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0], &[0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov eax, [rax]
                name: "#TF on read watchpoint of size 1 (writing 4 bytes)",
                instr: &[0x8b, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x2,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1003,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on read/write
                        dr7: 0b0011_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1003,
                        dr6: 0xffff4ff1,
                        dr7: 0b0011_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(0x1000, &[0, 0, 0, 0], &[0, 0, 0, 0], Permissions::ReadWrite)],
                ..Default::default()
            },
            TestCase {
                // mov rax, [rax]
                name: "#TF on read watchpoint of size 1 (writing 8 bytes)",
                instr: &[0x48, 0x8b, 0x00],
                input: GpRegs {
                    rax: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x3,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                debug_regs: Some((
                    DebugRegs {
                        dr0: 0x1007,
                        // Enable DR0 breakpoint at 0x1001 (size 1) triggering on read/write
                        dr7: 0b0111_0000_0000_0000_0011,
                        ..Default::default()
                    },
                    DebugRegs {
                        dr0: 0x1007,
                        dr6: 0xffff4ff1,
                        dr7: 0b0111_0000_0100_0000_0011,
                        ..Default::default()
                    },
                )),
                mem: vec![(
                    0x1000,
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    &[0, 0, 0, 0, 0, 0, 0, 0],
                    Permissions::ReadWrite,
                )],
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}

#[test]
pub fn dropping_iterator() {
    let mut vm = Vm::start(1).unwrap();
    let mut o = vm.first_observer_only();

    // We request 1000 observations, but then we drop the iterator after having checked only the first two.
    o.batch_iter(
        iter::repeat(TestCase {
            // add rax, rbx
            name: "Execution that should just work fine",
            instr: &[0x48, 0x01, 0xD8],
            input: GpRegs {
                rax: 0x10,
                rbx: 0x1234321,
                rip: 0x1000,
                rflags: DEFAULT_FLAGS,
                ..Default::default()
            },
            expected_output: GpRegs {
                rax: 0x1234331,
                rbx: 0x1234321,
                rip: 0x1003,
                rflags: DEFAULT_FLAGS,
                exception_id: TRAP_EXCEPTION,
                ..Default::default()
            },
            ..Default::default()
        })
        .take(1000),
    )
    .take(2)
    .for_each(drop);

    // Any other pending operations from batch_iter should have been ignored when the iterator was dropped.
    o.batch(
        [TestCase {
            // add rax, rbx
            name: "Execution after cancelling batch_iter in progress",
            instr: &[0x48, 0x01, 0xD8],
            input: GpRegs {
                rax: 0x33,
                rbx: 0x4321234,
                rip: 0x4300,
                rflags: DEFAULT_FLAGS,
                ..Default::default()
            },
            expected_output: GpRegs {
                rax: 0x4321267,
                rbx: 0x4321234,
                rip: 0x4303,
                rflags: DEFAULT_FLAGS,
                exception_id: TRAP_EXCEPTION,
                ..Default::default()
            },
            ..Default::default()
        }],
        &mut Vec::new(),
    );
}

#[test]
pub fn exec_xmm_regs() {
    let mut vm = Vm::start(1).unwrap();
    vm.first_observer_only().batch(
        [
            TestCase {
                // add rax, rbx
                name: "XMM should not change if instruction does not modify xmm",
                instr: &[0x48, 0x01, 0xD8],
                input: GpRegs {
                    rax: 0x10,
                    rbx: 0x1234321,
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rax: 0x1234331,
                    rbx: 0x1234321,
                    rip: 0x1003,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                xmm: Some(([0; 16], [0; 16])),
                ..Default::default()
            },
            TestCase {
                // pcmpeqd xmm0, xmm0
                name: "XMM should update when an instruction updates it",
                instr: &[0x66, 0x0F, 0x76, 0xC0],
                input: GpRegs {
                    rip: 0x1000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1004,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                xmm: Some((
                    [0; 16],
                    [
                        0xffffffff_ffffffff_ffffffff_ffffffff,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                    ],
                )),
                ..Default::default()
            },
            TestCase {
                // movqdu xmm0, [rax]
                name: "XMM should update when an instruction updates it",
                instr: &[0xf3, 0x0f, 0x6f, 0x00],
                input: GpRegs {
                    rip: 0x1000,
                    rax: 0x5000,
                    rflags: DEFAULT_FLAGS,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1004,
                    rax: 0x5000,
                    rflags: DEFAULT_FLAGS,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                xmm: Some((
                    [0; 16],
                    [
                        0xab0f0e0d0c0b0a090807060504030201,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                    ],
                )),
                mem: vec![(
                    0x5000,
                    &[
                        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0xab,
                    ],
                    &[
                        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0xab,
                    ],
                    Permissions::Read,
                )],
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}

#[test]
fn exec_hang() {
    let mut vm = Vm::start(1).unwrap();
    vm.first_observer_only().batch(
        [TestCase {
            // label: jmp label
            name: "Should detect and intercept hangs",
            instr: &[0xEB, 0xFE],
            input: GpRegs {
                rip: 0x1000,
                rflags: 0,
                ..Default::default()
            },
            expected_output: GpRegs {
                rip: 0x1000,
                rflags: 0x202,
                exception_id: TIMEOUT_EXCEPTION,
                ..Default::default()
            },
            ..Default::default()
        }],
        &mut Vec::new(),
    );
}

/// Make sure the FS and GS segment registers work properly.
#[test]
pub fn fsgs_working() {
    let mut vm = Vm::start(1).unwrap();

    vm.first_observer_only().batch(
        [
            TestCase {
                // mov    rax,QWORD PTR fs:0x3e8
                name: "Accessing FS without mapping should give page fault",
                instr: &[0x64, 0x48, 0x8B, 0x04, 0x25, 0xE8, 0x03, 0x00, 0x00],
                input: GpRegs {
                    rip: 0x1000,
                    fs_base: 0x5000,
                    rflags: 0,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1000,
                    rflags: 0x10202,
                    fs_base: 0x5000,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    access_address: 0x53e8,
                    error_code: 0x4,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // mov    rax,QWORD PTR fs:0x3e8
                name: "Accessing FS should load correct data",
                instr: &[0x64, 0x48, 0x8B, 0x04, 0x25, 0xE8, 0x03, 0x00, 0x00],
                input: GpRegs {
                    rip: 0x1000,
                    fs_base: 0x5000,
                    rflags: TRAP_FLAG,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1009,
                    rax: 0x8877665544332211,
                    fs_base: 0x5000,
                    rflags: 0x302,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x53e8,
                    &[0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
                    &[0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
                    Permissions::Read,
                )],
                ..Default::default()
            },
            TestCase {
                // mov    rax,QWORD PTR gs:0x3e8
                name: "Accessing gs without mapping should give page fault",
                instr: &[0x65, 0x48, 0x8B, 0x04, 0x25, 0xE8, 0x03, 0x00, 0x00],
                input: GpRegs {
                    rip: 0x1000,
                    gs_base: 0x5000,
                    rflags: 0,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1000,
                    rflags: 0x10202,
                    gs_base: 0x5000,
                    exception_id: PAGE_FAULT_EXCEPTION,
                    access_address: 0x53e8,
                    error_code: 0x4,
                    ..Default::default()
                },
                ..Default::default()
            },
            TestCase {
                // mov    rax,QWORD PTR gs:0x3e8
                name: "Accessing gs should load correct data",
                instr: &[0x65, 0x48, 0x8B, 0x04, 0x25, 0xE8, 0x03, 0x00, 0x00],
                input: GpRegs {
                    rip: 0x1000,
                    gs_base: 0x5000,
                    rflags: TRAP_FLAG,
                    ..Default::default()
                },
                expected_output: GpRegs {
                    rip: 0x1009,
                    rax: 0x8877665544332211,
                    gs_base: 0x5000,
                    rflags: 0x302,
                    exception_id: TRAP_EXCEPTION,
                    ..Default::default()
                },
                mem: vec![(
                    0x53e8,
                    &[0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
                    &[0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
                    Permissions::Read,
                )],
                ..Default::default()
            },
        ],
        &mut Vec::new(),
    );
}
