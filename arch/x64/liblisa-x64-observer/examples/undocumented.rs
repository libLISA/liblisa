use liblisa_x64_observer::vm::{
    CpuFeatures, DebugRegs, DebugRegsWriter, ExtendedRegs, ExtendedRegsWriter, GpRegs, MemoryMapper, ObservationRequest,
    PageAllocator, Permissions, ResultMemoryAccess, Vm, XsaveLegacyArea, YmmRegs,
};

/// This is a weird instruction;
///
/// It takes two 32-byte memory regions: M1 and M2
/// It takes the lowerst 8 bytes of M1: M1[0..8]
/// It fills an XMM reg with M1[0..8] . M1[0..8] (that is, M1[0..8] concatenated to itself)

const INSTR: &[u8] = &[0xC4, 0x03, 0x7D, 0x00, 0x00, 0x10];
const TRAP_FLAG: u64 = 1 << 8;

#[derive(Copy, Clone)]
struct TestRequest {
    avx_offset: usize,
}

impl ObservationRequest for TestRequest {
    type Result = ();

    #[inline(always)]
    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, mut extended_regs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        *gpregs = GpRegs {
            rip: 0x1234000,
            r8: 0x8fe0,
            rax: 0x4fe0,
            rbx: 0x11_000,
            rcx: 0x12_000,
            rdx: 0x13_000,
            rbp: 0x14_000,
            rsi: 0x15_000,
            rdi: 0x16_000,
            r9: 0x17_000,
            r10: 0x18_000,
            r11: 0x19_000,
            r12: 0x1a_000,
            r13: 0x1b_000,
            r14: 0x1c_000,
            r15: 0x1d_000,
            rsp: 0x1e_000,
            rflags: TRAP_FLAG,
            ..Default::default()
        };

        mapper.set(
            [
                alloc.allocate_page(0x1234000, INSTR, Permissions::Executable),
                alloc.allocate_page(
                    0x8fe0,
                    &[
                        0x13, 0x23, 0x33, 0x43, 0x53, 0x63, 0x73, 0x83, 0x14, 0x24, 0x34, 0x44, 0x54, 0x64, 0x74, 0x84, 0x15,
                        0x25, 0x35, 0x45, 0x55, 0x65, 0x75, 0x85, 0x16, 0x26, 0x36, 0x46, 0x56, 0x66, 0x76, 0x86,
                    ],
                    Permissions::Read,
                ),
                alloc.allocate_page(0x4fe0, &[0x66; 32], Permissions::ReadWrite),
            ]
            .into_iter(),
        );

        extended_regs.set_legacy(XsaveLegacyArea {
            xmm: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0xa, 0xb, 0xc, 0xd, 0xe, u128::MAX],
            ..Default::default()
        });
    }

    #[inline(always)]
    fn result(
        self, _: CpuFeatures, gpregs: &GpRegs, _debug_regs: &DebugRegs, extended_regs: &ExtendedRegs, memory: ResultMemoryAccess,
    ) {
        println!("GPREGS: {gpregs:#08X?}");
        let xmm = &extended_regs.legacy_area().xmm;
        println!("XMM: {xmm:#034X?}");

        println!("{}", self.avx_offset);
        let ymm = unsafe { extended_regs.component::<YmmRegs>(self.avx_offset) };
        println!("YMM: {ymm:#034X?}");

        for (index, entry) in memory.iter().enumerate() {
            let data = &entry[4096 - 32..];
            println!("Mem{index} = {data:02X?}");
        }

        assert_eq!(gpregs.exception_id, 0x01); // TRAP exception
    }
}

fn main() {
    let mut vm = Vm::start(1).unwrap();
    let mut observer = vm.first_observer_only();
    let layout = observer.layout();

    observer
        .batch_iter(
            [TestRequest {
                avx_offset: layout.avx256.offset as usize,
            }]
            .into_iter(),
        )
        .for_each(drop);
}
