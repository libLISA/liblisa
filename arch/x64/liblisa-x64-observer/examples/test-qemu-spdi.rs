use std::iter::repeat_with;

use liblisa_x64_observer::vm::{
    CpuFeatures, DebugRegs, DebugRegsWriter, ExtendedRegs, ExtendedRegsWriter, GpRegs, MemoryMapper, ObservationRequest,
    PageAllocator, Permissions, ResultMemoryAccess, Vm, XsaveLegacyArea,
};
use rand::seq::SliceRandom;
use rand::Rng;

const INSTR_ADD_DL_DL: &[u8] = &[0x00, 0xd2, 0xcc];
const INSTR_ADD_BL_DL: &[u8] = &[0x00, 0xd3, 0xcc];
const TRAP_FLAG: u64 = 1 << 8;

#[derive(Copy, Clone, Debug)]
struct TestRequest {
    instr: &'static [u8],
    gpregs: GpRegs,
    expected_rbx: u64,
    expected_rdx: u64,
}

impl ObservationRequest for TestRequest {
    type Result = (bool, TestRequest);

    #[inline(always)]
    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, mut eregs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        *gpregs = self.gpregs;

        mapper.set([alloc.allocate_page(self.gpregs.rip, self.instr, Permissions::Executable)].into_iter());

        eregs.set_legacy(XsaveLegacyArea {
            status_word: 5,
            ..Default::default()
        });
    }

    #[inline(always)]
    fn result(
        self, _: CpuFeatures, gpregs: &GpRegs, _debug_regs: &DebugRegs, _: &ExtendedRegs, m: ResultMemoryAccess,
    ) -> Self::Result {
        assert!(gpregs.exception_id == 0x01 || gpregs.exception_id == 0x03); // TRAP exception

        let offset = (gpregs.rip - 2) as usize & 0xfff;
        println!(
            " @ {:X} ({:X?})",
            gpregs.rip - 2,
            &m.iter().next().unwrap()[offset..offset + 3]
        );
        if gpregs.rbx != self.expected_rbx {
            println!("RBX don't match in {:X?}: {:X?} -> {gpregs:X?}", self.instr, self.gpregs);
            return (false, self);
        }

        if gpregs.rdx != self.expected_rdx {
            println!("RDX don't match in {:X?}: {:X?} -> {gpregs:X?}", self.instr, self.gpregs);
            return (false, self);
        }

        (true, self)
    }
}

/// Test whether running different instructions at the same address works correctly.
/// When using qemu in full emulation mode, it uses the TCG to dynamically recompile code.
/// The compilation is cached by page.
/// It remains cached even if we unmap and remap executable pages.
/// We perform a dummy volatile read and write on any executable page it maps to avoid this effect.
fn main() {
    let mut rng = rand::thread_rng();
    let mut best_trace = Vec::new();
    for k in 0..100 {
        println!("Iteration {k}");

        let mut vm = Vm::start(64).unwrap();
        let mut observer = vm.first_observer_only();
        let v = repeat_with(|| {
            let gpregs = GpRegs {
                rax: rng.gen(),
                rbx: rng.gen(),
                rcx: rng.gen(),
                rdx: rng.gen(),
                rbp: rng.gen(),
                rsi: rng.gen(),
                rdi: rng.gen(),
                r8: rng.gen(),
                r9: rng.gen(),
                r10: rng.gen(),
                r11: rng.gen(),
                r12: rng.gen(),
                r13: rng.gen(),
                r14: rng.gen(),
                r15: rng.gen(),
                exception_id: 0,
                error_code: 0,
                rip: *[
                    0xffff_ffff_ffff_fff0,
                    0xffff_ffff_ffff_fff1,
                    0xffff_ffff_ffff_fffc,
                    0xffff_ffff_ffff_ffef,
                    0xffff_ffff_ffff_ffe0,
                    0x3ffffffffc,
                    0x3fffffff00,
                    0x4047,
                    0,
                ]
                .choose(&mut rng)
                .unwrap(),
                rsp: rng.gen(),
                access_address: 0,
                rflags: TRAP_FLAG,
                fs_base: 0,
                gs_base: 0,
            };

            let instr = [INSTR_ADD_DL_DL, INSTR_ADD_BL_DL].choose(&mut rng).unwrap();

            TestRequest {
                instr,
                expected_rbx: if instr == &INSTR_ADD_DL_DL {
                    gpregs.rbx
                } else if instr == &INSTR_ADD_BL_DL {
                    (gpregs.rbx & !0xff) | ((gpregs.rbx as u8).wrapping_add(gpregs.rdx as u8) as u64)
                } else {
                    panic!()
                },
                expected_rdx: if instr == &INSTR_ADD_DL_DL {
                    (gpregs.rdx & !0xff) | ((gpregs.rdx as u8).wrapping_add(gpregs.rdx as u8) as u64)
                } else if instr == &INSTR_ADD_BL_DL {
                    gpregs.rdx
                } else {
                    panic!()
                },
                gpregs,
            }
        })
        .take(1_000_000);

        println!("Testing trace...");

        let mut stop = false;
        let trace = observer
            .batch_iter(v)
            .take_while(|(b, _)| {
                let result = !stop;
                if !*b {
                    stop = true;
                }

                result
            })
            .map(|(_, r)| r)
            .collect::<Vec<_>>();

        if stop {
            println!("Found trace of {} elements, best={}", trace.len(), best_trace.len());
            if trace.len() < best_trace.len() || best_trace.is_empty() {
                best_trace = trace;
            }
        }
    }

    println!("Best trace: {best_trace:?}");
}
