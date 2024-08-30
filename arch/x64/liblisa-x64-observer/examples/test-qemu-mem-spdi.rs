use std::iter::repeat_with;
use std::ops::Range;

use liblisa_x64_observer::vm::{
    CpuFeatures, DebugRegs, DebugRegsWriter, ExtendedRegs, ExtendedRegsWriter, GpRegs, MemoryMapper, ObservationRequest,
    PageAllocator, Permissions, ResultMemoryAccess, Vm, XsaveLegacyArea,
};
use rand::seq::SliceRandom;
use rand::Rng;

const INSTR_ADD_RAX_EAX_33: &[u8] = &[0x01, 0x04, 0x05, 0x00, 0x00, 0x00, 0x33, 0xcc];
const INSTR_ADD_RAX_EAX_32: &[u8] = &[0x01, 0x04, 0x05, 0x00, 0x00, 0x00, 0x32, 0xcc];

#[derive(Clone, Debug)]
struct TestRequest {
    instr: &'static [u8],
    mem: Vec<(u64, Vec<u8>)>,
    gpregs: GpRegs,
    expected_pf_addr: Option<u64>,
}

impl ObservationRequest for TestRequest {
    type Result = (bool, TestRequest);

    #[inline(always)]
    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, mut eregs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        *gpregs = self.gpregs;

        mapper.set(
            [alloc.allocate_page(self.gpregs.rip, self.instr, Permissions::Executable)]
                .into_iter()
                .chain(
                    self.mem
                        .iter()
                        .map(|(addr, data)| alloc.allocate_page(*addr, data, Permissions::ReadWrite)),
                ),
        );

        eregs.set_legacy(XsaveLegacyArea {
            status_word: 5,
            ..Default::default()
        });
    }

    #[inline(always)]
    fn result(
        self, _: CpuFeatures, gpregs: &GpRegs, _debug_regs: &DebugRegs, _: &ExtendedRegs, m: ResultMemoryAccess,
    ) -> Self::Result {
        let offset = self.gpregs.rip as usize & 0xfff;
        println!(
            " @ {:X} ({:02X?})",
            self.gpregs.rip,
            &m.iter().next().unwrap()[offset..offset + 7]
        );

        if let Some(addr) = self.expected_pf_addr {
            if gpregs.exception_id != 0xe {
                println!("Expected PF @ {addr:X}, but got exception 0x{:X}", gpregs.exception_id);
                return (false, self)
            } else if addr != gpregs.access_address {
                println!("Expected PF @ {addr:X}, but got PF @ {:X}", gpregs.access_address);
                return (false, self)
            }
        } else if gpregs.exception_id != 0x01 && gpregs.exception_id != 0x03 {
            println!(
                "Expected breakpoint or trap exception @ {:X}, but got 0x{:X} with mem={:X?}",
                self.gpregs.rip, gpregs.exception_id, self.mem
            );
            return (false, self)
        }

        (true, self)
    }
}

fn can_map(rr: &Range<u64>, addr: u64) -> bool {
    if (addr >> 48) == 0xffff * ((addr >> 47) & 1) {
        !rr.contains(&addr)
    } else {
        false
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
        let reserved = observer.reserved_range();
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
                    0xffff_ffff_ffff_fff2,
                    0xffff_ffff_ffff_fff3,
                    0xffff_ffff_ffff_fff4,
                    0xffff_ffff_ffff_fff5,
                    0xffff_ffff_ffff_fff6,
                    0xffff_ffff_ffff_fff7,
                    0xffff_ffff_ffff_fff8,
                    0x0000_7fff_ffff_fff0,
                    0x3fffffff00,
                    0x4047,
                    0,
                    0x37_1ff7,
                ]
                .choose(&mut rng)
                .unwrap(),
                rsp: rng.gen(),
                access_address: 0,
                rflags: 0,
                fs_base: 0,
                gs_base: 0,
            };

            let instr = *[INSTR_ADD_RAX_EAX_33, INSTR_ADD_RAX_EAX_32].choose(&mut rng).unwrap();

            if instr == INSTR_ADD_RAX_EAX_32 {
                TestRequest {
                    instr,
                    gpregs,
                    expected_pf_addr: None,
                    mem: vec![(gpregs.rax + 0x3200_0000, vec![0, 0, 0, 0])],
                }
            } else if instr == INSTR_ADD_RAX_EAX_33 {
                TestRequest {
                    instr,
                    gpregs,
                    expected_pf_addr: Some(gpregs.rax + 0x3300_0000),
                    mem: Vec::new(),
                }
            } else {
                unreachable!()
            }
        })
        .filter(|t| {
            if !t.mem.iter().all(|(addr, _)| {
                can_map(&reserved, *addr)
                    && addr & 0xfff < 0xffc
                    && addr.wrapping_sub(t.gpregs.rip) >= 4096
                    && t.gpregs.rip.wrapping_sub(*addr) >= 4096
            }) {
                return false
            }

            if let Some(addr) = t.expected_pf_addr {
                if !can_map(&reserved, addr) || addr.wrapping_sub(t.gpregs.rip) < 4096 || t.gpregs.rip.wrapping_sub(addr) < 4096 {
                    return false
                }
            }

            true
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
