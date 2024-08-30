use std::time::Instant;

use liblisa_x64_observer::vm::{
    CpuFeatures, DebugRegs, DebugRegsWriter, ExtendedRegsWriter, MemoryMapper, ObservationRequest, PageAllocator,
    ResultMemoryAccess, Vm, YmmRegs,
};
use liblisa_x64_observer_shmqueue::frame::command::{ExtendedRegs, Permissions};
use liblisa_x64_observer_shmqueue::regs::{GpRegs, XsaveLegacyArea};

#[derive(Copy, Clone)]
struct TestRequest(u64);
const TRAP_FLAG: u64 = 1 << 8;

impl ObservationRequest for TestRequest {
    type Result = ();

    #[inline(always)]
    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, mut extended_regs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        gpregs.rip = 0x1234000;
        gpregs.rflags = TRAP_FLAG;

        mapper.set([alloc.allocate_page(0x1234000, &[0xCC], Permissions::Executable)].into_iter());

        extended_regs.set_legacy(XsaveLegacyArea {
            xmm: [self.0 as u128; 16],
            ..Default::default()
        });

        extended_regs.set_ymm(YmmRegs {
            ymm_hi128: [self.0 as u128; 16],
        });
    }

    #[inline(always)]
    fn result(
        self, _: CpuFeatures, _gpregs: &GpRegs, _debug_regs: &DebugRegs, _extended_regs: &ExtendedRegs,
        _memory: ResultMemoryAccess,
    ) {
    }
}

fn main() {
    println!("Starting observer...");
    println!("Make sure to restrict this process to cores sharing the same L3 cache");

    let mut vm = Vm::start(1).unwrap();
    let mut observer = vm.first_observer_only();

    println!("Reserved range: {:?}", observer.reserved_range());

    // The shmem is currently configured to contain only 512 command pages.
    // Batch sizes of more than a few thousand are unlikely to affect performance much.

    const COUNT: usize = 5_000_000;
    for batch_size in [100_000, 1, 2, 5, 10, 100, 1000, 10_000, 100_000] {
        println!("{} observations in batches of {}", COUNT, batch_size);

        let start = Instant::now();
        for _n in 0..COUNT / batch_size {
            let mut n = 0u64;
            let mut num_seen = 0;
            observer
                .batch_iter(
                    std::iter::repeat_with(|| {
                        TestRequest({
                            n = n.wrapping_add(1);
                            n
                        })
                    })
                    .take(batch_size),
                )
                .for_each(|_| num_seen += 1);
            assert_eq!(num_seen, batch_size);
        }

        println!(
            "{}ns per observation with batch size {}",
            start.elapsed().as_nanos() / (COUNT) as u128,
            batch_size
        );
    }

    // println!("Sleeping now; Check CPU usage");
    // std::thread::sleep(std::time::Duration::from_secs(30));
}
