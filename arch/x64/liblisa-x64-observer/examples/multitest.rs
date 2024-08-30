use std::time::Instant;

use liblisa_x64_observer::vm::{
    CpuFeatures, DebugRegs, DebugRegsWriter, ExtendedRegsWriter, MemoryMapper, ObservationRequest, PageAllocator,
    ResultMemoryAccess, Vm,
};
use liblisa_x64_observer_shmqueue::frame::command::{ExtendedRegs, Permissions};
use liblisa_x64_observer_shmqueue::regs::GpRegs;

#[derive(Copy, Clone)]
struct TestRequest;

impl ObservationRequest for TestRequest {
    type Result = ();

    #[inline(always)]
    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, _extended_regs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        gpregs.rip = 0x1234000;

        mapper.set([alloc.allocate_page(0x1234000, &[0xCC], Permissions::Executable)].into_iter());
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

    let mut vm = Vm::start(2).unwrap();
    let mut observers = vm.observers().collect::<Vec<_>>();

    const COUNT: usize = 5_000_000;
    println!("{} observations in {} threads", COUNT, observers.len());

    for batch_size in [100_000, 1, 2, 5, 10, 100, 1000, 10_000, 100_000] {
        println!("{} observations in batches of {}", COUNT, batch_size);

        std::thread::scope(|scope| {
            let start = Instant::now();
            let threads = observers
                .iter_mut()
                .map(|observer| {
                    scope.spawn(move || {
                        for _n in 0..COUNT / 2 / batch_size {
                            observer
                                .batch_iter(std::iter::repeat(TestRequest).take(batch_size))
                                .for_each(drop)
                        }
                    })
                })
                .collect::<Vec<_>>();

            for thread in threads {
                thread.join().unwrap();
            }

            println!(
                "{}ns per observation with batch size {}",
                start.elapsed().as_nanos() / (COUNT) as u128,
                batch_size
            );
        });
    }

    // println!("Sleeping now; Check CPU usage");
    // std::thread::sleep(std::time::Duration::from_secs(30));
}
