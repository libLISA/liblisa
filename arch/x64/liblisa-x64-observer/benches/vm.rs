use std::iter::repeat;
use std::time::{Duration, Instant};

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use itertools::Itertools;
use liblisa_x64_observer::vm::*;
use liblisa_x64_observer_shmqueue::frame::command::{ExtendedRegs, Permissions};
use liblisa_x64_observer_shmqueue::regs::GpRegs;

const TRAP_FLAG: u64 = 1 << 8;

#[derive(Copy, Clone)]
struct MinimalBenchmarkRequest(u64);

impl ObservationRequest for MinimalBenchmarkRequest {
    type Result = ();

    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, _extended_regs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        gpregs.rip = self.0;
        gpregs.rflags = 0; // TRAP_FLAG;

        mapper.set([alloc.fill_and_allocate_page(self.0, &[0x90], Permissions::Executable)].into_iter());
    }

    fn result(
        self, _: CpuFeatures, gpregs: &GpRegs, _debug_regs: &DebugRegs, _extended_regs: &ExtendedRegs, memory: ResultMemoryAccess,
    ) {
        const BREAKPOINT_EXCEPTION: u64 = 0x3;
        assert_eq!(
            gpregs.exception_id,
            BREAKPOINT_EXCEPTION,
            "State: {:X?} with memory: {:X?}",
            gpregs,
            memory.iter().collect::<Vec<_>>()
        );
        assert_eq!(gpregs.rip, self.0 + 1);
    }
}

#[derive(Copy, Clone)]
struct RealInstructionBenchmarkRequest(u64);

impl ObservationRequest for RealInstructionBenchmarkRequest {
    type Result = ();

    fn setup(
        &mut self, _: CpuFeatures, gpregs: &mut GpRegs, _debug_regs: DebugRegsWriter, mut extended_regs: ExtendedRegsWriter,
        alloc: &mut PageAllocator, mapper: MemoryMapper,
    ) {
        gpregs.rip = self.0;
        gpregs.rax = 0x336128937819;
        gpregs.rdx = 0x112233445566;
        gpregs.r11 = 0x1234321;
        gpregs.rbx = 5;
        gpregs.rsp = 3;
        gpregs.rflags = TRAP_FLAG;

        let mut n = 1;
        extended_regs.set_ymm(YmmRegs {
            ymm_hi128: [(); 16].map(|_| {
                n *= 1234321;
                n
            }),
        });

        extended_regs.set_legacy(XsaveLegacyArea {
            xmm: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            ..Default::default()
        });

        mapper.set([alloc.allocate_page(self.0, &[0x48, 0x31, 0xD0], Permissions::Executable)].into_iter());
    }

    fn result(
        self, _: CpuFeatures, gpregs: &GpRegs, _debug_regs: &DebugRegs, _extended_regs: &ExtendedRegs, memory: ResultMemoryAccess,
    ) {
        assert_eq!(gpregs.rip, self.0 + 3);
        assert_eq!(gpregs.rax, 0x336128937819 ^ 0x112233445566);
        assert_eq!(gpregs.rdx, 0x112233445566);
        const TRAP_EXCEPTION: u64 = 0x1;
        assert_eq!(
            gpregs.exception_id,
            TRAP_EXCEPTION,
            "State: {:X?} with memory: {:X?}",
            gpregs,
            memory.iter().collect::<Vec<_>>()
        );
    }
}

fn minimal_observe(c: &mut Criterion) {
    let mut vm = Vm::start(2).unwrap();
    let mut observer = vm.first_observer_only();
    c.bench_function("minimal observe(single static mapping)", |b| {
        b.iter_custom(|num| {
            let start = Instant::now();
            observer
                .batch_iter(repeat(MinimalBenchmarkRequest(0x1234000)).take(num as usize))
                .for_each(drop);
            start.elapsed()
        })
    });

    c.bench_function("minimal observe(xor)", |b| {
        b.iter_custom(|num| {
            let start = Instant::now();
            observer
                .batch_iter(repeat(RealInstructionBenchmarkRequest(0x1234ffd)).take(num as usize))
                .for_each(drop);
            start.elapsed()
        })
    });

    c.bench_function("minimal observe(single alternating mapping)", |b| {
        b.iter_custom(|num| {
            let requests = repeat(MinimalBenchmarkRequest(0x1234000))
                .interleave(repeat(MinimalBenchmarkRequest(0x4321000)))
                .take(num as usize);
            let start = Instant::now();
            observer.batch_iter(requests).for_each(drop);
            start.elapsed()
        })
    });
}

fn discard_pending(c: &mut Criterion) {
    let mut vm = Vm::start(1).unwrap();
    let mut observer = vm.first_observer_only();
    c.bench_function("discard pending(single alternate mapping)", |b| {
        b.iter_custom(|num| {
            let start = Instant::now();
            for _ in 0..num {
                let requests = repeat(MinimalBenchmarkRequest(0x1234000)).interleave(repeat(MinimalBenchmarkRequest(0x4321000)));
                for result in observer.batch_iter(requests).take(1) {
                    black_box(&result);
                }
            }

            start.elapsed()
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .measurement_time(Duration::from_secs(30))
        .sample_size(1_000);
    targets = minimal_observe, discard_pending
}

criterion_main!(benches);
