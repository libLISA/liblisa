use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::fake::{AnyArea, FakeArch, FakeReg};
use liblisa::encoding::dataflows::{AccessKind, AddressComputation, Dest, Inputs, MemoryAccess, MemoryAccesses, Size, Source};
use liblisa::instr::Instruction;
use liblisa::state::random::StateGen;
use rand::SeedableRng;
use rand_xoshiro::Xoshiro256PlusPlus;

fn randomized_value(c: &mut Criterion) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    c.bench_function("randomized_value", |b| {
        b.iter(|| {
            black_box(liblisa::state::random::randomized_value(&mut rng));
        })
    });
}

fn randomized_bytes_into_buffer(c: &mut Criterion) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    c.bench_function("randomized_bytes_into_buffer", |b| {
        b.iter(|| {
            let mut buffer = [0u8; 16];
            liblisa::state::random::randomized_bytes_into_buffer(&mut rng, &mut buffer);
            black_box(&mut buffer);
        })
    });
}

fn randomize_new1(c: &mut Criterion) {
    let accesses = MemoryAccesses::<FakeArch> {
        instr: Instruction::new(&[0x00, 0x00]),
        memory: vec![MemoryAccess {
            kind: AccessKind::Executable,
            inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
            size: 3..3,
            calculation: AddressComputation::unscaled_sum(1),
            alignment: 1,
        }],
        use_trap_flag: false,
    };
    let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    c.bench_function("StateGen::randomize_new::<1 memory access>", |b| {
        b.iter(|| {
            black_box(state_gen.randomize_new(&mut rng).unwrap());
        })
    });
}

fn randomize_new2(c: &mut Criterion) {
    let accesses = MemoryAccesses::<FakeArch> {
        instr: Instruction::new(&[0x00, 0x00]),
        memory: vec![
            MemoryAccess {
                kind: AccessKind::Executable,
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                size: 3..3,
                calculation: AddressComputation::unscaled_sum(1),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                size: 3..3,
                calculation: AddressComputation::unscaled_sum(1).with_offset(10),
                alignment: 1,
            },
        ],
        use_trap_flag: false,
    };
    let state_gen = StateGen::new(&accesses, &AnyArea).unwrap();

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    c.bench_function("StateGen::randomize_new::<2 memory access>", |b| {
        b.iter(|| {
            black_box(state_gen.randomize_new(&mut rng).unwrap());
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = randomized_value, randomized_bytes_into_buffer, randomize_new1, randomize_new2
}
criterion_main!(benches);
