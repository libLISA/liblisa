use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::x64::X64Arch;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::state::random::StateGen;
use liblisa_enc::MemoryAccessAnalysis;
use liblisa_x64_observer::with_oracle;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

fn infer(c: &mut Criterion) {
    with_oracle(|mut o| {
        let instr = Instruction::new(&[0x48, 0x31, 0xD0]);
        c.bench_function("Accesses::<X64Arch, PtraceOracle>::infer[XOR rax, rdx]", |b| {
            b.iter(|| black_box(MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr)))
        });

        let instr = Instruction::new(&[0xFF, 0x74, 0xB8, 0x01]);
        c.bench_function(
            "Accesses::<X64Arch, PtraceOracle>::infer[PUSH QWORD PTR [rax+rdi*4+0x1]]",
            |b| b.iter(|| black_box(MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr))),
        );
    });
}

fn randomize_new(c: &mut Criterion) {
    with_oracle(|mut o| {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let mappable = Oracle::<X64Arch>::mappable_area(&o);

        let instr = Instruction::new(&[0x48, 0x31, 0xD0]);
        let accesses = MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr).unwrap();
        let state_gen = StateGen::new(&accesses, &mappable).unwrap();
        c.bench_function("randomize_no_memory_accesses", |b| {
            b.iter(|| black_box(state_gen.randomize_new(&mut rng).unwrap()))
        });

        let instr = Instruction::new(&[0xFF, 0x74, 0xB8, 0x01]);
        let accesses = MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr).unwrap();
        let state_gen = StateGen::new(&accesses, &mappable).unwrap();
        c.bench_function("randomize_double_memory_access", |b| {
            b.iter(|| black_box(state_gen.randomize_new(&mut rng).unwrap()))
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = infer, randomize_new
}
criterion_main!(benches);
