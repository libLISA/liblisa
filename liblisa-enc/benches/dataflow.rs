use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::x64::X64Arch;
use liblisa::instr::Instruction;
use liblisa_enc::{DataflowAnalysis, MemoryAccessAnalysis};
use liblisa_x64_observer::with_oracle;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

fn infer(c: &mut Criterion) {
    with_oracle(|mut o| {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let instr = Instruction::new(&[0x30, 0xD0]);
        let memory_accesses = MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr).unwrap();
        c.bench_function("Dataflow::<X64Arch, PtraceOracle>::infer[XOR al, dl]", |b| {
            b.iter(|| black_box(DataflowAnalysis::infer(&mut rng, &mut o, &memory_accesses).unwrap()))
        });

        let instr = Instruction::new(&[0x48, 0x31, 0xD0]);
        let memory_accesses = MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr).unwrap();
        c.bench_function("Dataflow::<X64Arch, PtraceOracle>::infer[XOR rax, rdx]", |b| {
            b.iter(|| black_box(DataflowAnalysis::infer(&mut rng, &mut o, &memory_accesses).unwrap()))
        });

        let instr = Instruction::new(&[0xFF, 0x74, 0xB8, 0x01]);
        let memory_accesses = MemoryAccessAnalysis::infer::<X64Arch, _>(&mut o, &instr).unwrap();
        c.bench_function(
            "Dataflow::<X64Arch, PtraceOracle>::infer[PUSH QWORD PTR [rax+rdi*4+0x1]]",
            |b| b.iter(|| black_box(DataflowAnalysis::infer(&mut rng, &mut o, &memory_accesses).unwrap())),
        );
    });
}

criterion_group!(benches, infer);
criterion_main!(benches);
