use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::x64::X64Arch;
use liblisa::arch::FullScope;
use liblisa::instr::Instruction;
use liblisa_enc::Validity;
use liblisa_x64_observer::with_oracle;

fn infer(c: &mut Criterion) {
    with_oracle(|mut o| {
        let instr = Instruction::new(&[0x48, 0x31, 0xD0]);
        c.bench_function("Validity::<X64Arch>::infer[XOR rax, rdx]", |b| {
            b.iter(|| black_box(Validity::infer::<X64Arch, _>(&mut o, &instr)))
        });

        let instr = Instruction::new(&[0xFF, 0x74, 0xB8, 0x01]);
        c.bench_function("Validity::<X64Arch>::infer[PUSH QWORD PTR [rax+rdi*4+0x1]]", |b| {
            b.iter(|| black_box(Validity::infer::<X64Arch, _>(&mut o, &instr)))
        });

        let instrs = (0..=0xff)
            .map(|n| Instruction::new(&[0xFF, 0x74, 0xB8, n]))
            .collect::<Vec<_>>();
        c.bench_function("batch_infer-256-instrs", |b| {
            b.iter(|| black_box(Validity::infer_batch::<X64Arch, _>(&mut o, &instrs, &FullScope)).for_each(drop))
        });

        let instrs = (0..0x1000)
            .map(|n| Instruction::new(&[0xFF, 0x74, (n >> 8) as u8, n as u8]))
            .collect::<Vec<_>>();
        c.bench_function("batch_infer-4096-instrs", |b| {
            b.iter(|| black_box(Validity::infer_batch::<X64Arch, _>(&mut o, &instrs, &FullScope)).for_each(drop))
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = infer
}
criterion_main!(benches);
