use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::x64::X64Arch;
use liblisa::arch::CpuState;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::state::{Addr, MemoryState, Permissions, SystemState};
use liblisa_x64_observer::with_oracle;

fn simple_oracle_observe(c: &mut Criterion) {
    println!("Make sure to restrict this process to cores sharing the same L3 cache");

    with_oracle(|mut o| {
        let page = o.random_mappable_page(&mut rand::thread_rng());
        let pc = page.start_addr();
        let instr = Instruction::new(&[0x48, 0x31, 0xD0]); // XOR rax, rdx
        let state = SystemState::<X64Arch>::new(
            CpuState::<X64Arch>::default_with_pc(pc.as_u64()),
            MemoryState::from_vec(vec![(pc, Permissions::Execute, instr.bytes().to_owned())]),
        );

        c.bench_function("Oracle::observe[XOR rax, rdx]", |b| {
            b.iter(|| black_box(o.observe(&state).unwrap()))
        });

        let instr = Instruction::new(&[0x48, 0x31, 0xD0]); // XOR rax, rdx
        let state2 = SystemState::<X64Arch>::new(
            CpuState::<X64Arch>::default_with_pc(pc.as_u64()),
            MemoryState::from_vec(vec![
                (pc, Permissions::Execute, instr.bytes().to_owned()),
                (
                    Addr::new(0x11223344),
                    Permissions::Read,
                    vec![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3],
                ),
                (
                    Addr::new(0x11323344),
                    Permissions::Read,
                    vec![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3],
                ),
                (
                    Addr::new(0x11423344),
                    Permissions::Read,
                    vec![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3],
                ),
                (
                    Addr::new(0x11523344),
                    Permissions::Read,
                    vec![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3],
                ),
            ]),
        );

        c.bench_function("Oracle::observe[XOR rax, rdx + 4 memory mappings]", |b| {
            b.iter(|| black_box(o.observe(&state2).unwrap()))
        });

        c.bench_function("Oracle::observe_carefully[XOR rax, rdx + 4 memory mappings]", |b| {
            b.iter(|| black_box(o.observe_carefully(&state2).unwrap()))
        });

        c.bench_function("Oracle::observe[XOR rax, rdx + 4 memory mappings alternating]", |b| {
            b.iter(|| {
                black_box(o.observe(&state).unwrap());
                black_box(o.observe(&state2).unwrap());
            })
        });
    })
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(60));
    targets = simple_oracle_observe
}
criterion_main!(benches);
