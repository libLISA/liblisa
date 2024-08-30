use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::x64::{GpReg, X64Arch, X64Reg, XmmReg};
use liblisa::arch::CpuState;
use liblisa::encoding::dataflows::MemoryAccesses;
use liblisa::instr::Instruction;
use liblisa::oracle::MappableArea;
use liblisa::state::random::StateGen;
use liblisa::state::{Addr, MemoryState, Permissions, StateByte, SystemState, SystemStateByteView};
use liblisa::value::MutValue;
use rand::SeedableRng;
use rand_xoshiro::Xoshiro256PlusPlus;

#[derive(Copy, Clone, Debug)]
struct Everything;

impl MappableArea for Everything {
    fn can_map(&self, _: Addr) -> bool {
        true
    }
}

pub fn find_differences1(c: &mut Criterion) {
    let empty1 = SystemState::<X64Arch>::default();
    let empty2 = SystemState::<X64Arch>::default();

    let accesses = MemoryAccesses::<X64Arch> {
        instr: Instruction::new(&[0x01]),
        memory: Vec::new(),
        use_trap_flag: true,
    };

    let view = SystemStateByteView::new(&accesses);

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    let gen = StateGen::new(&accesses, &Everything).unwrap();
    let random1 = gen.randomize_new(&mut rng).unwrap();
    let random2 = gen.randomize_new(&mut rng).unwrap();

    c.bench_function("find_differences_empty_empty", |b| {
        b.iter(|| {
            view.find_differences(&empty1, &empty2, &mut |byte| {
                black_box(byte);
            })
        })
    });

    c.bench_function("find_differences_random_random", |b| {
        b.iter(|| {
            view.find_differences(&random1, &random2, &mut |byte| {
                black_box(byte);
            })
        })
    });
}

fn find_differences2(c: &mut Criterion) {
    let state = SystemState::<X64Arch>::new(
        Default::default(),
        MemoryState::from_vec(vec![(
            Addr::new(0x0),
            Permissions::Execute,
            vec![0x00, 0xf0, 0x20, 0x50, 0x99, 0xab],
        )]),
    );

    let mut state2 = SystemState::<X64Arch>::new(
        Default::default(),
        MemoryState::from_vec(vec![(
            Addr::new(0x0),
            Permissions::Execute,
            vec![0x00, 0xf0, 0x20, 0x50, 0x99, 0xab],
        )]),
    );

    CpuState::<X64Arch>::set_gpreg(&mut *state2.cpu_mut(), GpReg::Rip, 50);

    let accesses = MemoryAccesses::<X64Arch> {
        instr: Instruction::new(&[0x01]),
        memory: Vec::new(),
        use_trap_flag: true,
    };
    let view = SystemStateByteView::new(&accesses);

    c.bench_function("find_differences-1", |b| {
        b.iter(|| {
            view.find_differences(&state, &state2, &mut |v| {
                black_box(v);
            });
        })
    });

    CpuState::<X64Arch>::set_gpreg(&mut *state2.cpu_mut(), GpReg::Rip, 0xffff_ffff_ffff_ffff);
    c.bench_function("find_differences-8", |b| {
        b.iter(|| {
            view.find_differences(&state, &state2, &mut |v| {
                black_box(v);
            });
        })
    });

    CpuState::<X64Arch>::set_gpreg(&mut *state2.cpu_mut(), GpReg::Rip, 0xffff_ffff_ffff_ffff);
    CpuState::<X64Arch>::modify_reg(&mut *state2.cpu_mut(), X64Reg::Xmm(XmmReg::Reg(1)), |v| match v {
        MutValue::Bytes(b) => b.fill(0xff),
        _ => todo!(),
    });

    c.bench_function("find_differences-40", |b| {
        b.iter(|| {
            view.find_differences(&state, &state2, &mut |v| {
                black_box(v);
            });
        })
    });

    CpuState::<X64Arch>::set_gpreg(&mut *state2.cpu_mut(), GpReg::Rip, 0xffff_ffff_ffff_ffff);
    CpuState::<X64Arch>::modify_reg(&mut *state2.cpu_mut(), X64Reg::Xmm(XmmReg::Reg(2)), |v| match v {
        MutValue::Bytes(b) => b.fill(0xff),
        _ => todo!(),
    });
    CpuState::<X64Arch>::modify_reg(&mut *state2.cpu_mut(), X64Reg::Xmm(XmmReg::Reg(5)), |v| match v {
        MutValue::Bytes(b) => b.fill(0xff),
        _ => todo!(),
    });
    CpuState::<X64Arch>::modify_reg(&mut *state2.cpu_mut(), X64Reg::Xmm(XmmReg::Reg(8)), |v| match v {
        MutValue::Bytes(b) => b.fill(0xff),
        _ => todo!(),
    });

    c.bench_function("find_differences-136", |b| {
        b.iter(|| {
            view.find_differences(&state, &state2, &mut |v| {
                black_box(v);
            });
        })
    });

    let dest_diff_mask = Default::default();
    let diff_mask = SystemStateByteView::<X64Arch>::create_diff_mask(
        &view,
        (0..SystemStateByteView::<X64Arch>::size(&view)).map(StateByte::new),
    );
    c.bench_function("find_differences_with_mask-0-136", |b| {
        b.iter(|| {
            view.find_dataflows_masked(
                (&state, &state2).into(),
                (&state, &state2).into(),
                &dest_diff_mask,
                &diff_mask,
                &mut |v| {
                    black_box(v);
                },
            );
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = find_differences2, find_differences1
}
criterion_main!(benches);
