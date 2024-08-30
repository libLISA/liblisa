use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::fake::AnyArea;
use liblisa::arch::x64::{GpReg, X64Arch, X64Reg};
use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{AccessKind, AddressComputation, Dest, Inputs, MemoryAccess, MemoryAccesses, Size};
use liblisa::instr::Instruction;
use liblisa::state::random::StateGen;
use liblisa::state::{Addr, Location, MemoryState, Permissions, SystemState};
use liblisa::value::Value;
use rand::SeedableRng;
use rand_xoshiro::Xoshiro256PlusPlus;

fn create(c: &mut Criterion) {
    c.bench_function("SystemState::create", |b| {
        b.iter(|| {
            let state = SystemState::<X64Arch>::new(
                Default::default(),
                MemoryState::from_vec(vec![(
                    Addr::new(0x0),
                    Permissions::Execute,
                    vec![0x00, 0xf0, 0x20, 0x50, 0x99, 0xab],
                )]),
            );

            black_box(state);
        })
    });
}

fn randomize_new(c: &mut Criterion) {
    let accesses = MemoryAccesses::<X64Arch> {
        instr: Instruction::new(&[0x01]),
        memory: vec![
            MemoryAccess {
                kind: AccessKind::Executable,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rip), Size::qword()).into()]),
                size: 2..2,
                calculation: AddressComputation::unscaled_sum(1),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![
                    Dest::Reg(X64Reg::GpReg(GpReg::Rax), Size::qword()).into(),
                    Dest::Reg(X64Reg::GpReg(GpReg::Rbx), Size::qword()).into(),
                ]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(2),
                alignment: 1,
            },
        ],
        use_trap_flag: true,
    };

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    let sg = StateGen::new(&accesses, &AnyArea).unwrap();

    c.bench_function("SystemState::randomize_new", |b| {
        b.iter(|| {
            black_box(sg.randomize_new(&mut rng).unwrap());
        })
    });
}

fn randomize_new_big(c: &mut Criterion) {
    let accesses = MemoryAccesses::<X64Arch> {
        instr: Instruction::new(&[0xC8, 0x03, 0x02, 0x10]),
        memory: vec![
            MemoryAccess {
                kind: AccessKind::Executable,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rip), Size::qword()).into()]),
                size: 4..4,
                calculation: AddressComputation::unscaled_sum(1),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x8),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x8),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x10),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x10),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x18),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x18),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x20),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x20),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x28),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x28),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x30),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x30),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x38),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x38),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x40),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x40),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x48),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x48),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x50),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x50),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x58),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x58),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x60),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x60),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x68),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x68),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x70),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x70),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x78),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rbp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(0x78),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x80),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 8..8,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x88),
                alignment: 1,
            },
            MemoryAccess {
                kind: AccessKind::InputOutput,
                inputs: Inputs::sorted(vec![Dest::Reg(X64Reg::GpReg(GpReg::Rsp), Size::qword()).into()]),
                size: 1..1,
                calculation: AddressComputation::unscaled_sum(1).with_offset(-0x28B),
                alignment: 1,
            },
        ],
        use_trap_flag: false,
    };

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    let sg = StateGen::new(&accesses, &AnyArea).unwrap();

    c.bench_function("SystemState::randomize_new::big", |b| {
        b.iter(|| {
            black_box(sg.randomize_new(&mut rng).unwrap());
        })
    });
}

fn clone(c: &mut Criterion) {
    let state = SystemState::<X64Arch>::new(
        Default::default(),
        MemoryState::from_vec(vec![(
            Addr::new(0x0),
            Permissions::Execute,
            vec![0x00, 0xf0, 0x20, 0x50, 0x99, 0xab],
        )]),
    );

    c.bench_function("SystemState::clone", |b| {
        b.iter(|| {
            black_box(state.clone());
        })
    });
}

fn set_single_location(c: &mut Criterion) {
    let mut state = SystemState::<X64Arch>::new(
        Default::default(),
        MemoryState::from_vec(vec![(
            Addr::new(0x0),
            Permissions::Execute,
            vec![0x00, 0xf0, 0x20, 0x50, 0x99, 0xab],
        )]),
    );

    let input_locations: Vec<Location<X64Arch>> = X64Arch::iter_regs().map(Location::Reg).collect::<Vec<_>>();

    c.bench_function("SystemState::set_location", |b| {
        b.iter(|| {
            for loc in input_locations.iter() {
                state.set_location(loc, Value::Num(10));
            }

            black_box(&state);
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(30));
    targets = create, clone, set_single_location, randomize_new, randomize_new_big
}
criterion_main!(benches);
