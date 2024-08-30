use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::fake::{FakeArch, FakeReg};
use liblisa::encoding::bitpattern::{
    Bit, FlowInputLocation, FlowValueLocation, ImmBitOrder, MappingOrBitOrder, Part, PartMapping,
};
use liblisa::encoding::dataflows::{
    AccessKind, AddressComputation, Dataflow, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses, Size, Source,
};
use liblisa::encoding::Encoding;
use liblisa::instr::Instruction;

fn instantiate1(c: &mut Criterion) {
    let encoding = Encoding::<FakeArch, ()> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
        ],
        errors: Vec::new(),
        parts: vec![Part {
            size: 3,
            value: 0,
            mapping: PartMapping::Register {
                mapping: vec![
                    Some(FakeReg::R0),
                    Some(FakeReg::R1),
                    Some(FakeReg::R2),
                    Some(FakeReg::R3),
                    Some(FakeReg::R4),
                    Some(FakeReg::R5),
                    Some(FakeReg::R6),
                    Some(FakeReg::R7),
                ],
                locations: vec![
                    FlowValueLocation::Output(0),
                    FlowValueLocation::InputForOutput {
                        output_index: 0,
                        input_index: 0,
                    },
                ],
            },
        }],
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr: Instruction::new(&[0x00, 0x00]),
                memory: vec![MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        write_ordering: Vec::new(),
    };

    c.bench_function("instantiate_1_reg", |b| {
        b.iter(|| {
            black_box(encoding.instantiate(&[5]).unwrap());
        })
    });
}

fn instantiate_4_reg(c: &mut Criterion) {
    let encoding = Encoding::<FakeArch, ()> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Part(3),
            Bit::Part(3),
            Bit::Part(3),
            Bit::Part(2),
            Bit::Part(2),
            Bit::Part(2),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Part(1),
            Bit::Part(1),
            Bit::Part(1),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
        ],
        errors: Vec::new(),
        parts: vec![
            Part {
                size: 3,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![
                        Some(FakeReg::R0),
                        Some(FakeReg::R1),
                        Some(FakeReg::R2),
                        Some(FakeReg::R3),
                        Some(FakeReg::R4),
                        Some(FakeReg::R5),
                        Some(FakeReg::R6),
                        Some(FakeReg::R7),
                    ],
                    locations: vec![
                        FlowValueLocation::Output(0),
                        FlowValueLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0,
                        },
                    ],
                },
            },
            Part {
                size: 3,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![
                        Some(FakeReg::R0),
                        Some(FakeReg::R1),
                        Some(FakeReg::R2),
                        Some(FakeReg::R3),
                        Some(FakeReg::R4),
                        Some(FakeReg::R5),
                        Some(FakeReg::R6),
                        Some(FakeReg::R7),
                    ],
                    locations: vec![
                        FlowValueLocation::Output(1),
                        FlowValueLocation::InputForOutput {
                            output_index: 1,
                            input_index: 0,
                        },
                    ],
                },
            },
            Part {
                size: 3,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![
                        Some(FakeReg::R0),
                        Some(FakeReg::R1),
                        Some(FakeReg::R2),
                        Some(FakeReg::R3),
                        Some(FakeReg::R4),
                        Some(FakeReg::R5),
                        Some(FakeReg::R6),
                        Some(FakeReg::R7),
                    ],
                    locations: vec![
                        FlowValueLocation::Output(2),
                        FlowValueLocation::InputForOutput {
                            output_index: 2,
                            input_index: 0,
                        },
                    ],
                },
            },
            Part {
                size: 3,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![
                        Some(FakeReg::R0),
                        Some(FakeReg::R1),
                        Some(FakeReg::R2),
                        Some(FakeReg::R3),
                        Some(FakeReg::R4),
                        Some(FakeReg::R5),
                        Some(FakeReg::R6),
                        Some(FakeReg::R7),
                    ],
                    locations: vec![
                        FlowValueLocation::Output(3),
                        FlowValueLocation::InputForOutput {
                            output_index: 3,
                            input_index: 0,
                        },
                    ],
                },
            },
        ],
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr: Instruction::new(&[0x00, 0x00]),
                memory: vec![MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    size: 3..3,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R1, Size::qword()),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R3, Size::qword()),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        },
        write_ordering: Vec::new(),
    };

    c.bench_function("instantiate_4_reg", |b| {
        b.iter(|| {
            black_box(encoding.instantiate(&[5, 3, 1, 4]).unwrap());
        })
    });
}

fn instantiate2(c: &mut Criterion) {
    let encoding = Encoding::<FakeArch, ()> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
        ],
        errors: Vec::new(),
        parts: vec![Part {
            size: 32,
            value: 0,
            mapping: PartMapping::Imm {
                mapping: Some(MappingOrBitOrder::BitOrder((0..32).map(ImmBitOrder::Positive).collect())),
                locations: vec![FlowInputLocation::MemoryAddress {
                    memory_index: 0,
                    input_index: 1,
                }],
                bits: None,
            },
        }],
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr: Instruction::new(&[0x00, 0x00, 0x00, 0x00, 0x00]),
                memory: vec![MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())), Source::Imm(0)]),
                    size: 5..5,
                    calculation: AddressComputation::unscaled_sum(2),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        write_ordering: Vec::new(),
    };

    c.bench_function("instantiate_1_mem_imm", |b| {
        b.iter(|| {
            black_box(encoding.instantiate(&[0x1234_5678]).unwrap());
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = instantiate1, instantiate_4_reg, instantiate2
}
criterion_main!(benches);
