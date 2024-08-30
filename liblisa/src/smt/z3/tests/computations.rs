use std::time::Duration;

use test_log::test;

use crate::arch::fake::FakeReg::{B0, R0, R1, R2, R3, RZ};
use crate::arch::fake::{FakeArch, FakeState};
use crate::compare::{ComputationEquivalence, EncodingComparisonOptions, PartIndexMapping};
use crate::encoding::bitpattern::{Bit, FlowInputLocation, FlowValueLocation, Part, PartMapping};
use crate::encoding::dataflows::{
    AccessKind, AddrTerm, AddrTermSize, AddressComputation, Dataflow, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses,
    Size, Source,
};
use crate::encoding::Encoding;
use crate::instr::{Instruction, InstructionFilter};
use crate::semantics::default::computation::{Arg, ArgEncoding, OutputEncoding, SynthesizedComputation};
use crate::semantics::default::ops::Op;
use crate::semantics::default::Expression;
use crate::semantics::IoType;
use crate::smt::z3::Z3Solver;
use crate::state::{Addr, MemoryState, Permissions, SystemState};
use crate::value::Value;

fn default_encoding_data() -> Encoding<FakeArch, SynthesizedComputation> {
    Encoding {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: MemoryAccesses {
                instr: Instruction::new(&[0]),
                memory: vec![MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R1, Size::new(0, 0)),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Const(1), Op::Add]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 8,
                        encoding: ArgEncoding::UnsignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: vec![],
        write_ordering: Vec::new(),
    }
}

#[test]
pub fn simple_equality() {
    let e1 = Encoding {
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: default_encoding_data().dataflows.addresses,
            outputs: vec![Dataflow {
                target: Dest::Reg(R1, Size::new(0, 0)),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Const(1), Op::Add]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 8,
                        encoding: ArgEncoding::UnsignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        ..default_encoding_data()
    };
    let e2 = Encoding {
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: default_encoding_data().dataflows.addresses,
            outputs: vec![Dataflow {
                target: Dest::Reg(R1, Size::new(0, 0)),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Const(1), Op::Hole(0), Op::Add]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 8,
                        encoding: ArgEncoding::UnsignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        ..default_encoding_data()
    };

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn extra_identity_assignments_are_equal() {
    let e1 = Encoding {
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: default_encoding_data().dataflows.addresses,
            outputs: vec![Dataflow {
                target: Dest::Reg(R1, Size::new(0, 0)),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Const(1), Op::Add]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 8,
                        encoding: ArgEncoding::UnsignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        ..default_encoding_data()
    };
    let e2 = Encoding {
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: default_encoding_data().dataflows.addresses,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(R1, Size::new(0, 0)),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                    computation: Some(SynthesizedComputation::new(
                        Expression::new(vec![Op::Const(1), Op::Hole(0), Op::Add]),
                        vec![Arg::Input {
                            index: 0,
                            num_bits: 8,
                            encoding: ArgEncoding::UnsignedBigEndian,
                        }],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer {
                            num_bits: 8,
                        },
                    )),
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(R1, Size::new(1, 1)),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(1, 1)))]),
                    computation: Some(SynthesizedComputation::new(
                        Expression::new(vec![Op::Const(0), Op::Hole(0), Op::Add]),
                        vec![Arg::Input {
                            index: 0,
                            num_bits: 8,
                            encoding: ArgEncoding::UnsignedBigEndian,
                        }],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer {
                            num_bits: 8,
                        },
                    )),
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        },
        ..default_encoding_data()
    };

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn extra_non_identity_assignments_are_not_equal() {
    let e1 = Encoding {
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: default_encoding_data().dataflows.addresses,
            outputs: vec![Dataflow {
                target: Dest::Reg(R1, Size::new(0, 0)),
                inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Const(1), Op::Add]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 8,
                        encoding: ArgEncoding::UnsignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        ..default_encoding_data()
    };
    let e2 = Encoding {
        dataflows: Dataflows::<FakeArch, SynthesizedComputation> {
            addresses: default_encoding_data().dataflows.addresses,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(R1, Size::new(0, 0)),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(0, 0)))]),
                    computation: Some(SynthesizedComputation::new(
                        Expression::new(vec![Op::Const(1), Op::Hole(0), Op::Add]),
                        vec![Arg::Input {
                            index: 0,
                            num_bits: 8,
                            encoding: ArgEncoding::UnsignedBigEndian,
                        }],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer {
                            num_bits: 8,
                        },
                    )),
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(R1, Size::new(1, 1)),
                    inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(R1, Size::new(1, 1)))]),
                    computation: Some(SynthesizedComputation::new(
                        Expression::new(vec![Op::Const(5), Op::Hole(0), Op::Add]),
                        vec![Arg::Input {
                            index: 0,
                            num_bits: 8,
                            encoding: ArgEncoding::UnsignedBigEndian,
                        }],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer {
                            num_bits: 8,
                        },
                    )),
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        },
        ..default_encoding_data()
    };

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::NotEqual
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::NotEqual
        );
    });
}

#[test]
pub fn check_encodings_riz_part_to_dontcares() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Fixed(0),
            Bit::Part(1),
            Bit::Part(1),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: vec![
                    MemoryAccess {
                        kind: AccessKind::Executable,
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
                        size: 2..2,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    },
                    MemoryAccess {
                        kind: AccessKind::InputOutput,
                        inputs: Inputs::sorted(vec![Dest::Reg(R1, Size::qword()).into(), Dest::Reg(R2, Size::qword()).into()]),
                        size: 8..8,
                        calculation: AddressComputation::unscaled_sum(2),
                        alignment: 1,
                    },
                ],
                use_trap_flag: false,
            },
            outputs: vec![],
            found_dependent_bytes: false,
        },
        parts: vec![
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::MemoryComputation {
                    mapping: vec![
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 2),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 4),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 8),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                    ],
                    memory_indexes: vec![1],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(RZ), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 1,
                        input_index: 1,
                    }],
                },
            },
        ],
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::DontCare,
            Bit::DontCare,
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: vec![
                    MemoryAccess {
                        kind: AccessKind::Executable,
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
                        size: 2..2,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    },
                    MemoryAccess {
                        kind: AccessKind::InputOutput,
                        inputs: Inputs::sorted(vec![Dest::Reg(R1, Size::qword()).into()]),
                        size: 8..8,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    },
                ],
                use_trap_flag: false,
            },
            outputs: vec![],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_equivalent_with_imm_cropping() {
    let base1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr: Instruction::new(&[0x00]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::qword()),
                inputs: Inputs::unsorted(vec![Dest::Reg(R0, Size::qword()).into(), Source::Imm(0)]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![
                        Op::Hole(0),
                        Op::Hole(1),
                        Op::SignExtend {
                            num_bits: 7,
                        },
                        Op::Add,
                    ]),
                    vec![
                        Arg::Input {
                            index: 0,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                        Arg::Input {
                            index: 1,
                            num_bits: 7,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                    ],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: vec![Part {
            size: 7,
            value: 0,
            mapping: PartMapping::Imm {
                mapping: None,
                locations: vec![FlowInputLocation::InputForOutput {
                    output_index: 0,
                    input_index: 1,
                }],
                bits: None,
            },
        }],
        write_ordering: Vec::new(),
    };
    let base2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Fixed(1),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr: Instruction::new(&[0x40]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::qword()),
                inputs: Inputs::unsorted(vec![Dest::Reg(R0, Size::qword()).into(), Source::Imm(0)]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![
                        Op::Hole(0),
                        Op::Hole(1),
                        Op::Const(0b0100_0000),
                        Op::Or,
                        Op::SignExtend {
                            num_bits: 7,
                        },
                        Op::Add,
                    ]),
                    vec![
                        Arg::Input {
                            index: 0,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                        Arg::Input {
                            index: 1,
                            num_bits: 7,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                    ],
                    Vec::new(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: vec![Part {
            size: 6,
            value: 0,
            mapping: PartMapping::Imm {
                mapping: None,
                locations: vec![FlowInputLocation::InputForOutput {
                    output_index: 0,
                    input_index: 1,
                }],
                bits: None,
            },
        }],
        write_ordering: Vec::new(),
    };

    println!("{base1}");
    println!("{base2}");

    let filter_a = InstructionFilter::parse("0100____");
    let filter_b = InstructionFilter::parse("01__1_1_");
    let filter_c = InstructionFilter::parse("01001011");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let e1 = base1.restrict_to(&filter_a).unwrap().restrict_to(&filter_c).unwrap();
        let e2 = base2.restrict_to(&filter_c).unwrap();

        println!("{e1}");
        println!("{e2}");

        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let e1 = base1.restrict_to(&filter_a).unwrap().restrict_to(&filter_b).unwrap();
        let e2 = base1.restrict_to(&filter_b).unwrap().restrict_to(&filter_a).unwrap();

        println!("{e1}");
        println!("{e2}");

        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let e1 = base1.restrict_to(&filter_a).unwrap();
        let e2 = base2.restrict_to(&filter_a).unwrap();

        println!("{e1}");
        println!("{e2}");

        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_equivalent_when_split1() {
    let or_bits = |num_bits| {
        Some(SynthesizedComputation::new(
            Expression::new(vec![Op::Hole(0), Op::Hole(1), Op::Or]),
            vec![
                Arg::Input {
                    index: 0,
                    num_bits,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ],
            Vec::new(),
            OutputEncoding::UnsignedBigEndian,
            IoType::Integer {
                num_bits: num_bits as usize,
            },
        ))
    };
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 3)),
                inputs: Inputs::unsorted(vec![
                    Dest::Reg(R0, Size::new(0, 3)).into(),
                    Dest::Reg(R1, Size::new(0, 3)).into(),
                ]),
                computation: or_bits(32),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::DontCare,
            Bit::DontCare,
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(R0, Size::new(0, 0)),
                    inputs: Inputs::unsorted(vec![
                        Dest::Reg(R0, Size::new(0, 0)).into(),
                        Dest::Reg(R1, Size::new(0, 0)).into(),
                    ]),
                    computation: or_bits(8),
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(R0, Size::new(1, 1)),
                    inputs: Inputs::unsorted(vec![
                        Dest::Reg(R0, Size::new(1, 1)).into(),
                        Dest::Reg(R1, Size::new(1, 1)).into(),
                    ]),
                    computation: or_bits(8),
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(R0, Size::new(2, 3)),
                    inputs: Inputs::unsorted(vec![
                        Dest::Reg(R0, Size::new(2, 3)).into(),
                        Dest::Reg(R1, Size::new(2, 3)).into(),
                    ]),
                    computation: or_bits(16),
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_equivalent_when_split2() {
    // m1[0..0]   := Select[12:+8](sbe(<c>[5..7]))
    // m1[1..7]   := (sle(m1[0..6]) << 4) | Select[20:+4](ube(<c>[5..7]))

    // vs.

    // m1[0..7]   := (ube(<c>[6..7]) | (ule(m1[0..6]) << 16)) >> 4
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: vec![MemoryAccess {
                    kind: AccessKind::InputOutput,
                    calculation: AddressComputation::unscaled_sum(0),
                    inputs: Inputs::default(),
                    size: 8..8,
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Mem(0, Size::new(0, 0)),
                    inputs: Inputs::unsorted(vec![Dest::Reg(R1, Size::new(5, 7)).into()]),
                    computation: Some(SynthesizedComputation::new(
                        Expression::new(vec![
                            Op::Hole(0),
                            Op::Select {
                                num_skip: 12,
                                num_take: 8,
                            },
                        ]),
                        vec![Arg::Input {
                            index: 0,
                            num_bits: 24,
                            encoding: ArgEncoding::SignedBigEndian,
                        }],
                        Vec::new(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Bytes {
                            num_bytes: 1,
                        },
                    )),
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Mem(0, Size::new(1, 7)),
                    inputs: Inputs::unsorted(vec![
                        Dest::Reg(R0, Size::new(0, 6)).into(),
                        Dest::Reg(R1, Size::new(5, 7)).into(),
                    ]),
                    computation: Some(SynthesizedComputation::new(
                        Expression::new(vec![
                            Op::Hole(0),
                            Op::Const(4),
                            Op::Shl,
                            Op::Hole(1),
                            Op::Select {
                                num_skip: 20,
                                num_take: 4,
                            },
                            Op::Or,
                        ]),
                        vec![
                            Arg::Input {
                                index: 0,
                                num_bits: 56,
                                encoding: ArgEncoding::SignedLittleEndian,
                            },
                            Arg::Input {
                                index: 1,
                                num_bits: 24,
                                encoding: ArgEncoding::UnsignedBigEndian,
                            },
                        ],
                        Vec::new(),
                        OutputEncoding::UnsignedLittleEndian,
                        IoType::Bytes {
                            num_bytes: 8,
                        },
                    )),
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::DontCare,
            Bit::DontCare,
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: vec![MemoryAccess {
                    kind: AccessKind::InputOutput,
                    calculation: AddressComputation::unscaled_sum(0),
                    inputs: Inputs::default(),
                    size: 8..8,
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Mem(0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![
                    Dest::Reg(R0, Size::new(0, 6)).into(),
                    Dest::Reg(R1, Size::new(6, 7)).into(),
                ]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![
                        Op::Hole(1),
                        Op::Hole(0),
                        Op::Const(16),
                        Op::Shl,
                        Op::Or,
                        Op::Const(4),
                        Op::Shr,
                    ]),
                    vec![
                        Arg::Input {
                            index: 0,
                            num_bits: 56,
                            encoding: ArgEncoding::UnsignedLittleEndian,
                        },
                        Arg::Input {
                            index: 1,
                            num_bits: 24,
                            encoding: ArgEncoding::UnsignedBigEndian,
                        },
                    ],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Bytes {
                        num_bytes: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    let mut initial_state = SystemState::<FakeArch>::new(
        FakeState::default(),
        MemoryState::new([(Addr::new(0), Permissions::ReadWrite, vec![0; 8])].into_iter()),
    );
    initial_state.set_reg(R1, Value::Num(0x10000000000000));

    let mut state_e1 = initial_state.clone();
    let mut state_e2 = initial_state.clone();

    e1.instantiate(&[]).unwrap().execute(&mut state_e1);
    e2.instantiate(&[]).unwrap().execute(&mut state_e2);

    println!("Test e1: {state_e1:#X?}");
    println!("Test e2: {state_e2:#X?}");

    assert_eq!(state_e1, state_e2);

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_carryless_mul_performance() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![
                    Dest::Reg(R0, Size::new(0, 7)).into(),
                    Dest::Reg(R1, Size::new(0, 7)).into(),
                ]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Hole(1), Op::CarrylessMul]),
                    vec![
                        Arg::Input {
                            index: 0,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                        Arg::Input {
                            index: 0,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                    ],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::DontCare,
            Bit::DontCare,
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![
                    Dest::Reg(R0, Size::new(0, 7)).into(),
                    Dest::Reg(R1, Size::new(0, 7)).into(),
                ]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(1), Op::Hole(0), Op::CarrylessMul]),
                    vec![
                        Arg::Input {
                            index: 0,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                        Arg::Input {
                            index: 0,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                    ],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_imm_vs_dontcare_equivalent() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![Source::Imm(0)]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Const(0), Op::Const(5), Op::IfZero]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 64,
                        encoding: ArgEncoding::SignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: vec![Part {
            size: 4,
            value: 0,
            mapping: PartMapping::Imm {
                mapping: None,
                locations: vec![FlowInputLocation::InputForOutput {
                    output_index: 0,
                    input_index: 0,
                }],
                bits: None,
            },
        }],
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::DontCare,
            Bit::DontCare,
            Bit::DontCare,
            Bit::Fixed(1),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 7)),
                inputs: Inputs::default(),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Const(5)]),
                    Vec::new(),
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    let e1 = e1.restrict_to(&e2.bitpattern_as_filter()).unwrap();
    let e2 = e2.restrict_to(&e1.bitpattern_as_filter()).unwrap();

    println!("{e1}");
    println!("{e2}");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        println!("Checking e1 vs e2");
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        println!("Checking e2 vs e1");
        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_reg_vs_dontcare_equivalent() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![
                    Dest::Reg(R0, Size::new(3, 3)).into(),
                    Dest::Reg(R0, Size::new(0, 7)).into(),
                    Dest::Reg(R0, Size::new(0, 7)).into(),
                ]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0), Op::Hole(1), Op::Hole(2), Op::IfZero]),
                    vec![
                        Arg::Input {
                            index: 0,
                            num_bits: 8,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                        Arg::Input {
                            index: 1,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                        Arg::Input {
                            index: 2,
                            num_bits: 64,
                            encoding: ArgEncoding::SignedBigEndian,
                        },
                    ],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: vec![Part {
            size: 2,
            value: 0,
            mapping: PartMapping::Register {
                mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                locations: vec![FlowValueLocation::InputForOutput {
                    output_index: 0,
                    input_index: 0,
                }],
            },
        }],
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::DontCare,
            Bit::DontCare,
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(R0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![Dest::Reg(R0, Size::new(0, 7)).into()]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![Op::Hole(0)]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 64,
                        encoding: ArgEncoding::SignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Integer {
                        num_bits: 64,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    let e1 = e1.restrict_to(&e2.bitpattern_as_filter()).unwrap();
    let e2 = e2.restrict_to(&e1.bitpattern_as_filter()).unwrap();

    println!("{e1}");
    println!("{e2}");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        println!("Checking e1 vs e2");
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        println!("Checking e2 vs e1");
        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}

#[test]
pub fn check_byte_value_orderings() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(B0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![Dest::Reg(B0, Size::new(0, 3)).into()]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![
                        Op::Hole(0),
                        Op::Select {
                            num_skip: 7,
                            num_take: 1,
                        },
                    ]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 32,
                        encoding: ArgEncoding::SignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Bytes {
                        num_bytes: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
            Bit::Fixed(0),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(B0, Size::new(0, 7)),
                inputs: Inputs::unsorted(vec![Dest::Reg(B0, Size::new(3, 3)).into()]),
                computation: Some(SynthesizedComputation::new(
                    Expression::new(vec![
                        Op::Hole(0),
                        Op::Select {
                            num_skip: 7,
                            num_take: 1,
                        },
                    ]),
                    vec![Arg::Input {
                        index: 0,
                        num_bits: 8,
                        encoding: ArgEncoding::SignedBigEndian,
                    }],
                    Vec::new(),
                    OutputEncoding::UnsignedLittleEndian,
                    IoType::Bytes {
                        num_bytes: 8,
                    },
                )),
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        },
        parts: Vec::new(),
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    let base_state = {
        let mut s: SystemState<FakeArch> = SystemState::new_without_memory(FakeState::default());
        s.set_reg(B0, Value::Bytes(&[0, 0, 0, 0x80, 0, 0, 0, 0]));
        s
    };

    println!("Base state: {base_state:#X?}");
    let mut s1 = base_state.clone();
    let mut s2 = base_state.clone();

    e1.instantiate(&[]).unwrap().execute(&mut s1);
    println!("s1: {s1:#?}");

    e2.instantiate(&[]).unwrap().execute(&mut s2);
    println!("s2: {s2:#?}");

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        println!("Checking e1 vs e2");
        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e1, &e2, &mut context),
            ComputationEquivalence::Equal
        );

        println!("Checking e2 vs e1");
        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert_eq!(
            ComputationEquivalence::of(&mapping, &EncodingComparisonOptions::default(), &e2, &e1, &mut context),
            ComputationEquivalence::Equal
        );
    });
}
