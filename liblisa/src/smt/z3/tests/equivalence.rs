use std::time::Duration;

use test_log::test;

use crate::arch::fake::FakeArch;
use crate::arch::fake::FakeReg::{R0, R1, R2, R3, RZ};
use crate::compare::{encodings_semantically_equal, encodings_structurally_equal, Equivalence};
use crate::encoding::bitpattern::{Bit, FlowValueLocation, Part, PartMapping};
use crate::encoding::dataflows::{
    AccessKind, AddrTerm, AddrTermSize, AddressComputation, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses, Size,
};
use crate::encoding::Encoding;
use crate::instr::Instruction;
use crate::semantics::default::computation::SynthesizedComputation;
use crate::smt::z3::Z3Solver;
use crate::smt::{CachedSolver, MemoryCache};

#[test]
pub fn check_encodings_equal_different_addr_computations() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, _> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(1),
            Bit::Part(1),
            Bit::Part(2),
            Bit::Part(2),
            Bit::Part(3),
            Bit::Part(3),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: vec![MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![
                        Dest::Reg(R0, Size::qword()).into(),
                        Dest::Reg(R1, Size::qword()).into(),
                        Dest::Reg(R2, Size::qword()).into(),
                    ]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![],
            found_dependent_bytes: false,
        },
        parts: vec![
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 0,
                    }],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 1,
                    }],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 2,
                    }],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::MemoryComputation {
                    mapping: vec![
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 1),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 2),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 4),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::single(AddrTermSize::U64, 0, 8),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                    ],
                    memory_indexes: vec![0],
                },
            },
        ],
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, _> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(1),
            Bit::Part(1),
            Bit::Part(2),
            Bit::Part(2),
            Bit::Part(3),
            Bit::Part(3),
        ],
        errors: std::iter::repeat(false).take(16).collect(),
        dataflows: Dataflows {
            addresses: MemoryAccesses {
                instr,
                memory: vec![MemoryAccess {
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![
                        Dest::Reg(R0, Size::qword()).into(),
                        Dest::Reg(R1, Size::qword()).into(),
                        Dest::Reg(R2, Size::qword()).into(),
                    ]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![],
            found_dependent_bytes: false,
        },
        parts: vec![
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 1,
                    }],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 0,
                    }],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 2,
                    }],
                },
            },
            Part {
                size: 2,
                value: 0,
                mapping: PartMapping::MemoryComputation {
                    mapping: vec![
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 1),
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 2),
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 4),
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 8),
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                    ],
                    memory_indexes: vec![0],
                },
            },
        ],
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");
    // assert!(encodings_structurally_equal(&Default::default(), &e1, &e2));

    Z3Solver::with_thread_local(Duration::from_secs(900), |context| {
        let mut context = CachedSolver::new(context, MemoryCache::new());

        assert_eq!(
            encodings_semantically_equal(&Default::default(), &e1, &e2, &mut context),
            Equivalence {
                equal: true,
                timeout: false,
            }
        );
    });
}

#[test]
pub fn check_encodings_riz_vs_memmapping_equal() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(1),
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
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into(), Dest::Reg(R1, Size::qword()).into()]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
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
                                AddrTerm::single(AddrTermSize::U64, 0, 1),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 2),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 4),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 8),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                    ],
                    memory_indexes: vec![0],
                },
            },
            Part {
                size: 1,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R1), Some(RZ)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 1,
                    }],
                },
            },
        ],
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
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
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into(), Dest::Reg(R1, Size::qword()).into()]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![],
            found_dependent_bytes: false,
        },
        parts: vec![Part {
            size: 3,
            value: 0,
            mapping: PartMapping::MemoryComputation {
                mapping: vec![
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 1),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 2),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 4),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 8),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 1),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 2),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 4),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 8),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                ],
                memory_indexes: vec![0],
            },
        }],
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    assert!(encodings_structurally_equal(&Default::default(), &e1, &e2));

    Z3Solver::with_thread_local(Duration::from_secs(900), |context| {
        let mut context = CachedSolver::new(context, MemoryCache::new());

        assert_eq!(
            encodings_semantically_equal(&Default::default(), &e1, &e2, &mut context),
            Equivalence {
                equal: true,
                timeout: false,
            }
        );
    });
}

#[test]
pub fn check_encodings_riz_vs_memmapping_notequal() {
    let instr = Instruction::new(&[0x00]);
    let e1 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(1),
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
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into(), Dest::Reg(R2, Size::qword()).into()]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
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
                                AddrTerm::single(AddrTermSize::U64, 0, 1),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 2),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 4),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::single(AddrTermSize::U64, 0, 8),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                                AddrTerm::default(),
                            ],
                        }),
                    ],
                    memory_indexes: vec![0],
                },
            },
            Part {
                size: 1,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R2), Some(RZ)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 1,
                    }],
                },
            },
        ],
        write_ordering: Vec::new(),
    };

    let e2 = Encoding::<FakeArch, SynthesizedComputation> {
        bits: vec![
            Bit::Part(0),
            Bit::Part(0),
            Bit::Part(0),
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
                    kind: AccessKind::Executable,
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into(), Dest::Reg(R1, Size::qword()).into()]),
                    size: 2..2,
                    calculation: AddressComputation::unscaled_sum(1),
                    alignment: 1,
                }],
                use_trap_flag: false,
            },
            outputs: vec![],
            found_dependent_bytes: false,
        },
        parts: vec![Part {
            size: 3,
            value: 0,
            mapping: PartMapping::MemoryComputation {
                mapping: vec![
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 1),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 2),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 4),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 8),
                            AddrTerm::identity(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 1),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 2),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 4),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                    Some(AddressComputation {
                        offset: 0,
                        terms: [
                            AddrTerm::single(AddrTermSize::U64, 0, 8),
                            AddrTerm::default(),
                            AddrTerm::default(),
                            AddrTerm::default(),
                        ],
                    }),
                ],
                memory_indexes: vec![0],
            },
        }],
        write_ordering: Vec::new(),
    };

    println!("{e1}");
    println!("{e2}");

    assert!(!encodings_structurally_equal(&Default::default(), &e1, &e2));

    Z3Solver::with_thread_local(Duration::from_secs(900), |context| {
        let mut context = CachedSolver::new(context, MemoryCache::new());

        assert_eq!(
            encodings_semantically_equal(&Default::default(), &e1, &e2, &mut context),
            Equivalence {
                equal: false,
                timeout: false,
            }
        );
    });
}
