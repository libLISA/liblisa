//! Provides various ways to compare [`crate::encoding::Encoding`]s.
//!
//! Some of the comparisons require an [`crate::smt::SmtSolver`].
//! You can use the `liblisa-z3` crate to import bindings to the Z3 SMT solver.

use std::collections::{HashMap, HashSet};

use log::trace;

use crate::arch::Arch;
use crate::encoding::bitpattern::{Bit, FlowInputLocation, FlowValueLocation, MappingOrBitOrder, PartMapping};
use crate::encoding::{Encoding, RestrictError};
use crate::semantics::default::computation::SynthesizedComputation;
use crate::semantics::Computation;
use crate::smt::SmtSolver;

mod addresses;
mod computations;
mod group;
mod mapping;
mod rows;
mod split;
pub mod summary;

pub use addresses::*;
pub use computations::*;
pub use group::*;
pub use mapping::*;
pub use rows::*;
pub use split::*;

/// Options for comparing [`Encoding`]s.
#[derive(Clone, Debug, Default)]
pub struct EncodingComparisonOptions {
    /// Comparison options for the address comparison.
    pub addresses: AddressComparisonOptions,

    /// When set to true, comparing a computation against a missing (i.e., not synthesized) computation is treated as equivalent.
    pub treat_missing_as_equal: bool,
}

impl EncodingComparisonOptions {
    /// Creates new comparison options with all fields set to `false`.
    pub const fn new() -> Self {
        EncodingComparisonOptions {
            addresses: AddressComparisonOptions::new(),
            treat_missing_as_equal: false,
        }
    }
}

fn bits_equal_with_mapping(_mapping: &PartIndexMapping, a: &[Bit], b: &[Bit]) -> bool {
    for (&bit_a, &bit_b) in a.iter().zip(b.iter()) {
        match (bit_a, bit_b) {
            (Bit::DontCare, Bit::DontCare) => (),
            // TODO: Is there some case where we would still want to return false, even if we have a valid part mapping?
            (Bit::Part(_x), Bit::Part(_y)) => (),
            (Bit::Part(_), Bit::Fixed(_) | Bit::DontCare)
            | (Bit::Fixed(_), Bit::Part(_) | Bit::DontCare)
            | (Bit::DontCare, Bit::Fixed(_) | Bit::Part(_)) => (),
            (Bit::Fixed(_x), Bit::Fixed(_y)) => (),
        }
    }

    true
}

/// Only compares the overlapping parts of the covered instruction space.
pub fn encodings_structurally_equal<A: Arch, C: Computation + PartialEq>(
    options: &EncodingComparisonOptions, a: &Encoding<A, C>, b: &Encoding<A, C>,
) -> bool {
    // Compare bits
    trace!("Comparing bits...");
    let mapping = match PartIndexMapping::of(a, b) {
        Some(mapping) => mapping,
        _ => return false,
    };

    bits_equal_with_mapping(&mapping, &a.bits, &b.bits)
        && encoding_addresses_equal(&mapping, &options.addresses, a, b)
        && encoding_dataflow_parts_equal(&mapping, a, b)
        && encoding_dataflows_structurally_equal(&mapping, a, b)
}

/// Determines if the dataflows of the encodings provided are equal, ignoring the actual computations.
/// Only compares the overlapping parts of the covered instruction space.
pub fn encoding_dataflows_structurally_equal<A: Arch, C: PartialEq>(
    mapping: &PartIndexMapping, a: &Encoding<A, C>, b: &Encoding<A, C>,
) -> bool {
    trace!("Comparing outputs...");
    if !mapping.dataflow_regs.all_indices_mapped() {
        return false
    }

    let a_outputs = a
        .dataflows
        .outputs
        .iter()
        .enumerate()
        .map(|(output_index, flow)| {
            let target = a
                .parts
                .iter()
                .enumerate()
                .find(|(_, part)| match &part.mapping {
                    PartMapping::Register {
                        locations, ..
                    } => locations.contains(&FlowValueLocation::Output(output_index)),
                    _ => false,
                })
                .map(|(part_index, _)| FilledOutput::Part(PartIndex::new(mapping, part_index, true), flow.target.size()))
                .unwrap_or_else(|| FilledOutput::Concrete(flow.target));
            (target, (output_index, flow))
        })
        .collect::<HashMap<_, _>>();

    let b_outputs = b
        .dataflows
        .outputs
        .iter()
        .enumerate()
        .map(|(output_index, flow)| {
            let target = b
                .parts
                .iter()
                .enumerate()
                .find(|(_, part)| match &part.mapping {
                    PartMapping::Register {
                        locations, ..
                    } => locations.contains(&FlowValueLocation::Output(output_index)),
                    _ => false,
                })
                .map(|(part_index, _)| FilledOutput::Part(PartIndex::new(mapping, part_index, false), flow.target.size()))
                .unwrap_or_else(|| FilledOutput::Concrete(flow.target));
            (target, (output_index, flow))
        })
        .collect::<HashMap<_, _>>();

    if a_outputs.len() != b_outputs.len() {
        trace!("Output length difference: {} vs {}", a_outputs.len(), b_outputs.len());
        return false
    }

    for (target, (output_index_a, flow_a)) in a_outputs {
        if let Some(&(output_index_b, flow_b)) = b_outputs.get(&target) {
            let a_inputs = flow_a
                .inputs
                .iter()
                .enumerate()
                .map(|(input_index, &input)| {
                    a.parts
                        .iter()
                        .enumerate()
                        .find(|(_, part)| match &part.mapping {
                            PartMapping::Imm {
                                locations, ..
                            } => locations.contains(&FlowInputLocation::InputForOutput {
                                output_index: output_index_a,
                                input_index,
                            }),
                            PartMapping::Register {
                                locations, ..
                            } => locations.contains(&FlowValueLocation::InputForOutput {
                                output_index: output_index_a,
                                input_index,
                            }),
                            _ => false,
                        })
                        .map(|(part_index, _)| FilledInput::Part(PartIndex::new(mapping, part_index, true), input.size()))
                        .unwrap_or_else(|| FilledInput::Concrete(input))
                })
                .collect::<HashSet<_>>();

            let b_inputs = flow_b
                .inputs
                .iter()
                .enumerate()
                .map(|(input_index, &input)| {
                    b.parts
                        .iter()
                        .enumerate()
                        .find(|(_, part)| match &part.mapping {
                            PartMapping::Imm {
                                locations, ..
                            } => locations.contains(&FlowInputLocation::InputForOutput {
                                output_index: output_index_b,
                                input_index,
                            }),
                            PartMapping::Register {
                                locations, ..
                            } => locations.contains(&FlowValueLocation::InputForOutput {
                                output_index: output_index_b,
                                input_index,
                            }),
                            _ => false,
                        })
                        .map(|(part_index, _)| FilledInput::Part(PartIndex::new(mapping, part_index, false), input.size()))
                        .unwrap_or_else(|| FilledInput::Concrete(input))
                })
                .collect::<HashSet<_>>();

            if a_inputs != b_inputs {
                trace!("Inputs for target {target:?} are not equal: {a_inputs:?} vs. {b_inputs:?}");
                return false
            }
        } else {
            trace!("Target A: {target:?}, not found in B");
            return false
        }
    }

    true
}

fn encoding_dataflow_parts_equal<A: Arch, C: PartialEq>(
    mapping: &PartIndexMapping, a: &Encoding<A, C>, b: &Encoding<A, C>,
) -> bool {
    trace!("Comparing parts...");

    for ((_, part_a), (_, part_b)) in mapping.iter_dataflow_involved_parts(a, b) {
        match (&part_a.mapping, &part_b.mapping) {
            (
                PartMapping::Imm {
                    mapping: mapping_a, ..
                },
                PartMapping::Imm {
                    mapping: mapping_b, ..
                },
            ) => {
                let mapping_ok = match (mapping_a, mapping_b) {
                    (None, None) => true,
                    (None, Some(_)) | (Some(_), None) => false,
                    (Some(a), Some(b)) => match (a, b) {
                        (MappingOrBitOrder::Mapping(_), MappingOrBitOrder::BitOrder(_))
                        | (MappingOrBitOrder::BitOrder(_), MappingOrBitOrder::Mapping(_)) => false,
                        (MappingOrBitOrder::BitOrder(a), MappingOrBitOrder::BitOrder(b)) => a == b,
                        // We don't need these to be equal, as these only restrict what values are valid
                        (MappingOrBitOrder::Mapping(_), MappingOrBitOrder::Mapping(_)) => true,
                    },
                };

                if !mapping_ok {
                    trace!("Immediate values don't have compatible mappings");
                    return false
                }
            },
            // We don't need to compare this, because encoding_addresses_equal will do it for us!
            (
                PartMapping::MemoryComputation {
                    ..
                },
                PartMapping::MemoryComputation {
                    ..
                },
            ) => (),
            (
                PartMapping::Register {
                    mapping: mapping_a, ..
                },
                PartMapping::Register {
                    mapping: mapping_b, ..
                },
            ) => {
                if mapping_a.len() != mapping_b.len() {
                    trace!("Different lengths of mappings");
                    return false
                }

                for (reg_a, reg_b) in mapping_a.iter().zip(mapping_b.iter()) {
                    if let (Some(reg_a), Some(reg_b)) = (reg_a, reg_b) {
                        if reg_a != reg_b {
                            trace!("Register mappings do not match");
                            return false
                        }
                    }
                }
            },
            (mapping_a, mapping_b) => {
                trace!("Unable to handle non-identical mapping: {mapping_a:?} vs {mapping_b:?}");
                return false
            },
        }
    }

    trace!("Parts equal");

    true
}

/// The result of `encodings_semantically_equal`.
/// Semantics are guaranteed to be equivalent if `equal && !timeout` holds.
#[derive(Clone, Debug, PartialEq)]
pub struct Equivalence {
    /// Set to true if no case was encountered where the Encodings' semantics are not equivalent.
    pub equal: bool,

    /// Set to true if in at least one case, the comparison timed out.
    pub timeout: bool,
}

/// Determines whether two encodings are semantically equivalent.
///
/// This function assumes both encodings describe the exact same instruction space.
pub fn encodings_semantically_equal<'ctx, A: Arch>(
    options: &EncodingComparisonOptions, a: &Encoding<A, SynthesizedComputation>, b: &Encoding<A, SynthesizedComputation>,
    solver: &mut impl SmtSolver<'ctx>,
) -> Equivalence {
    let a_filter = a.bitpattern_as_filter();
    let b_filter = b.bitpattern_as_filter();
    if !a_filter.overlaps(&b_filter) {
        trace!("Comparison with no overlapping instruction space always returns true: {a} vs {b}");

        return Equivalence {
            equal: true,
            timeout: false,
        }
    }

    let filter = a_filter.intersect(&b_filter);

    let mut result = Equivalence {
        equal: true,
        timeout: false,
    };

    match (a.restrict_to(&filter), b.restrict_to(&filter)) {
        (Ok(a), Ok(b)) => {
            trace!("Comparing {a} vs {b}");

            if let Some(mapping) = PartIndexMapping::of(&a, &b) {
                if !encoding_addresses_equal(&mapping, &options.addresses, &a, &b)
                    || !encoding_dataflow_parts_equal(&mapping, &a, &b)
                {
                    result.equal = false;
                    return result
                }

                let is_equal = match ComputationEquivalence::of(&mapping, options, &a, &b, solver) {
                    ComputationEquivalence::Equal => true,
                    ComputationEquivalence::EqualOrTimeout => {
                        result.timeout = true;
                        true
                    },
                    ComputationEquivalence::NotEqual => {
                        result.equal = false;
                        false
                    },
                };

                if !is_equal {
                    return result
                }
            } else {
                result.equal = false;
                return result
            }
        },
        (Err(RestrictError::NoOverlap), _) | (_, Err(RestrictError::NoOverlap)) => (),
    }

    result
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use crate::arch::fake::FakeArch;
    use crate::arch::fake::FakeReg::{R0, R1, R2, R3};
    use crate::compare::encodings_structurally_equal;
    use crate::encoding::bitpattern::{Bit, FlowValueLocation, Part, PartMapping};
    use crate::encoding::dataflows::{
        AccessKind, AddrTerm, AddressComputation, Dataflow, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses, Size,
    };
    use crate::encoding::Encoding;
    use crate::instr::Instruction;

    #[test]
    pub fn check_encodings_equal1() {
        let instr = Instruction::new(&[0x00]);
        let e1 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
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
                            inputs: Inputs::sorted(vec![
                                Dest::Reg(R1, Size::qword()).into(),
                                Dest::Reg(R2, Size::qword()).into(),
                            ]),
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
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                        locations: vec![FlowValueLocation::MemoryAddress {
                            memory_index: 1,
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
                            memory_index: 1,
                            input_index: 1,
                        }],
                    },
                },
            ],
            write_ordering: Vec::new(),
        };

        let e2 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
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
                            inputs: Inputs::sorted(vec![
                                Dest::Reg(R1, Size::qword()).into(),
                                Dest::Reg(R2, Size::qword()).into(),
                            ]),
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
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                        locations: vec![FlowValueLocation::MemoryAddress {
                            memory_index: 1,
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
                            memory_index: 1,
                            input_index: 0,
                        }],
                    },
                },
            ],
            write_ordering: Vec::new(),
        };

        println!("{e1}");
        println!("{e2}");

        assert!(encodings_structurally_equal(&Default::default(), &e1, &e2))
    }

    #[test]
    pub fn check_encodings_equal2() {
        let instr = Instruction::new(&[0x00]);
        let e1 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
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
                            inputs: Inputs::sorted(vec![
                                Dest::Reg(R1, Size::qword()).into(),
                                Dest::Reg(R2, Size::qword()).into(),
                            ]),
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
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                        locations: vec![FlowValueLocation::MemoryAddress {
                            memory_index: 1,
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
                            memory_index: 1,
                            input_index: 1,
                        }],
                    },
                },
            ],
            write_ordering: Vec::new(),
        };

        let e2 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
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
                            inputs: Inputs::sorted(vec![
                                Dest::Reg(R1, Size::qword()).into(),
                                Dest::Reg(R2, Size::qword()).into(),
                            ]),
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
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                        locations: vec![FlowValueLocation::MemoryAddress {
                            memory_index: 1,
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
            ],
            write_ordering: Vec::new(),
        };

        println!("{e1}");
        println!("{e2}");
        assert!(!encodings_structurally_equal(&Default::default(), &e1, &e2))
    }

    #[test]
    pub fn check_encodings_equal3() {
        let instr = Instruction::new(&[0x00]);
        let e1 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
                addresses: MemoryAccesses {
                    instr,
                    memory: vec![MemoryAccess {
                        kind: AccessKind::Executable,
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
                        size: 2..2,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    }],
                    use_trap_flag: false,
                },
                outputs: vec![
                    Dataflow {
                        target: Dest::Reg(R0, Size::new(0, 2)),
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(0, 2)).into()]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                    Dataflow {
                        target: Dest::Reg(R1, Size::qword()),
                        inputs: Inputs::sorted(vec![
                            Dest::Reg(R1, Size::new(0, 5)).into(),
                            Dest::Reg(R2, Size::new(0, 5)).into(),
                        ]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                ],
                found_dependent_bytes: false,
            },
            parts: vec![Part {
                size: 2,
                value: 0,
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::InputForOutput {
                        output_index: 1,
                        input_index: 1,
                    }],
                },
            }],
            write_ordering: Vec::new(),
        };

        let e2 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
                addresses: MemoryAccesses {
                    instr,
                    memory: vec![MemoryAccess {
                        kind: AccessKind::Executable,
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
                        size: 2..2,
                        calculation: AddressComputation::unscaled_sum(1),
                        alignment: 1,
                    }],
                    use_trap_flag: false,
                },
                outputs: vec![
                    Dataflow {
                        target: Dest::Reg(R1, Size::qword()),
                        inputs: Inputs::sorted(vec![
                            Dest::Reg(R0, Size::new(0, 5)).into(),
                            Dest::Reg(R1, Size::new(0, 5)).into(),
                        ]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                    Dataflow {
                        target: Dest::Reg(R0, Size::new(0, 2)),
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(0, 2)).into()]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                ],
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

        println!("{e1}");
        println!("{e2}");

        assert!(encodings_structurally_equal(&Default::default(), &e1, &e2))
    }

    #[test]
    pub fn check_encodings_equal4() {
        let instr = Instruction::new(&[0x00]);
        let e1 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
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
            parts: vec![Part {
                size: 2,
                value: 0,
                mapping: PartMapping::MemoryComputation {
                    mapping: vec![
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::all()[0],
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::all()[1],
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::all()[2],
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::all()[3],
                                AddrTerm::identity(),
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                    ],
                    memory_indexes: vec![0],
                },
            }],
            write_ordering: Vec::new(),
        };

        let e2 = Encoding {
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
            dataflows: Dataflows::<FakeArch, AddressComputation> {
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
            parts: vec![Part {
                size: 2,
                value: 0,
                mapping: PartMapping::MemoryComputation {
                    mapping: vec![
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::all()[0],
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::all()[1],
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::all()[2],
                                AddrTerm::identity(),
                                AddrTerm::default(),
                            ],
                        }),
                        Some(AddressComputation {
                            offset: 0,
                            terms: [
                                AddrTerm::identity(),
                                AddrTerm::all()[3],
                                AddrTerm::identity(),
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
        assert!(!encodings_structurally_equal(&Default::default(), &e1, &e2))
    }
}
