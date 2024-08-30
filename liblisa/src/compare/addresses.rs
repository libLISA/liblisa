use std::collections::HashMap;
use std::fmt::Debug;

use log::trace;

use crate::arch::{Arch, Register};
use crate::compare::PartIndexMapping;
use crate::encoding::bitpattern::Bit;
use crate::encoding::dataflows::{AddrTermSize, AddressComputation, Dest, Inputs, MemoryAccesses, Source};
use crate::encoding::Encoding;

/// Options for comparing [`MemoryAccesses`].
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct AddressComparisonOptions {
    /// Whether differences in alignment should be ignored.
    pub allow_alignment_differences: bool,

    /// Whether differences in side should be ignored
    pub allow_size_differences: bool,
}

impl AddressComparisonOptions {
    /// Creates new ComparisonOptions with all fields set to `false`.
    pub const fn new() -> Self {
        AddressComparisonOptions {
            allow_size_differences: false,
            allow_alignment_differences: false,
        }
    }
}

/// An input for a memory address calculation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum FilledMemInput<'a, A: Arch> {
    /// A concrete input. Normally this is a register.
    ///
    /// If you have manually constructed the MemoryAccess it can be any valid [`Source`].
    Concrete(&'a Source<A>),

    /// An immediate value from a part.
    Part(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExtractedAddrTerms<'a, A: Arch> {
    offset: u64,
    terms: HashMap<(FilledMemInput<'a, A>, AddrTermSize, u8), usize>,
}

fn extract_addr_terms<'a, A: Arch>(
    inputs: &'a Inputs<A>, calculation: &AddressComputation, map_part_index: impl Fn(usize) -> usize,
) -> ExtractedAddrTerms<'a, A> {
    let mut offset = calculation.offset as u64;
    let mut terms = HashMap::new();
    for (input_index, input) in inputs.iter().enumerate() {
        let term = calculation.terms[input_index];
        let key = if let Source::Imm(part_index) = input {
            FilledMemInput::Part(map_part_index(*part_index))
        } else {
            FilledMemInput::Concrete(input)
        };

        match input {
            Source::Dest(Dest::Reg(reg, _)) if reg.is_zero() => (),
            Source::Dest(_) | Source::Imm(_) => {
                for term in [Some(term.primary), term.second_use].into_iter().flatten() {
                    if term.shift.mult() != 0 {
                        *terms.entry((key, term.size, term.shift.right())).or_insert(0) += term.shift.mult() as usize;
                    }
                }
            },
            Source::Const {
                value, ..
            } => offset = offset.wrapping_add(term.apply(*value)),
        }
    }

    ExtractedAddrTerms {
        offset,
        terms,
    }
}

fn addresses_equal<A: Arch>(
    mapping: &PartIndexMapping, options: &AddressComparisonOptions, addresses_a: &MemoryAccesses<A>,
    addresses_b: &MemoryAccesses<A>,
) -> bool {
    if addresses_a.len() != addresses_b.len() {
        return false
    }

    let addresses_match = addresses_a.iter().zip(addresses_b.iter()).all(|(a, b)| {
        (options.allow_alignment_differences || a.alignment == b.alignment)
            && (options.allow_size_differences || a.size == b.size)
            && a.kind == b.kind
            && {
                let a_terms = extract_addr_terms(a.inputs(), &a.calculation, |a_index| a_index);
                let b_terms = extract_addr_terms(b.inputs(), &b.calculation, |b_index| mapping.b_imm_to_a(b_index));

                trace!("a_terms={a_terms:?}, b_terms={b_terms:?}");

                a_terms == b_terms
            }
    });

    addresses_match
}

/// Compares the [`MemoryAcesses`](crate::encoding::dataflows::MemoryAccesses) of the two encodings, and returns whether they are equal.
pub fn encoding_addresses_equal<A: Arch, C: Clone + Debug>(
    mapping: &PartIndexMapping, options: &AddressComparisonOptions, a: &Encoding<A, C>, b: &Encoding<A, C>,
) -> bool {
    let bits_involved_with_addresses = a
        .bits
        .iter()
        .zip(b.bits.iter())
        .enumerate()
        .filter(|(_, (&bit_a, &bit_b))| {
            a.is_bit_involved_with_address_reg_or_computation(bit_a) || b.is_bit_involved_with_address_reg_or_computation(bit_b)
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();

    assert!(bits_involved_with_addresses.len() <= 20);

    let base_instr = {
        let mut instr = *a.instr();

        for (index, (&a, &b)) in a.bits.iter().zip(b.bits.iter()).enumerate() {
            match (a, b) {
                (Bit::Fixed(bit), _) => instr.set_nth_bit_from_right(index, bit),
                (_, Bit::Fixed(bit)) => instr.set_nth_bit_from_right(index, bit),
                _ => (),
            }
        }

        instr
    };

    let a_filter = a.bitpattern_as_filter();
    let b_filter = b.bitpattern_as_filter();

    for k in 0..(1u64 << bits_involved_with_addresses.len()) {
        let instr = {
            let mut instr = base_instr;
            for (index, &bit_index) in bits_involved_with_addresses.iter().enumerate() {
                instr.set_nth_bit_from_right(bit_index, (k >> index) as u8 & 1);
            }

            instr
        };

        if a_filter.matches(&instr) && b_filter.matches(&instr) {
            let parts_a = a.extract_parts(&instr);
            let parts_b = b.extract_parts(&instr);

            let dataflows_a = a.instantiate(&parts_a);
            let dataflows_b = b.instantiate(&parts_b);

            if let (Ok(dataflows_a), Ok(dataflows_b)) = (dataflows_a, dataflows_b) {
                if !addresses_equal(mapping, options, &dataflows_a.addresses, &dataflows_b.addresses) {
                    trace!(
                        "Addresses not equal in {instr:?}: {:#?} vs {:#?}",
                        dataflows_a.addresses, dataflows_b.addresses
                    );
                    return false
                }
            }
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use test_log::test;
    use FakeReg::*;

    use crate::arch::fake::{FakeArch, FakeReg};
    use crate::compare::addresses::{addresses_equal, encoding_addresses_equal};
    use crate::compare::mapping::Mapping;
    use crate::compare::PartIndexMapping;
    use crate::encoding::bitpattern::{Bit, FlowValueLocation, Part, PartMapping};
    use crate::encoding::dataflows::{
        AccessKind, AddrTerm, AddrTermSize, AddressComputation, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses, Size,
        Source,
    };
    use crate::encoding::Encoding;
    use crate::instr::Instruction;
    use crate::semantics::default::computation::SynthesizedComputation;
    use crate::semantics::{Computation, ARG_NAMES};

    fn assert_accesses_equal<const EQUAL: bool>(
        custom_mapping: Option<&PartIndexMapping>, lhs_inputs: Inputs<FakeArch>, lhs: AddressComputation,
        rhs_inputs: Inputs<FakeArch>, rhs: AddressComputation,
    ) {
        assert!(
            EQUAL
                == addresses_equal(
                    custom_mapping.unwrap_or(&PartIndexMapping::default()),
                    &Default::default(),
                    &MemoryAccesses::<FakeArch> {
                        instr: Instruction::new(&[0]),
                        use_trap_flag: false,
                        memory: vec![MemoryAccess {
                            kind: AccessKind::InputOutput,
                            inputs: lhs_inputs.clone(),
                            size: 4..4,
                            calculation: lhs,
                            alignment: 1,
                        }]
                    },
                    &MemoryAccesses {
                        instr: Instruction::new(&[0]),
                        use_trap_flag: false,
                        memory: vec![MemoryAccess {
                            kind: AccessKind::InputOutput,
                            inputs: rhs_inputs.clone(),
                            size: 4..4,
                            calculation: rhs,
                            alignment: 1,
                        }]
                    }
                ),
            "Expected comparison to return {EQUAL}: {} with inputs {lhs_inputs:?} == {} with inputs {rhs_inputs:?}",
            lhs.display(ARG_NAMES),
            rhs.display(ARG_NAMES)
        );
    }

    #[test]
    pub fn test_ordering_differences() {
        assert_accesses_equal::<true>(
            None,
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
        );
    }

    #[test]
    pub fn test_mapping_differences() {
        assert_accesses_equal::<true>(
            Some(&PartIndexMapping {
                imms: Mapping::of(
                    [Bit::Part(0), Bit::Part(1)].into_iter().map(|x| (x, true)),
                    [Bit::Part(1), Bit::Part(0)].into_iter().map(|x| (x, true)),
                )
                .unwrap(),
                dataflow_regs: Mapping::default(),
            }),
            Inputs::unsorted(vec![Source::Imm(1), Source::Imm(0)]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![Source::Imm(0), Source::Imm(1)]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
        );

        assert_accesses_equal::<false>(
            Some(&PartIndexMapping {
                imms: Mapping::of(
                    [Bit::Part(0), Bit::Part(1)].into_iter().map(|x| (x, true)),
                    [Bit::Part(0), Bit::Part(1)].into_iter().map(|x| (x, true)),
                )
                .unwrap(),
                dataflow_regs: Mapping::default(),
            }),
            Inputs::unsorted(vec![Source::Imm(0), Source::Imm(1)]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![Source::Imm(0), Source::Imm(1)]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
        );
    }

    #[test]
    pub fn test_riz_resolution() {
        assert_accesses_equal::<true>(
            None,
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::RZ, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::default(),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
        );
    }

    #[test]
    pub fn test_multiplication_differences() {
        assert_accesses_equal::<true>(
            None,
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 3),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 4),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
        );

        assert_accesses_equal::<true>(
            None,
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 2),
                    AddrTerm::single(AddrTermSize::U64, 0, 3),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 5),
                    AddrTerm::default(),
                    AddrTerm::default(),
                    AddrTerm::default(),
                ],
            },
        );

        assert_accesses_equal::<true>(
            None,
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::single(AddrTermSize::U64, 0, 4),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                ],
            },
            Inputs::unsorted(vec![
                Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())),
            ]),
            AddressComputation {
                offset: 0,
                terms: [
                    AddrTerm::single(AddrTermSize::U64, 0, 4),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::single(AddrTermSize::U64, 0, 1),
                    AddrTerm::default(),
                ],
            },
        );
    }

    #[test]
    pub fn test_encoding_addresses_equal_partially_overlapping() {
        let instr = Instruction::new(&[0x00]);
        let e1 = Encoding::<FakeArch, SynthesizedComputation> {
            bits: vec![
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(0),
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
                    memory: vec![MemoryAccess {
                        kind: AccessKind::InputOutput,
                        inputs: Inputs::sorted(vec![Dest::Reg(R1, Size::qword()).into()]),
                        size: 8..8,
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
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 0,
                    }],
                },
            }],
            write_ordering: Vec::new(),
        };

        let e2 = Encoding::<FakeArch, SynthesizedComputation> {
            bits: vec![
                Bit::Fixed(0),
                Bit::Part(0),
                Bit::Part(0),
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
                    memory: vec![MemoryAccess {
                        kind: AccessKind::InputOutput,
                        inputs: Inputs::sorted(vec![Dest::Reg(R1, Size::qword()).into()]),
                        size: 8..8,
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
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R2), Some(R4), Some(R6)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 0,
                    }],
                },
            }],
            write_ordering: Vec::new(),
        };

        println!("{e1}");
        println!("{e2}");

        let mapping = PartIndexMapping::of(&e1, &e2).unwrap();
        assert!(encoding_addresses_equal(&mapping, &Default::default(), &e1, &e2));

        let mapping = PartIndexMapping::of(&e2, &e1).unwrap();
        assert!(encoding_addresses_equal(&mapping, &Default::default(), &e2, &e1));
    }
}
