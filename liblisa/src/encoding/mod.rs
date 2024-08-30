//! The main component of libLISA's semantics is an [`Encoding`].
//! An encoding represents a group of instructions with similar semantics.
//!
//! An encoding consists of two components: [a bitpattern](bitpattern) (for grouping instructions) and [Dataflows](dataflows).

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::iter::{repeat, repeat_with};

use arrayvec::ArrayVec;
use bitpattern::*;
use dataflows::*;
use itertools::Itertools;
use log::*;
use rand::seq::IteratorRandom;
use rand::Rng;
use serde::{Deserialize, Serialize};

use crate::arch::{Arch, Register};
use crate::instr::{ByteFilter, FilterBit, Instruction, InstructionFilter};
use crate::semantics::{Computation, ARG_NAMES};
use crate::utils::bitmap::{BitmapSlice, GrowingBitmap};
use crate::utils::min_cover_with_exclusions::MinCoverWithExclusions;
use crate::utils::{bitmask_u64, EitherIter};

pub mod bitpattern;
pub mod dataflows;

mod display;
pub mod indexed;
pub mod mcs;
mod merge;

pub use merge::{merge_encodings_semantically, merge_encodings_structurally};

/// An [`Encoding`] with pre-computed filters.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct EncodingWithFilters<A: Arch, C> {
    /// The encoding.
    pub encoding: Encoding<A, C>,

    /// The precomputed value of `encoding.filters()`.
    pub filters: Vec<InstructionFilter>,
}

impl<A: Arch, C: PartialEq> PartialEq for EncodingWithFilters<A, C> {
    fn eq(&self, other: &Self) -> bool {
        self.encoding == other.encoding
    }
}

impl<A: Arch, C> EncodingWithFilters<A, C> {
    /// Pre-computes the filters for `encoding`, and returns an [`EncodingWithFilters`].
    pub fn new(encoding: Encoding<A, C>) -> Self {
        Self {
            filters: encoding.filters(),
            encoding,
        }
    }
}

/// [`Dataflows`] and semantics for a group of similar instructions.
/// An encoding matches at least one instruction.
/// If an encoding matches an instruction, it can be *instantiated* for that instruction.
///
/// Instantiation computes the [`Dataflows`] for a specific instruction.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema, C: schemars::JsonSchema")
)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct Encoding<A: Arch, C> {
    /// The bitpattern
    pub bits: Vec<Bit>,

    /// `errors[N]` is true if the analysis for `bits[N]` produced an error, and the correct [`Bit`] was inferred from context.
    pub errors: Vec<bool>,

    /// A part mapping that maps the value of parts to registers/memory computations or immediate values that can be filled in the `dataflows`.
    pub parts: Vec<Part<A>>,

    /// The dataflows of the encoding.
    pub dataflows: Dataflows<A, C>,

    #[serde(default)]
    /// Describes the ordering in which outputs must be written in case overlapping outputs are possible.
    /// If there are multiple applicable orderings, they should all be applied.
    /// If multiple orderings apply, they may not conflict.
    pub write_ordering: Vec<WriteOrdering>,
}

/// Describes the order in which outputs should be written, if the part_values match.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct WriteOrdering {
    /// The ordering is applicable when the part values for an instruction match these part values.
    /// A value of `None` means that any part value matches.
    pub part_values: Vec<Option<u64>>,

    /// The order that needs to be applied if the part values match.
    pub output_index_order: Vec<usize>,
}

impl<A: Arch, C> Encoding<A, C> {
    /// Returns the instruction corresponding to the provided part values, **without checking whether the provided part values are valid.**
    ///
    /// If the provided part values are invalid, a garbage instruction is returned.
    pub fn unchecked_instr(&self, part_values: &[u64]) -> Instruction {
        let part_values = part_values.iter().map(|&v| Some(v)).collect::<ArrayVec<_, MAX_PARTS>>();
        self.part_values_to_instr(&part_values)
    }

    /// Converts the bitpattern to a single filter.
    /// Does not account for invalid part values.
    ///
    /// If you want filters that match the covered instructions exactly, use [`Encoding::filters`] instead.
    pub fn bitpattern_as_filter(&self) -> InstructionFilter {
        let mut f = InstructionFilter::new(repeat(ByteFilter::new(0, 0)).take(self.instr().byte_len()));
        for (index, bit) in self.bits.iter().enumerate() {
            match bit {
                Bit::Fixed(0) => f.set_nth_bit_from_right(index, FilterBit::Is0),
                Bit::Fixed(1) => f.set_nth_bit_from_right(index, FilterBit::Is1),
                Bit::DontCare | Bit::Part(_) => (),
                Bit::Fixed(_) => unreachable!(),
            }
        }

        f
    }

    /// Returns true if the first `num_bits_to_check` of `instr` match the encoding.
    pub fn prefix_matches(&self, instr: &Instruction, num_bits_to_check: usize) -> bool {
        let mut k = self.parts.iter().map(|part| part.size).collect::<Vec<_>>();
        let mut part_values = vec![0u64; self.parts.len()];
        for (index, &bit) in self.bits.iter().rev().enumerate().take(num_bits_to_check) {
            let instr_bit = instr.nth_bit_from_left(index);
            match (bit, instr_bit) {
                (Bit::Fixed(fixed_bit), instr_bit) => {
                    if fixed_bit != instr_bit {
                        return false
                    }
                },
                (Bit::DontCare, _) => (),
                (Bit::Part(part_index), instr_bit) => {
                    let v = &mut part_values[part_index];
                    k[part_index] -= 1;
                    *v |= (instr_bit as u64) << k[part_index];
                },
            }
        }

        self.parts
            .iter()
            .zip(part_values.iter().zip(k.iter().map(|&k| !bitmask_u64(k as u32))))
            .all(|(part, (&val, mask))| match &part.mapping {
                PartMapping::Imm {
                    mapping, ..
                } => mapping
                    .as_ref()
                    .map(|mapping| match mapping {
                        MappingOrBitOrder::Mapping(mapping) => mapping
                            .iter()
                            .enumerate()
                            .filter(|(_, val)| val.is_invalid())
                            .any(|(index, _)| index as u64 & mask == val),
                        MappingOrBitOrder::BitOrder(_) => true,
                    })
                    .unwrap_or(true),
                PartMapping::MemoryComputation {
                    mapping, ..
                } => mapping
                    .iter()
                    .enumerate()
                    .filter(|(_, val)| val.is_some())
                    .any(|(index, _)| index as u64 & mask == val),
                PartMapping::Register {
                    mapping, ..
                } => mapping
                    .iter()
                    .enumerate()
                    .filter(|(_, val)| val.is_some())
                    .any(|(index, _)| index as u64 & mask == val),
            })
    }

    /// Computes the [`Instruction`] that corresponds to the part values provided.
    /// When a part value is `None`, the current part value of the Encoding is picked.
    /// You must ensure that the part values are valid for this encoding.
    /// Passing invalid part values produces an [`Instruction`] that is not covered by the encoding.
    pub fn part_values_to_instr(&self, part_values: &[Option<u64>]) -> Instruction {
        let mut new_instr: Instruction = *self.instr();
        let mut shift_values = part_values.iter().copied().collect::<ArrayVec<_, MAX_PARTS>>();
        let mut index = 0;
        while index < self.bits.len() {
            let kind = self.bits[index];

            if let Bit::Part(n) = kind {
                if let Some(part_value) = &mut shift_values[n] {
                    if index % 8 == 0 {
                        let num_matching = &self.bits[index + 1..].iter().take_while(|&&k| k == kind).count() + 1;

                        if num_matching >= 8 {
                            let num_matching = num_matching / 8 * 8;

                            new_instr.set_multiple_bits_from_right(index, *part_value, num_matching);
                            index += num_matching;

                            match num_matching.cmp(&64) {
                                Ordering::Less => *part_value >>= num_matching,
                                Ordering::Equal => *part_value = 0,
                                Ordering::Greater => panic!("A part {n} is larger than 64 bits"),
                            }

                            continue
                        }
                    }

                    new_instr.set_nth_bit_from_right(index, *part_value as u8 & 1);
                    *part_value >>= 1;
                }
            }

            index += 1;
        }

        if shift_values.iter().flatten().any(|&v| v != 0) {
            panic!("Part values out of range: {part_values:X?}");
        }

        new_instr
    }

    /// Computes the [`Instruction`] that corresponds to the part values provided.
    /// You must ensure that the part values are valid for this encoding.
    /// Passing invalid part values produces an [`Instruction`] that is not covered by the encoding.
    pub fn all_part_values_to_instr(&self, part_values: &[u64]) -> Instruction {
        let mut new_instr: Instruction = *self.instr();
        let mut shift_values = part_values.iter().copied().collect::<ArrayVec<_, MAX_PARTS>>();
        let mut index = 0;
        while index < self.bits.len() {
            let kind = self.bits[index];

            if let Bit::Part(n) = kind {
                let part_value = &mut shift_values[n];
                if index % 8 == 0 {
                    let num_matching = &self.bits[index + 1..].iter().take_while(|&&k| k == kind).count() + 1;

                    if num_matching >= 8 {
                        let num_matching = num_matching / 8 * 8;

                        new_instr.set_multiple_bits_from_right(index, *part_value, num_matching);
                        index += num_matching;

                        match num_matching.cmp(&64) {
                            Ordering::Less => *part_value >>= num_matching,
                            Ordering::Equal => *part_value = 0,
                            Ordering::Greater => panic!("A part {n} is larger than 64 bits"),
                        }

                        continue
                    }
                }

                new_instr.set_nth_bit_from_right(index, *part_value as u8 & 1);
                *part_value >>= 1;
            }

            index += 1;
        }

        if shift_values.iter().any(|&v| v != 0) {
            panic!("Part values out of range: {part_values:X?}");
        }

        new_instr
    }

    /// Returns the bit indices of the part.
    /// In other words, returns all indices for which `self.bits[N] == Bit::Part(part_index)`.
    pub fn part_bit_indices(&self, part_index: usize) -> impl Iterator<Item = usize> + '_ {
        self.bits
            .iter()
            .enumerate()
            .filter(move |&(_, &bit)| bit == Bit::Part(part_index))
            .map(|(index, _)| index)
    }

    fn find_overlapping_for(&self, target: &Dest<A>) -> HashSet<usize> {
        self.dataflows
            .outputs
            .iter()
            .enumerate()
            .filter(|&(output_index, output)| {
                if output.target.overlaps(target) {
                    true
                } else if output.target.size().overlaps(&target.size()) {
                    if let Some(mapping) = self
                        .parts
                        .iter()
                        .flat_map(|p| match &p.mapping {
                            PartMapping::Register {
                                mapping,
                                locations,
                            } if locations.contains(&FlowValueLocation::Output(output_index)) => Some(mapping),
                            _ => None,
                        })
                        .next()
                    {
                        let reg = match target {
                            Dest::Reg(reg, _) => reg,
                            Dest::Mem(..) => return false,
                        };
                        mapping.contains(&Some(*reg))
                    } else {
                        false
                    }
                } else {
                    false
                }
            })
            .map(|(index, _)| index)
            .collect()
    }

    /// Iterates over all of output indices, and a [`HashSet`] of overlapping output indices.
    /// An output index is only yielded if it is overlapping with at least one other output index.
    /// Outputs overlap if their destinations overlap. See [`Dest::overlaps`].
    pub fn overlapping_outputs(&self) -> impl Iterator<Item = (usize, HashSet<usize>)> + '_ {
        self.dataflows
            .outputs
            .iter()
            .enumerate()
            .map(|(output_index, output)| {
                let overlapping = if let Some((_, mapping)) = self
                    .parts
                    .iter()
                    .enumerate()
                    .flat_map(|(index, p)| match &p.mapping {
                        PartMapping::Register {
                            mapping,
                            locations,
                        } if locations.contains(&FlowValueLocation::Output(output_index)) => Some((index, mapping)),
                        _ => None,
                    })
                    .next()
                {
                    let mut v = HashSet::new();

                    for reg in mapping.iter().flatten() {
                        v.extend(self.find_overlapping_for(&Dest::Reg(*reg, output.target.size())));
                    }

                    v
                } else {
                    let v = self.find_overlapping_for(output.target());
                    v
                };

                (output_index, overlapping)
            })
            .filter(|(_, overlapping)| overlapping.len() > 1)
    }

    /// Returns the current [`Instruction`] of the encoding.
    /// While encodings cover a group of instructions, the dataflows and memory accesses are always instantiated for a specific instruction.
    /// The [`Encoding::canonicalize`] function changes the current instruction to the instruction where all part have the lowest valid value.
    /// This means that the [`Instruction`] of an encoding typically has mostly 0s for the bits that are parts or DontCare bits.
    pub fn instr(&self) -> &Instruction {
        &self.dataflows.addresses.instr
    }

    /// Determines if there is any instruction that is covered by this encoding.
    pub fn covers_some_instr(&self) -> bool {
        for part in self.parts.iter() {
            match &part.mapping {
                PartMapping::Register {
                    locations: _,
                    mapping,
                } if mapping.iter().all(Option::is_none) => return false,
                PartMapping::Imm {
                    locations: _,
                    mapping: Some(MappingOrBitOrder::Mapping(mapping)),
                    ..
                } if mapping.iter().all(PartValue::is_invalid) => return false,
                _ => (),
            }
        }

        true
    }

    /// Returns a [`Vec`] of filters that describe exactly which instructions are covered by this encoding.
    /// The filters may overlap.
    pub fn filters(&self) -> Vec<InstructionFilter> {
        let incomplete_choices = self
            .parts
            .iter()
            .enumerate()
            .flat_map(|(index, p)| match &p.mapping {
                PartMapping::Register {
                    locations: _,
                    mapping,
                } if mapping.iter().any(Option::is_none) => {
                    Some((index, mapping.iter().map(Option::is_some).collect::<Vec<_>>()))
                },
                PartMapping::Imm {
                    locations: _,
                    mapping: Some(MappingOrBitOrder::Mapping(mapping)),
                    ..
                } if mapping.iter().any(PartValue::is_invalid) => {
                    Some((index, mapping.iter().map(PartValue::is_valid).collect::<Vec<_>>()))
                },
                PartMapping::MemoryComputation {
                    mapping, ..
                } if mapping.iter().any(Option::is_none) => {
                    Some((index, mapping.iter().map(Option::is_some).collect::<Vec<_>>()))
                },
                _ => None,
            })
            .collect::<Vec<_>>();

        let incomplete_choice_filters = incomplete_choices
            .into_iter()
            .map(|(index, valid)| {
                let excluded = valid
                    .iter()
                    .enumerate()
                    .filter(|(_, valid)| !*valid)
                    .map(|(index, _)| index as u64)
                    .collect::<Vec<_>>();

                let minimal_filters = MinCoverWithExclusions::new(&excluded, self.parts[index].size);
                let bit_filters = minimal_filters.into_bit_filters();

                (index, bit_filters)
            })
            .collect::<Vec<_>>();

        let incomplete_choices_map = {
            let mut m = HashMap::new();
            for (index, (n, _)) in incomplete_choice_filters.iter().enumerate() {
                m.insert(*n, index);
            }

            m
        };

        let mut filters = Vec::new();
        let mut values = vec![0usize; incomplete_choice_filters.len()];
        loop {
            let mut ks: Vec<i32> = vec![0; incomplete_choice_filters.len()];
            let mut byte_filters = Vec::with_capacity(self.bits.len() / 8);
            for byte in self.bits.chunks(8) {
                let mvs = byte
                    .iter()
                    .map(|b| match b {
                        Bit::Fixed(v) => (1, *v),
                        Bit::Part(n) => {
                            if let Some(&index) = incomplete_choices_map.get(n) {
                                let bit_filter = &incomplete_choice_filters[index].1[values[index]];

                                let shift = ks[index];
                                let value = (bit_filter.value >> shift) & 1;
                                let fixed = bit_filter.bit_is_fixed.get(shift as usize) as u8;
                                ks[index] += 1;

                                (fixed, value as u8)
                            } else {
                                (0, 0)
                            }
                        },
                        Bit::DontCare => (0, 0),
                    })
                    .collect::<Vec<_>>();
                let mask = mvs.iter().enumerate().map(|(i, (m, _))| m << i).fold(0, |a, b| a | b);
                let value = mvs.iter().enumerate().map(|(i, (_, v))| v << i).fold(0, |a, b| a | b);

                byte_filters.push(ByteFilter::new(mask, value));
            }

            // Reverse the filters because they are in the wrong order because self.bits is stored the other way round
            byte_filters.reverse();
            filters.push(InstructionFilter::new(byte_filters));

            let mut carry = 1;
            for (index, val) in values.iter_mut().enumerate() {
                *val += carry;
                if *val >= incomplete_choice_filters[index].1.len() {
                    *val = 0;
                    carry = 1;
                } else {
                    carry = 0;
                    break
                }
            }

            if carry > 0 {
                break;
            }
        }

        filters
    }

    fn value_bits(&self, n: usize) -> usize {
        let mut result = 0;
        for bit in self.bits.iter() {
            if let Bit::Part(v) = bit {
                if n == *v {
                    result += 1;
                }
            }
        }

        result
    }

    /// Returns true if all dataflow outputs have a computation.
    pub fn all_outputs_have_computations(&self) -> bool {
        self.dataflows.output_dataflows().all(|o| o.computation.is_some())
    }

    /// Remaps the computations to a new value.
    pub fn map_computations<CNew>(&self, f: impl Fn(&Inputs<A>, &C) -> Option<CNew>) -> Encoding<A, CNew> {
        Encoding {
            bits: self.bits.clone(),
            errors: self.errors.clone(),
            parts: self.parts.clone(),
            dataflows: self.dataflows.map_computations(f),
            write_ordering: self.write_ordering.clone(),
        }
    }

    /// Replaces the computation for the output in position `index` with `computation`.
    pub fn set_computation(&mut self, index: usize, computation: C) {
        self.dataflows[index].computation = Some(computation);
    }

    fn fill_value_imms(&self, choices: &mut [u64], values: HashSet<usize>) {
        let mut base = vec![0; choices.len()];
        for index in values.iter() {
            choices[*index] = 0;
        }

        for (index, kind) in self.bits.iter().enumerate() {
            match kind {
                Bit::Part(n) if values.contains(n) => {
                    // If there are less than 6 bits, we're just going to set the lowest 2 bits instead of doing a checkerboard pattern.
                    if self.bits.iter().filter(|b| b == &kind).count() >= 6 {
                        choices[*n] |= ((1 ^ (index & 1)) as u64) << base[*n];
                    } else if base[*n] <= 1 {
                        choices[*n] |= 1 << base[*n];
                    }

                    base[*n] += 1;
                },
                _ => {},
            }
        }
    }

    fn fill_addr_imms(&self, choices: &mut [u64], values: HashSet<usize>) {
        for index in values.iter() {
            let count = self.bits.iter().filter(|b| b == &&Bit::Part(*index)).count();
            choices[*index] = match count.cmp(&3) {
                Ordering::Less => 0,
                Ordering::Equal => 0b010,
                Ordering::Greater => 0b11 << (count / 2),
            };
        }
    }

    /// Determines the part values that give the "best" register assignments for analysis.
    ///
    /// The "best" assignment in this case, is an assignment where as many different registers as possible are used.
    /// This allows encoding analysis and synthesis to produce better results.
    pub fn find_best_reg_choices(&self, _alter_sizes: bool, eval: impl Fn(&[u64]) -> usize) -> Option<Vec<Option<u64>>> {
        let reg_choices = self
            .parts
            .iter()
            .map(|p| match &p.mapping {
                PartMapping::Register {
                    mapping, ..
                } => Some(mapping.len()),
                _ => None,
            })
            .collect::<Vec<_>>();

        let current_choices = self.parts.iter().map(|p| p.value).collect::<Vec<_>>();
        if reg_choices.iter().filter(|x| x.is_some()).count() == 0 {
            return None;
        }

        let mut perfect_score = eval(&current_choices);
        let mut perfect_choices = current_choices;
        let mut new_choices = vec![0; reg_choices.len()];
        loop {
            let score = eval(&new_choices);
            if score < perfect_score {
                debug!("Choosing {new_choices:X?} over {perfect_choices:?} because {score} < {perfect_score}");
                perfect_score = score;
                perfect_choices.clone_from(&new_choices);
            }

            let mut carry = 1;
            for (val, choice) in new_choices.iter_mut().zip(reg_choices.iter()) {
                if let Some(choices_len) = choice {
                    *val += carry;
                    if *val >= *choices_len as u64 {
                        *val = 0;
                        carry = 1;
                    } else {
                        carry = 0;
                    }
                }
            }

            if carry > 0 {
                break;
            }
        }

        Some(
            perfect_choices
                .iter()
                .copied()
                .zip(reg_choices.iter())
                .map(|(c, r)| r.map(|_| c))
                .collect::<Vec<_>>(),
        )
    }

    /// Returns the part values for the provided `instr`.
    /// You must make sure that `instr` is covered by this encoding.
    /// In many cases, this function will panic if it is invoked with an instruction not covered by this encoding.
    /// It will not panic if all fixed bits match, but one of the part values is not a valid value according to the part mapping.
    pub fn extract_parts(&self, instr: &Instruction) -> Vec<u64> {
        assert_eq!(instr.bit_len(), self.bits.len(), "Instr: {instr:X?}, bits: {:?}", self.bits);

        let mut parts = vec![0u64; self.parts.len()];
        let mut part_indices = vec![0usize; self.parts.len()];
        for (bit_index, bit) in self.bits.iter().enumerate() {
            match bit {
                Bit::Part(n) => {
                    parts[*n] |= (instr.nth_bit_from_right(bit_index) as u64) << part_indices[*n];
                    part_indices[*n] += 1;
                },
                Bit::Fixed(v) => {
                    assert_eq!(
                        instr.nth_bit_from_right(bit_index),
                        *v,
                        "The instruction does not match the encoding; You cannot instantiate it: {instr:X} = {instr:?} vs {:?}; Bit {bit_index} is different",
                        self.bits
                    );
                },
                _ => (),
            }
        }

        parts
    }

    /// Verifies whether the encoding is internally consistent.
    pub fn integrity_check(&self) -> Result<(), IntegrityError> {
        if let Some(index) = self.dataflows.output_dataflows().position(|flow| {
            flow.inputs.iter().any(|s| match s {
                Source::Imm(n) => self.parts.get(*n).is_none(),
                _ => false,
            })
        }) {
            return Err(IntegrityError::UnknownPartInOutputImm {
                output_index: index,
            });
        }

        if let Some(index) = self.dataflows.addresses.iter().position(|access| {
            access.inputs.iter().any(|s| match s {
                Source::Imm(n) => self.parts.get(*n).is_none(),
                _ => false,
            })
        }) {
            return Err(IntegrityError::UnknownPartInAddrImm {
                memory_index: index,
            });
        }

        for (part_index, part) in self.parts.iter().enumerate() {
            if part.size != self.bits.iter().filter(|&&bit| bit == Bit::Part(part_index)).count() {
                return Err(IntegrityError::PartSizeDoesNotMatchBits {
                    part_index,
                })
            }

            match &part.mapping {
                PartMapping::Imm {
                    mapping, ..
                } => match mapping {
                    Some(MappingOrBitOrder::Mapping(mapping)) => {
                        if mapping.iter().all(|x| x.is_invalid()) {
                            return Err(IntegrityError::PartHasNoValidMapping {
                                part_index,
                            })
                        }
                    },
                    Some(MappingOrBitOrder::BitOrder(bit_order)) => {
                        if bit_order.len() != part.size {
                            return Err(IntegrityError::MappingDoesNotMatchPartSize {
                                part_index,
                                mapping_entries: bit_order.len(),
                                part_bits: part.size,
                            })
                        }
                    },
                    None => (),
                },
                PartMapping::MemoryComputation {
                    mapping, ..
                } => {
                    if mapping.len() != 1 << part.size {
                        return Err(IntegrityError::MappingDoesNotMatchPartSize {
                            part_index,
                            mapping_entries: mapping.len(),
                            part_bits: part.size,
                        })
                    }

                    if mapping.iter().all(|item| item.is_none()) {
                        return Err(IntegrityError::PartHasNoValidMapping {
                            part_index,
                        })
                    }
                },
                PartMapping::Register {
                    mapping, ..
                } => {
                    if mapping.len() != 1 << part.size {
                        return Err(IntegrityError::MappingDoesNotMatchPartSize {
                            part_index,
                            mapping_entries: mapping.len(),
                            part_bits: part.size,
                        })
                    }

                    if mapping.iter().all(|item| item.is_none()) {
                        return Err(IntegrityError::PartHasNoValidMapping {
                            part_index,
                        })
                    }
                },
            }
        }

        Ok(())
    }

    /// Splits all flag outputs in the dataflows into a separate output for each destination register byte.
    pub fn split_flag_output(&mut self) {
        loop {
            let removed_index = if let Some(removed_index) = self.dataflows.output_dataflows().position(|f| {
                if let Dest::Reg(r, s) = f.target {
                    r.is_flags() && s.num_bytes() > 1
                } else {
                    false
                }
            }) {
                removed_index
            } else {
                break
            };

            // Add all ValueImms as potential inputs for the flags.
            // We're not always able to figure out the flags, so we'll err on the side of safety until synthesis.
            // Having a few too many inputs never hurts.
            for (part_index, part) in self.parts.iter_mut().enumerate() {
                if let PartMapping::Imm {
                    locations, ..
                } = &mut part.mapping
                {
                    let dataflow = &mut self.dataflows.outputs[removed_index];
                    if locations
                        .iter()
                        .any(|loc| matches!(loc, FlowInputLocation::InputForOutput { .. }))
                        && !dataflow.inputs.iter().any(|s| s == &Source::Imm(part_index))
                    {
                        let input_index = dataflow.inputs.len();
                        dataflow.inputs.push(Source::Imm(part_index));
                        locations.push(FlowInputLocation::InputForOutput {
                            output_index: removed_index,
                            input_index,
                        })
                    }
                }
            }

            let num_added = self.dataflows.split_flag_output(removed_index);
            let n = self.dataflows.output_dataflows().count();
            let added_index_range = n - num_added..n;

            for part in self.parts.iter_mut() {
                match &mut part.mapping {
                    PartMapping::Register {
                        locations, ..
                    } => {
                        let mut new_locations = Vec::new();
                        let mut removed_indexes = Vec::new();
                        for (location_index, location) in locations.iter_mut().enumerate() {
                            match location {
                                FlowValueLocation::InputForOutput {
                                    output_index, ..
                                }
                                | FlowValueLocation::Output(output_index) => match (*output_index).cmp(&removed_index) {
                                    Ordering::Greater => *output_index -= 1,
                                    Ordering::Equal => {
                                        removed_indexes.push(location_index);
                                        for new_output_index in added_index_range.clone() {
                                            new_locations.push(match location {
                                                FlowValueLocation::InputForOutput {
                                                    input_index, ..
                                                } => FlowValueLocation::InputForOutput {
                                                    output_index: new_output_index,
                                                    input_index: *input_index,
                                                },
                                                FlowValueLocation::Output(_) => FlowValueLocation::Output(new_output_index),
                                                FlowValueLocation::MemoryAddress {
                                                    ..
                                                } => unreachable!(),
                                            });
                                        }
                                    },
                                    Ordering::Less => (),
                                },
                                FlowValueLocation::MemoryAddress {
                                    ..
                                } => {},
                            }
                        }

                        for &index in removed_indexes.iter().rev() {
                            locations.remove(index);
                        }

                        locations.extend(new_locations);
                        locations.sort();
                    },
                    PartMapping::Imm {
                        locations, ..
                    } => {
                        let mut new_locations = Vec::new();
                        let mut removed_indexes = Vec::new();
                        for (location_index, location) in locations.iter_mut().enumerate() {
                            match location {
                                FlowInputLocation::InputForOutput {
                                    output_index, ..
                                } => match (*output_index).cmp(&removed_index) {
                                    Ordering::Greater => *output_index -= 1,
                                    Ordering::Equal => {
                                        removed_indexes.push(location_index);
                                        for new_output_index in added_index_range.clone() {
                                            new_locations.push(match location {
                                                FlowInputLocation::InputForOutput {
                                                    input_index, ..
                                                } => FlowInputLocation::InputForOutput {
                                                    output_index: new_output_index,
                                                    input_index: *input_index,
                                                },
                                                FlowInputLocation::MemoryAddress {
                                                    ..
                                                } => unreachable!(),
                                            });
                                        }
                                    },
                                    Ordering::Less => (),
                                },
                                FlowInputLocation::MemoryAddress {
                                    ..
                                } => {},
                            }
                        }

                        for &index in removed_indexes.iter().rev() {
                            locations.remove(index);
                        }

                        locations.extend(new_locations);
                        locations.sort();
                    },
                    PartMapping::MemoryComputation {
                        ..
                    } => (),
                }
            }
        }
    }

    /// returns what kinds of mapping will be removed: (good_mapping, invalid_mapping)
    pub fn preview_make_bit_fixed(&self, bit_index: usize) -> (usize, usize) {
        let bit = self.bits[bit_index];
        let bit_value = self.instr().nth_bit_from_right(bit_index);
        match bit {
            Bit::Part(part_index) => {
                let part = &self.parts[part_index];
                let bit_index_in_part = self
                    .bits
                    .iter()
                    .take(bit_index)
                    .filter(|b| b == &&Bit::Part(part_index))
                    .count();
                match &part.mapping {
                    PartMapping::Register {
                        mapping, ..
                    } => preview_pick_bit_value(mapping, |x| x.is_some(), bit_index_in_part, bit_value),
                    PartMapping::Imm {
                        mapping, ..
                    } => {
                        if let Some(MappingOrBitOrder::Mapping(mapping)) = mapping {
                            preview_pick_bit_value(mapping, |x| x.is_valid(), bit_index_in_part, bit_value)
                        } else {
                            (1, 0)
                        }
                    },
                    PartMapping::MemoryComputation {
                        mapping, ..
                    } => preview_pick_bit_value(mapping, |x| x.is_some(), bit_index_in_part, bit_value),
                }
            },
            Bit::Fixed(_) => (0, 0),
            Bit::DontCare => (1, 0),
        }
    }

    /// Returns true if the provided `bit` is involved in the computation of a memory address, as a register or memory computation.
    /// Otherwise, returns false.
    ///
    /// Note: If the `bit` is an *immediate value* that is used in the computation of a memory address, false is returned.
    pub fn is_bit_involved_with_address_reg_or_computation(&self, bit: Bit) -> bool {
        if let Bit::Part(n) = bit {
            match &self.parts[n].mapping {
                PartMapping::Imm {
                    ..
                } => false,
                PartMapping::MemoryComputation {
                    ..
                } => true,
                PartMapping::Register {
                    locations, ..
                } => locations
                    .iter()
                    .any(|loc| matches!(loc, FlowValueLocation::MemoryAddress { .. })),
            }
        } else {
            false
        }
    }

    /// Returns true if the provided `bit` affects a register used in a dataflow.
    pub fn is_bit_involved_with_dataflow_reg(&self, bit: Bit) -> bool {
        if let Bit::Part(n) = bit {
            match &self.parts[n].mapping {
                PartMapping::Imm {
                    ..
                } => false,
                PartMapping::MemoryComputation {
                    ..
                } => false,
                PartMapping::Register {
                    locations, ..
                } => locations
                    .iter()
                    .any(|loc| !matches!(loc, FlowValueLocation::MemoryAddress { .. })),
            }
        } else {
            false
        }
    }

    /// Returns true if the provided `bit` is part of an immediate value.
    pub fn is_bit_imm(&self, bit: Bit) -> bool {
        if let Bit::Part(n) = bit {
            matches!(&self.parts[n].mapping, PartMapping::Imm { .. })
        } else {
            false
        }
    }

    /// Returns true if the provided `bit` is part of an immediate value that is used in at least one dataflow.
    pub fn is_bit_dataflow_imm(&self, bit: Bit) -> bool {
        if let Bit::Part(n) = bit {
            matches!(&self.parts[n].mapping, PartMapping::Imm { locations, .. } if locations.iter().any(|loc| matches!(loc, FlowInputLocation::InputForOutput { .. })))
        } else {
            false
        }
    }

    /// Iterates over all `(part_index, loc)` tuples, where `part_index` is the index of a part in the encoding and `loc` is a location where that part is used.
    /// The same `part_index` may occur multiple times with different values for `loc`.
    pub fn part_value_locations(&self) -> impl Iterator<Item = (usize, FlowValueLocation)> + '_ {
        self.parts
            .iter()
            .enumerate()
            .flat_map(|(part_index, part)| match &part.mapping {
                PartMapping::Imm {
                    locations, ..
                } => Some(EitherIter::Left(
                    locations.iter().map(move |&loc| (part_index, FlowValueLocation::from(loc))),
                )),
                PartMapping::Register {
                    locations, ..
                } => Some(EitherIter::Right(locations.iter().map(move |&loc| (part_index, loc)))),
                PartMapping::MemoryComputation {
                    ..
                } => None,
            })
            .flatten()
    }
}

struct FlowValueLocationMap<T> {
    outputs: ArrayVec<Option<T>, 1024>,
    mem: ArrayVec<Option<T>, 1024>,
    num_mem: usize,
    num_outputs: usize,
}

impl<T> FlowValueLocationMap<T> {
    pub fn new(num_mem: usize, num_outputs: usize) -> Self {
        Self {
            outputs: ArrayVec::new(),
            mem: ArrayVec::new(),
            num_mem,
            num_outputs,
        }
    }

    fn mem_index(&self, memory_index: usize, input_index: usize) -> usize {
        self.num_mem * input_index + memory_index
    }

    fn output_index(&self, output_index: usize) -> usize {
        output_index
    }

    fn input_index(&self, output_index: usize, input_index: usize) -> usize {
        self.num_outputs * (input_index + 1) + output_index
    }

    pub fn insert(&mut self, loc: FlowValueLocation, value: T) -> Option<T> {
        let (data, index) = match loc {
            FlowValueLocation::Output(index) => {
                let index = self.output_index(index);
                (&mut self.outputs, index)
            },
            FlowValueLocation::InputForOutput {
                output_index,
                input_index,
            } => {
                let index = self.input_index(output_index, input_index);
                (&mut self.outputs, index)
            },
            FlowValueLocation::MemoryAddress {
                memory_index,
                input_index,
            } => {
                let index = self.mem_index(memory_index, input_index);
                (&mut self.mem, index)
            },
        };

        while data.len() <= index {
            data.push(None);
        }

        let old_value = data[index].take();
        data[index] = Some(value);

        old_value
    }

    pub fn get(&self, loc: FlowValueLocation) -> Option<&T> {
        let (data, index) = match loc {
            FlowValueLocation::Output(index) => {
                let index = self.output_index(index);
                (&self.outputs, index)
            },
            FlowValueLocation::InputForOutput {
                output_index,
                input_index,
            } => {
                let index = self.input_index(output_index, input_index);
                (&self.outputs, index)
            },
            FlowValueLocation::MemoryAddress {
                memory_index,
                input_index,
            } => {
                let index = self.mem_index(memory_index, input_index);
                (&self.mem, index)
            },
        };

        if data.len() <= index { None } else { data[index].as_ref() }
    }
}

impl<A: Arch, C: Clone + Debug> Encoding<A, C> {
    fn compute_new_indices(part_values: &[Option<u64>]) -> ArrayVec<Option<usize>, MAX_PARTS> {
        let mut new_indices = ArrayVec::new();
        let mut n = 0;
        for part_value in part_values.iter() {
            if part_value.is_none() {
                new_indices.push(Some(n));
                n += 1;
            } else {
                new_indices.push(None);
            }
        }

        new_indices
    }

    fn instantiate_dataflows(
        &self, part_values: &[Option<u64>], new_indices: &[Option<usize>],
    ) -> Result<Dataflows<A, C>, InstantiationError> {
        assert_eq!(
            self.parts.len(),
            part_values.len(),
            "A value must be specified for every part"
        );
        assert!(
            self.parts.len() <= MAX_PARTS,
            "We can't handle more than MAX_PARTS={MAX_PARTS} parts"
        );

        let new_instr = self.part_values_to_instr(part_values);

        for (value, part) in part_values.iter().zip(self.parts.iter()) {
            let num_bits = part.size;
            if let Some(value) = value {
                if num_bits < 64 {
                    if let PartMapping::Imm {
                        mapping: Some(MappingOrBitOrder::BitOrder(_bit_order)),
                        ..
                    } = &part.mapping
                    {
                        // TODO
                    } else {
                        assert!(
                            *value <= 1 << num_bits,
                            "Part values: {part_values:X?} not valid for {self:?}; TODO: If this is a BitOrder, we should check if only bits present in the bit order are set instead..."
                        );
                    }

                    if !part.mapping.value_is_valid(*value) {
                        return Err(match part.mapping {
                            PartMapping::Imm {
                                ..
                            } => InstantiationError::MissingImmValueMapping,
                            PartMapping::MemoryComputation {
                                ..
                            } => InstantiationError::MissingMemoryComputationMapping,
                            PartMapping::Register {
                                ..
                            } => InstantiationError::MissingRegisterMapping,
                        })
                    }
                }
            }
        }

        // Make sure MAX_PARTS isn't increased beyond the assumptions we make below
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(MAX_PARTS <= 64);
        }

        #[derive(Copy, Clone, Debug)]
        enum Interp<R> {
            Reg(R),
            Const {
                num_bits: usize,
                mem_value: u64,
                imm_value: u64,
            },
            Addr(AddressComputation),
            None,
        }

        let mut missing_register_mapping = false;
        let mut missing_imm_mapping = false;
        let mut missing_mem_mapping = false;
        let part_interp = self
            .parts
            .iter()
            .zip(part_values.iter().copied())
            .map(|(part, part_value)| {
                if let Some(part_value) = part_value {
                    match &part.mapping {
                        PartMapping::Register {
                            mapping, ..
                        } => {
                            let reg = if let Some(value) = &mapping[part_value as usize] {
                                *value
                            } else {
                                missing_register_mapping = true;
                                return Interp::None
                            };

                            Interp::Reg(reg)
                        },
                        PartMapping::Imm {
                            mapping,
                            bits,
                            ..
                        } => {
                            // Correct for immediate value bits that we might have removed with remove_bits
                            let imm_value = bits
                                .as_ref()
                                .map(|bits| bits.interpret_value(part_value))
                                .unwrap_or(part_value);

                            match mapping {
                                Some(MappingOrBitOrder::Mapping(mapping)) => {
                                    if mapping[part_value as usize].is_valid() {
                                        Interp::Const {
                                            mem_value: part_value,
                                            imm_value,
                                            num_bits: part.size,
                                        }
                                    } else {
                                        missing_imm_mapping = true;
                                        Interp::None
                                    }
                                },
                                Some(MappingOrBitOrder::BitOrder(bit_order)) => {
                                    let mem_value = bit_order.iter().enumerate().fold(0, |acc: u64, (index, bit)| {
                                        acc.wrapping_add(bit.as_offset((part_value >> index) & 1))
                                    });

                                    Interp::Const {
                                        mem_value,
                                        imm_value,
                                        num_bits: part.size,
                                    }
                                },
                                _ => Interp::Const {
                                    mem_value: part_value,
                                    imm_value,
                                    num_bits: part.size,
                                },
                            }
                        },
                        PartMapping::MemoryComputation {
                            mapping, ..
                        } => {
                            if let Some(mapped_value) = mapping[part_value as usize] {
                                Interp::Addr(mapped_value)
                            } else {
                                missing_mem_mapping = true;
                                Interp::None
                            }
                        },
                    }
                } else {
                    Interp::None
                }
            })
            .collect::<ArrayVec<_, MAX_PARTS>>();

        if missing_register_mapping {
            return Err(InstantiationError::MissingRegisterMapping)
        }

        if missing_imm_mapping {
            return Err(InstantiationError::MissingImmValueMapping);
        }

        if missing_mem_mapping {
            return Err(InstantiationError::MissingMemoryComputationMapping);
        }

        let mut applicable_part = FlowValueLocationMap::new(self.dataflows.addresses.len(), self.dataflows.outputs.len());
        for ((part, part_value), interp) in self.parts.iter().zip(part_values.iter().copied()).zip(part_interp.iter()) {
            if part_value.is_some() {
                match &part.mapping {
                    PartMapping::Register {
                        locations, ..
                    } => {
                        for loc in locations {
                            assert!(applicable_part.insert(*loc, interp).is_none());
                        }
                    },
                    PartMapping::Imm {
                        locations, ..
                    } => {
                        for loc in locations {
                            assert!(applicable_part.insert(FlowValueLocation::from(*loc), interp).is_none());
                        }
                    },
                    PartMapping::MemoryComputation {
                        ..
                    } => (),
                }
            }
        }

        let dataflows = self.dataflows.map(new_instr, |loc, old| {
            let mut result = *old;

            if let Some(&&interp) = applicable_part.get(loc) {
                match interp {
                    Interp::Reg(new_reg) => if let Source::Dest(Dest::Reg(reg, _)) = &mut result {
                        *reg = new_reg;
                    } else {
                        panic!("Invalid encoding (at {loc:?} there should be a register): {self:?}");
                    },
                    Interp::Const { num_bits, mem_value, imm_value } => if loc.is_address() {
                        result = Source::Const { num_bits, value: mem_value };
                    } else {
                        result = Source::Const { num_bits, value: imm_value };
                    },
                    _ => unreachable!(),
                }
            } else if let Source::Imm(n) = &mut result {
                if let Some(val) = new_indices[*n] {
                    *n = val;
                } else {
                    // if new_indices[*n] is None, then it will be replaced with a Source::Const in the match above
                    panic!("Encoding is not valid: {self:#?}; found {result:?} at {loc:?} which is not being remapped to a new index");
                }
            }

            Some(result)
        }, |memory_index, old_computation| {
            for (part_index, (part, part_value)) in self.parts.iter().zip(part_values.iter().copied()).enumerate() {
                if part_value.is_some() {
                    if let PartMapping::MemoryComputation { memory_indexes, .. } = &part.mapping {
                        if memory_indexes.contains(&memory_index) {
                            match part_interp[part_index] {
                                // TODO: Should we really copy the offset here?
                                Interp::Addr(addr) => return Some(addr.with_offset(old_computation.offset)),
                                _ => unreachable!(),
                            }
                        }
                    }
                }
            }

            None
        });

        Ok(dataflows)
    }

    /// Instantiates the encoding with the provided part values.
    /// Returns the dataflows for the instruction that corresponds to these part values.
    ///
    /// Use [`Self::extract_parts`] to convert a covered [`Instruction`] into part values.
    pub fn instantiate(&self, part_values: &[u64]) -> Result<Dataflows<A, C>, InstantiationError> {
        let part_values = part_values.iter().map(|&v| Some(v)).collect::<ArrayVec<_, MAX_PARTS>>();
        let new_indices = Self::compute_new_indices(&part_values);

        self.instantiate_dataflows(&part_values, &new_indices)
    }

    /// Iterates over covered instructions randomly.
    /// May yield the same instruction multiple times.
    /// Does not terminate.
    ///
    /// `part_values` can be used to restrict the yielded instructions to have fixed part values.
    /// Even if all `part_values` are set, different instructions might be yielded if one or more bits are [`Bit::DontCare`].
    pub fn random_instrs<'a>(
        &'a self, part_value: &'a [Option<u64>], rng: &'a mut impl Rng,
    ) -> impl Iterator<Item = Instruction> + 'a {
        repeat_with(move || {
            let parts = self
                .parts
                .iter()
                .zip(part_value.iter())
                .map(|(p, fixed_value)| {
                    fixed_value.unwrap_or_else(|| {
                        if let Some(iter) = p.mapping.valid_values() {
                            iter.choose(rng).unwrap() as u64
                        } else {
                            rng.gen::<u64>() & !(u64::MAX.checked_shl(p.size as u32).unwrap_or(0))
                        }
                    })
                })
                .collect::<Vec<_>>();
            let mut instr = self.all_part_values_to_instr(&parts);

            for (index, bit) in self.bits.iter().enumerate() {
                if let Bit::DontCare = bit {
                    instr.set_nth_bit_from_right(index, rng.gen_range(0..=1));
                }
            }

            instr
        })
    }
}

fn remove_bit(value: u64, bit_index: usize) -> (u64, bool) {
    let lower_value = value & ((1 << bit_index) - 1);
    let upper_value = (value >> (bit_index + 1)) << bit_index;
    let bit = (value >> bit_index) & 1 != 0;

    (lower_value | upper_value, bit)
}

impl<A: Arch, C: Computation> Encoding<A, C> {
    /// Automatically fixes some consistency issues in an encoding.
    pub fn fix(&mut self) -> bool {
        // Make sure all immediate values are correctly numbered
        for (part_index, part) in self.parts.iter_mut().enumerate() {
            part.size = self.bits.iter().filter(|&&bit| bit == Bit::Part(part_index)).count();

            if let PartMapping::Imm {
                locations, ..
            } = &mut part.mapping
            {
                for location in locations.iter_mut() {
                    match location {
                        FlowInputLocation::InputForOutput {
                            output_index,
                            input_index,
                        } => match &mut self.dataflows.outputs[*output_index].inputs[*input_index] {
                            Source::Imm(n) => {
                                *n = part_index;
                            },
                            v @ Source::Const {
                                ..
                            } => {
                                *v = Source::Imm(part_index);
                            },
                            _ => return false,
                        },
                        FlowInputLocation::MemoryAddress {
                            memory_index,
                            input_index,
                        } => match &mut self.dataflows.addresses.memory[*memory_index].inputs[*input_index] {
                            Source::Imm(n) => {
                                *n = part_index;
                            },
                            v @ Source::Const {
                                ..
                            } => {
                                *v = Source::Imm(part_index);
                            },
                            _ => return false,
                        },
                    }
                }
            }
        }

        // Make sure all immediate values are correctly registered in a part
        for (output_index, flow) in self.dataflows.outputs.iter().enumerate() {
            for (input_index, input) in flow.inputs.iter().enumerate() {
                if let Source::Imm(n) = input {
                    if let PartMapping::Imm {
                        locations, ..
                    } = &mut self.parts[*n].mapping
                    {
                        let loc = FlowInputLocation::InputForOutput {
                            output_index,
                            input_index,
                        };
                        if !locations.contains(&loc) {
                            locations.push(loc);
                        }
                    } else {
                        error!("Invalid PartMapping: {:?} {}", self, self);
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Returns a new encoding where the parts for which `part_values` is set to `Some(..)` are instantiated.
    pub fn instantiate_partially(&self, part_values: &[Option<u64>]) -> Result<Encoding<A, C>, InstantiationError> {
        let new_indices = Self::compute_new_indices(part_values);
        let dataflows = self.instantiate_dataflows(part_values, &new_indices)?;

        let parts = self
            .parts
            .iter()
            .cloned()
            .zip(part_values.iter().copied())
            .filter(|(_, p)| p.is_none())
            .map(|(p, _)| p)
            .collect::<Vec<_>>();

        let bits = self
            .bits
            .iter()
            .copied()
            .enumerate()
            .map(|(i, b)| match b {
                Bit::Part(n) => match new_indices[n] {
                    Some(new) => Bit::Part(new),
                    None => Bit::Fixed(dataflows.instr().nth_bit_from_right(i)),
                },
                other => other,
            })
            .collect::<Vec<_>>();

        trace!("Instantiate with {part_values:02X?}: {self}");

        let write_ordering = self
            .write_ordering
            .iter()
            // Make sure we only keep write orderings that are relevant for this set of part values.
            .filter(|wo| {
                wo.part_values
                    .iter()
                    .zip(part_values.iter())
                    .all(|(val, set)| match (val, set) {
                        (Some(val), Some(set)) => val == set,
                        _ => true,
                    })
            })
            .map(|wo| WriteOrdering {
                part_values: wo
                    .part_values
                    .iter()
                    .zip(part_values.iter())
                    .filter(|(_, set)| !set.is_some())
                    .map(|(&val, _)| val)
                    .collect(),
                output_index_order: wo.output_index_order.clone(),
            })
            .unique()
            .collect::<Vec<_>>();

        Ok(Encoding {
            dataflows,
            errors: self.errors.clone(),
            bits,
            parts,
            write_ordering,
        })
    }

    /// Replaces the bit at position `bit_index` with a fixed bit.
    /// The fixed bit is taken from [`Self::instr`].
    pub fn make_bit_fixed(&mut self, bit_index: usize) -> Result<(), InstantiationError> {
        let bit = self.bits[bit_index];
        let bit_value = self.instr().nth_bit_from_right(bit_index);
        let new_bit = Bit::Fixed(bit_value);

        match bit {
            Bit::Part(part_index) => {
                let part = &mut self.parts[part_index];
                if part.size <= 1 {
                    // Remove the entire part
                    let values = self
                        .extract_parts(self.instr())
                        .into_iter()
                        .enumerate()
                        .map(|(n, v)| if n == part_index { Some(v) } else { None })
                        .collect::<Vec<_>>();

                    *self = self.instantiate_partially(&values)?;
                } else {
                    let bit_index_in_part = self.bits[..bit_index]
                        .iter()
                        .filter(|&&bit| bit == Bit::Part(part_index))
                        .count();

                    self.bits[bit_index] = new_bit;
                    part.size -= 1;

                    match &mut part.mapping {
                        PartMapping::Register {
                            mapping, ..
                        } => *mapping = pick_bit_value(mapping, bit_index_in_part, bit_value),
                        PartMapping::Imm {
                            mapping,
                            locations,
                            bits,
                        } => {
                            match mapping {
                                // TODO: Abort here! This doesn't work!
                                Some(MappingOrBitOrder::Mapping(mapping)) => {
                                    *mapping = pick_bit_value(mapping, bit_index_in_part, bit_value)
                                },
                                Some(MappingOrBitOrder::BitOrder(bit_order)) => {
                                    let removed = bit_order.remove(bit_index_in_part);
                                    let offset = removed.as_offset(new_bit.unwrap_fixed() as u64);

                                    for location in locations.iter() {
                                        match location {
                                            FlowInputLocation::InputForOutput {
                                                ..
                                            } => (),
                                            FlowInputLocation::MemoryAddress {
                                                memory_index,
                                                input_index,
                                            } => {
                                                let calculation = &mut self.dataflows.addresses[*memory_index].calculation;
                                                let applied_offset = calculation.terms[*input_index].apply(offset);
                                                calculation.offset = calculation.offset.wrapping_add(applied_offset as i64);
                                            },
                                        }
                                    }
                                },
                                None => (),
                            }

                            if locations.iter().any(|loc| match loc {
                                FlowInputLocation::InputForOutput {
                                    output_index, ..
                                } => self.dataflows.output_dataflow(*output_index).computation.is_some(),
                                FlowInputLocation::MemoryAddress {
                                    ..
                                } => false,
                            }) {
                                if bits.is_none() {
                                    *bits = Some(ImmBits::new(repeat(ImmBit::Fill).take(part.size + 1)));
                                }

                                let bits = bits.as_mut().unwrap();

                                let mut n = 0;
                                for bit in bits.iter_mut() {
                                    if *bit == ImmBit::Fill {
                                        if n == bit_index_in_part {
                                            *bit = match bit_value {
                                                0 => ImmBit::Is0,
                                                1 => ImmBit::Is1,
                                                _ => unreachable!(),
                                            };

                                            break
                                        }

                                        n += 1;
                                    }
                                }
                            }
                        },
                        PartMapping::MemoryComputation {
                            mapping, ..
                        } => *mapping = pick_bit_value(mapping, bit_index_in_part, bit_value),
                    }

                    (part.value, _) = remove_bit(part.value, bit_index_in_part);

                    trace!(
                        "Write ordering before removing bit {bit_index_in_part}: {:?}",
                        self.write_ordering
                    );
                    self.write_ordering.retain_mut(|wo| {
                        if let Some(val) = &mut wo.part_values[part_index] {
                            let (new_val, removed) = remove_bit(*val, bit_index_in_part);
                            *val = new_val;
                            matches!((removed, new_bit), (true, Bit::Fixed(1)) | (false, Bit::Fixed(0)))
                        } else {
                            true
                        }
                    });
                    trace!("Write ordering after: {:?}", self.write_ordering);
                }
            },
            Bit::Fixed(_) => {},
            Bit::DontCare => self.bits[bit_index] = new_bit,
        }

        for part in self.parts.iter() {
            match &part.mapping {
                PartMapping::Imm {
                    mapping: Some(MappingOrBitOrder::Mapping(mapping)),
                    ..
                } => {
                    if mapping.iter().all(|item| item.is_invalid()) {
                        return Err(InstantiationError::MissingImmValueMapping)
                    }
                },
                PartMapping::Imm {
                    ..
                } => (),
                PartMapping::MemoryComputation {
                    mapping, ..
                } => {
                    if mapping.iter().all(|item| item.is_none()) {
                        return Err(InstantiationError::MissingMemoryComputationMapping)
                    }
                },
                PartMapping::Register {
                    mapping, ..
                } => {
                    if mapping.iter().all(|item| item.is_none()) {
                        return Err(InstantiationError::MissingRegisterMapping)
                    }
                },
            }
        }

        Ok(())
    }

    /// Removes the byte at position `index` (counting from the left) from the encoding.
    /// Panics if this would remove any bitpatterns.
    /// If you want to remove a byte that contains parts, first call [`Self::make_bit_fixed`] for each part bit in that byte.
    pub fn remove_byte(&mut self, index: usize) {
        let mut instr_bytes = self.dataflows.instr().bytes().to_vec();
        instr_bytes.remove(index);
        self.dataflows.addresses.instr = Instruction::new(&instr_bytes);

        let bit_start = self.bits.len() - (index + 1) * 8;
        for bit in self.bits.drain(bit_start..bit_start + 8) {
            assert!(matches!(bit, Bit::DontCare | Bit::Fixed(_)));
        }
    }

    /// Determines the best instruction to use for encoding analysis.
    ///
    /// The primary criteria to determine the "best" instruction are:
    ///
    /// - it uses as many different registers as possible
    /// - fills immediate values such that there are at least two bits 1 and two bits 0 in each byte.
    pub fn best_instr(&self) -> Option<Instruction> {
        let reg_choice_locations = self
            .parts
            .iter()
            .flat_map(|p| match &p.mapping {
                PartMapping::Register {
                    locations,
                    mapping: _,
                } => locations.iter(),
                _ => [].iter(),
            })
            .collect::<Vec<_>>();
        let current_choices = self.parts.iter().map(|p| p.value).collect::<Vec<_>>();
        let fixed_register_use = {
            let mut h = HashMap::new();
            for reg in self
                .dataflows
                .values()
                .filter(|(loc, _)| !reg_choice_locations.contains(&loc))
                .flat_map(|(_, s)| match s {
                    Source::Dest(Dest::Reg(reg, _)) => Some(reg),
                    _ => None,
                })
            {
                h.entry(reg).or_insert(1);
            }

            h
        };

        let compute_score = |new_choices: &[u64]| {
            let mut register_use = fixed_register_use.clone();
            let mut bad = false;

            // Count how many times each register is used
            for (part, choice) in self.parts.iter().zip(new_choices.iter()) {
                if let Some(values) = part.mapping.register_mapping() {
                    match &values[*choice as usize] {
                        Some(r) if r.is_zero() => bad = true,
                        Some(r) => {
                            let v = register_use.entry(*r).or_insert(0);
                            *v += 1;
                        },
                        None => bad = true,
                    }
                }
            }

            let score = if !bad {
                // Count the number of register mappings that use the exact same value
                let mut register_choices = self
                    .parts
                    .iter()
                    .zip(new_choices.iter())
                    .filter(|(part, _)| part.mapping.register_mapping().is_some())
                    .map(|(_, &choice)| choice)
                    .collect::<Vec<_>>();
                register_choices.sort();
                let len_before = register_choices.len();
                register_choices.dedup();
                let duplication_penalty = len_before - register_choices.len();

                // Count the number of register pairs that have a 0 or 1 hamming distance between them
                let mut one_bit_distances = 0;
                let register_choices = self
                    .parts
                    .iter()
                    .zip(new_choices.iter())
                    .flat_map(|(part, choice)| {
                        part.mapping
                            .register_mapping()
                            .map(|m| m[*choice as usize].expect("if !bad, all register choices should be mappable"))
                    })
                    .map(|reg| (reg, A::iter_regs().position(|item| item == reg).unwrap()))
                    .collect::<Vec<_>>();

                for (_, index_a) in register_choices.iter() {
                    for (_, index_b) in register_choices.iter() {
                        match (index_a ^ index_b).count_ones() {
                            0 => one_bit_distances += 5,
                            1 => one_bit_distances += 1,
                            _ => (),
                        }
                    }
                }

                let score = register_use.values().map(|v| v * v).sum::<usize>();
                score * 100 + duplication_penalty + one_bit_distances
            } else {
                999_999_999
            };

            debug!("- single score for {new_choices:X?} = {score}");

            score
        };

        let compute_full_score = |new_choices: &[u64]| {
            // Weigh the score of the current chosen encoding much heavier than that of the bitflips
            let mut score = compute_score(new_choices) * 0x100;
            for (choice_index, part) in self.parts.iter().enumerate() {
                if let Some(values) = part.mapping.register_mapping() {
                    for bit in 0..self.value_bits(choice_index) {
                        let mut choices_with_flipped_bit = new_choices.to_vec();
                        choices_with_flipped_bit[choice_index] ^= 1 << bit;

                        score += compute_score(&choices_with_flipped_bit);
                    }

                    match &values[new_choices[choice_index] as usize] {
                        Some(r) if r.should_avoid() || r.is_zero() => score *= 2,
                        _ => (),
                    }
                }
            }

            debug!("Combined score for {new_choices:X?} = {score}");

            score
        };

        let mut perfect_choices = self
            .find_best_reg_choices(false, compute_full_score)
            .map(|choices| {
                choices
                    .iter()
                    .enumerate()
                    .map(|(index, value)| value.unwrap_or(current_choices[index]))
                    .collect()
            })
            .unwrap_or_else(|| current_choices.clone());

        let value_imms = self
            .parts
            .iter()
            .enumerate()
            .filter(|(_, p)| match &p.mapping {
                PartMapping::Imm {
                    mapping: Some(MappingOrBitOrder::BitOrder(_)),
                    ..
                } => false,
                PartMapping::Imm {
                    ..
                } => true,
                _ => false,
            })
            .map(|(n, _)| n)
            .collect::<HashSet<_>>();
        debug!("ValueImms: {value_imms:?}");
        self.fill_value_imms(&mut perfect_choices, value_imms);

        let will_return_instr_anyway = perfect_choices != current_choices;
        let addr_imms = self
            .parts
            .iter()
            .enumerate()
            .filter(|(_, p)| match &p.mapping {
                PartMapping::Imm {
                    mapping: Some(MappingOrBitOrder::BitOrder(bit_order)),
                    ..
                } => {
                    let bits_covered = bit_order
                        .iter()
                        .map(|bit| match bit {
                            ImmBitOrder::Positive(n) | ImmBitOrder::Negative(n) => 1u64 << n,
                        })
                        .fold(0, |a, b| a | b);

                    // only include addr imm in choices if the number of address bits looks strange,
                    // or if we're going to return Some(instr) anyways.
                    bits_covered.count_ones() % 4 != 0 || will_return_instr_anyway
                },
                _ => false,
            })
            .filter(|(_, part)| part.size >= 3)
            .map(|(n, _)| n)
            .collect::<HashSet<_>>();
        debug!("AddrImms: {addr_imms:?}");
        self.fill_addr_imms(&mut perfect_choices, addr_imms);

        debug!(
            "Parts: {:?} with perfect choices={perfect_choices:X?}, current choices={current_choices:X?}",
            self.parts
        );

        // TODO: Pick address computations such that at least one value is *1, and not *2,*4 or *8.

        if perfect_choices == current_choices {
            None
        } else if let Ok(dataflows) = self.instantiate(&perfect_choices) {
            debug!("Instantiated: {dataflows:X?}");
            Some(dataflows.addresses.instr)
        } else {
            error!("best_instr: unable to instantiate perfect instruction!");
            None
        }
    }

    /// Returns the number of bits that aren't `Fixed` in the encoding.
    /// This is equivalent to the number of `Part` bits and `DontCare` bits.
    pub fn num_wildcard_bits(&self) -> usize {
        self.bits.iter().filter(|bit| !matches!(bit, Bit::Fixed(_))).count()
    }

    /// Returns the number of bits that are `DontCare` in the encoding.
    pub fn num_dontcare_bits(&self) -> usize {
        self.bits.iter().filter(|bit| matches!(bit, Bit::DontCare)).count()
    }

    /// Returns the number of `Part` bits in the encoding.
    pub fn part_size(&self, index: usize) -> usize {
        self.bits.iter().filter(|&&b| b == Bit::Part(index)).count()
    }

    /// Iterates over all possible instructions that match the encoding.
    /// If `fixed_value[N]` is `Some(val)`, then only instructions where part `N` is val are returned.
    pub fn iter_instrs<'a>(
        &'a self, fixed_value: &'a [Option<u64>], iter_dontcare: bool,
    ) -> impl Iterator<Item = Instruction> + 'a {
        let dontcare_indices = if iter_dontcare {
            self.bits
                .iter()
                .enumerate()
                .filter(|(_, &bit)| bit == Bit::DontCare)
                .map(|(n, _)| n)
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        assert!(dontcare_indices.len() < 24);

        (0..(1u64 << dontcare_indices.len())).flat_map(move |c| {
            let mut current = self
                .parts
                .iter()
                .map(|part| part.mapping.first_valid_value())
                .collect::<Vec<_>>();
            let mut done = false;

            repeat_with(move || {
                loop {
                    if done {
                        return None
                    }

                    let instantiation = self.instantiate(&current);

                    let mut carry = 1;
                    for ((current, val), part) in current.iter_mut().zip(fixed_value).zip(self.parts.iter()) {
                        if val.is_none() {
                            *current += carry;
                            if *current >= (1 << part.size) as u64 {
                                *current = 0;
                                carry = 1;
                            } else {
                                carry = 0;
                            }
                        }
                    }

                    done = carry != 0;

                    if let Ok(result) = instantiation {
                        return Some(*result.instr())
                    }
                }
            })
            .take_while(|x| x.is_some())
            .flatten()
            .map(move |mut instr| {
                let mut n = 0;
                for (index, &bit) in self.bits.iter().enumerate() {
                    if bit == Bit::DontCare {
                        instr = instr.with_nth_bit_from_right(index, ((c >> n) & 1) as u8);
                        n += 1;
                    }
                }

                instr
            })
        })
    }

    /// Converts the encoding into a canonical form.
    /// This sets all parts to the lowest valid value.
    pub fn canonicalize(&self) -> Encoding<A, C> {
        info!("Canonicalizing {}", self);

        // Transform the encoding into a canonical form.
        // The canonical form uses the minimum value for all parts.
        let min_parts = self
            .parts
            .iter()
            .map(|part| match &part.mapping {
                PartMapping::Register {
                    mapping, ..
                } => mapping.iter().enumerate().find(|(_, v)| v.is_some()).unwrap().0,
                PartMapping::Imm {
                    mapping, ..
                } => match mapping {
                    Some(MappingOrBitOrder::Mapping(mapping)) => {
                        mapping.iter().enumerate().find(|(_, v)| v.is_valid()).unwrap().0
                    },
                    _ => 0,
                },
                PartMapping::MemoryComputation {
                    mapping, ..
                } => mapping.iter().enumerate().find(|(_, v)| v.is_some()).unwrap().0,
            } as u64)
            .collect::<Vec<_>>();
        let mut dataflows = self.instantiate(&min_parts).unwrap();
        let mut parts = self
            .parts
            .iter()
            .zip(min_parts.iter())
            .map(|(part, &new_value)| Part {
                value: new_value,
                ..part.clone()
            })
            .collect::<Vec<_>>();

        let instr = &mut dataflows.addresses.instr;
        for (index, bit) in self.bits.iter().enumerate() {
            if let Bit::DontCare = bit {
                *instr = instr.with_nth_bit_from_right(index, 0);
            }
        }

        dataflows.addresses = dataflows.addresses.map_computations(|memory_index, inputs, current| {
            let mut input_term_pairs = inputs
                .iter()
                .zip(current.terms.iter())
                .enumerate()
                .map(|(input_index, (&input, &term))| (input, input_index, term))
                .collect::<Vec<_>>();
            input_term_pairs.sort_by_key(|&(input, ..)| input);

            debug!("Mapping {:?} with {:?} to: {:?}", inputs, current, input_term_pairs);

            // We need to update the part mapping, so that it contains the correct indices
            let mut index_mapping = (0..inputs.len()).collect::<Vec<_>>();
            for (index, (_, old_index, _)) in input_term_pairs.iter().enumerate() {
                index_mapping[*old_index] = index;
            }

            for part in parts.iter_mut() {
                match &mut part.mapping {
                    PartMapping::Register {
                        locations, ..
                    } => {
                        for location in locations.iter_mut() {
                            match location {
                                FlowValueLocation::MemoryAddress {
                                    memory_index: index,
                                    input_index,
                                } if *index == memory_index => *input_index = index_mapping[*input_index],
                                _ => (),
                            }
                        }
                    },
                    PartMapping::Imm {
                        locations, ..
                    } => {
                        for location in locations.iter_mut() {
                            match location {
                                FlowInputLocation::MemoryAddress {
                                    memory_index: index,
                                    input_index,
                                } if *index == memory_index => *input_index = index_mapping[*input_index],
                                _ => (),
                            }
                        }
                    },
                    PartMapping::MemoryComputation {
                        mapping,
                        memory_indexes,
                    } if memory_indexes.contains(&memory_index) => {
                        if memory_indexes.len() > 1 {
                            panic!("Can't handle memory computation parts that influence more than one memory access");
                        }

                        for computation in mapping.iter_mut().flatten() {
                            let mut new_terms = [AddrTerm::default(); 4];
                            for index in 0..4 {
                                if let Some(new_index) = index_mapping.get(index) {
                                    new_terms[*new_index] = computation.terms[index];
                                }
                            }

                            *computation = AddressComputation::from_iter(IntoIterator::into_iter(new_terms), computation.offset);
                        }
                    },
                    _ => (),
                }
            }

            let inputs = Inputs::unsorted(input_term_pairs.iter().map(|&(input, ..)| input).collect());
            let calculation =
                AddressComputation::from_iter(input_term_pairs.into_iter().map(|(_, _, term)| term), current.offset);

            (inputs, calculation)
        });

        let mut e = Encoding {
            bits: self.bits.clone(),
            errors: self.errors.clone(),
            dataflows,
            parts,
            write_ordering: self.write_ordering.clone(),
        };
        assert!(e.fix(), "Unable to fix {e}");
        e
    }

    /// Reduces the scope of the encoding such that it covers no more instructions than (but potentially less than) the provided `filter`.
    pub fn restrict_to(&self, filter: &InstructionFilter) -> Result<Self, RestrictError> {
        trace!("Restricting to {filter:?}: {self}");

        let mut result = self.clone();

        let check = result.integrity_check();
        assert!(
            check.is_ok(),
            "Integrity check fails before call to restrict_to: {}: {self}\n\n{self:?}",
            check.unwrap_err()
        );

        // Fast path to eliminate an entire part if we're setting all bits to a concrete value
        for (part_index, _) in self.parts.iter().enumerate().rev() {
            if self
                .bits
                .iter()
                .enumerate()
                .all(|(index, &bit)| bit != Bit::Part(part_index) || filter.nth_bit_from_right(index) != FilterBit::Wildcard)
            {
                // We're setting all bits of this part!
                let mut instr = *result.instr();
                for (index, &bit) in result.bits.iter().enumerate() {
                    if bit == Bit::Part(part_index) {
                        instr.set_nth_bit_from_right(index, filter.nth_bit_from_right(index).as_u8().unwrap());
                    }
                }

                let part_values = result
                    .extract_parts(&instr)
                    .into_iter()
                    .enumerate()
                    .map(|(index, value)| if index == part_index { Some(value) } else { None })
                    .collect::<Vec<_>>();

                result = match result.instantiate_partially(&part_values) {
                    Ok(result) => result,
                    Err(
                        InstantiationError::MissingImmValueMapping
                        | InstantiationError::MissingMemoryComputationMapping
                        | InstantiationError::MissingRegisterMapping,
                    ) => return Err(RestrictError::NoOverlap),
                };

                let check = result.integrity_check();
                assert!(
                    check.is_ok(),
                    "Integrity check fails after instantiating {part_index} via {part_values:X?}: {}:\n{result}\n\n{result:?}\n\nFilter={filter:?}; Original=\n{self}",
                    check.unwrap_err()
                );
            }
        }

        let num_bits = result.bits.len();
        for bit_index in 0..num_bits {
            let bit = result.bits[bit_index];
            let new_bit = filter.nth_bit_from_right(bit_index);
            match (bit, new_bit) {
                (Bit::Part(_) | Bit::Fixed(_) | Bit::DontCare, FilterBit::Wildcard)
                | (Bit::Fixed(1), FilterBit::Is1)
                | (Bit::Fixed(0), FilterBit::Is0) => (),
                (Bit::Fixed(0), FilterBit::Is1) | (Bit::Fixed(1), FilterBit::Is0) => return Err(RestrictError::NoOverlap),
                (Bit::Part(part_index), FilterBit::Is0 | FilterBit::Is1) => {
                    if let PartMapping::Imm {
                        locations,
                        mapping,
                        ..
                    } = &result.parts[part_index].mapping
                    {
                        if let Some(loc) = locations.iter().find(|loc| match loc {
                            FlowInputLocation::MemoryAddress {
                                ..
                            } => !matches!(mapping, Some(MappingOrBitOrder::BitOrder(_))),
                            _ => false,
                        }) {
                            error!("Remove bits from Imm in {loc:?} without changing the meaning: {filter:?} {result}");
                            panic!("Cannot remove memory imm bit if we do not have bitorder");
                        }
                    }

                    // println!("Setting bit {bit_index}={new_bit:?} for {:?}", result.instr());
                    result
                        .dataflows
                        .addresses
                        .instr
                        .set_nth_bit_from_right(bit_index, new_bit.as_u8().unwrap());
                    // println!("Result: {:?}", result.instr());

                    // println!("Now removing bit {bit_index}");
                    match result.make_bit_fixed(bit_index) {
                        Ok(_) => (),
                        Err(
                            InstantiationError::MissingImmValueMapping
                            | InstantiationError::MissingMemoryComputationMapping
                            | InstantiationError::MissingRegisterMapping,
                        ) => return Err(RestrictError::NoOverlap),
                    }

                    // println!("Result: {result}");
                },
                (Bit::DontCare, FilterBit::Is0 | FilterBit::Is1) => {
                    let bit = new_bit.as_u8().unwrap();
                    result.dataflows.addresses.instr.set_nth_bit_from_right(bit_index, bit);
                    result.bits[bit_index] = Bit::Fixed(bit);

                    // println!("Fixed DontCare bit @ {bit_index}: {result}");
                },
                (Bit::Fixed(2..), _) => unreachable!(),
            }
        }

        for part_index in (0..result.parts.len()).rev() {
            let (is_single_item, part_value) = match &result.parts[part_index].mapping {
                PartMapping::Register {
                    mapping, ..
                } => (
                    mapping.iter().flatten().unique().count() == 1,
                    mapping.iter().position(Option::is_some).unwrap(),
                ),
                _ => (false, 0),
            };

            if is_single_item {
                let bits = result
                    .bits
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|&(_, bit)| bit == Bit::Part(part_index))
                    .collect::<Vec<_>>();
                let mut part_values = vec![None; result.parts.len()];
                part_values[part_index] = Some(part_value as u64);
                result = result.instantiate_partially(&part_values).unwrap();
                for (index, _) in bits {
                    result.bits[index] = Bit::DontCare;
                }
            }
        }

        // println!("Restricted: {result} {result:?}");
        let check = result.integrity_check();
        assert!(
            check.is_ok(),
            "Restricted fails integrity check: {}: {result}; Filter={filter:?}; Original={self}",
            check.unwrap_err()
        );

        // result.reduce_parts();

        Ok(result)
    }

    fn update_remapped_input_references(parts: &mut [Part<A>], index: usize, remap: &[Option<usize>]) {
        for part in parts.iter_mut() {
            match &mut part.mapping {
                PartMapping::Imm {
                    locations, ..
                } => locations.retain_mut(|location| match location {
                    FlowInputLocation::InputForOutput {
                        output_index,
                        input_index,
                    } => {
                        if *output_index == index {
                            if let Some(new_index) = remap[*input_index] {
                                *input_index = new_index;
                                true
                            } else {
                                false
                            }
                        } else {
                            true
                        }
                    },
                    FlowInputLocation::MemoryAddress {
                        ..
                    } => true,
                }),
                PartMapping::Register {
                    locations, ..
                } => locations.retain_mut(|location| match location {
                    FlowValueLocation::InputForOutput {
                        output_index,
                        input_index,
                    } => {
                        if *output_index == index {
                            if let Some(new_index) = remap[*input_index] {
                                *input_index = new_index;
                                true
                            } else {
                                false
                            }
                        } else {
                            true
                        }
                    },
                    FlowValueLocation::Output(_)
                    | FlowValueLocation::MemoryAddress {
                        ..
                    } => true,
                }),
                PartMapping::MemoryComputation {
                    ..
                } => (),
            }
        }
    }

    /// Removes all inputs in the dataflows that are not used in the computations.
    /// If a dataflow has no computation, the inputs are not modified.
    pub fn remove_unused_inputs(mut self) -> Encoding<A, C> {
        info!("Remapping inputs in: {self}");

        for (index, output) in self.dataflows.outputs.iter_mut().enumerate() {
            if let Some(computation) = &mut output.computation {
                let used_indices = computation.used_input_indices();
                let indices_to_keep = (0..output.inputs.len())
                    .map(|n| used_indices.contains(&n))
                    .collect::<GrowingBitmap>();

                if !indices_to_keep.is_all_ones() {
                    debug!("Indices to keep: {indices_to_keep:?}");
                    let mut remap = Vec::new();
                    let mut new_index = 0;
                    for index in 0..output.inputs.len() {
                        if indices_to_keep[index] {
                            remap.push(Some(new_index));
                            new_index += 1;
                        } else {
                            remap.push(None);
                        }
                    }

                    debug!("Remapping: {remap:?}");
                    debug!("Before: {}", computation.display(ARG_NAMES));
                    computation.remap_inputs(&remap);
                    debug!("After : {}", computation.display(ARG_NAMES));

                    debug!("Inputs before: {:?}", output.inputs);
                    for index in (0..output.inputs.len()).rev() {
                        if !indices_to_keep[index] {
                            output.inputs.remove_index(index);
                        }
                    }

                    debug!("Inputs after : {:?}", output.inputs);

                    // Remap any references in parts
                    Self::update_remapped_input_references(&mut self.parts, index, &remap);
                }
            }
        }

        info!("Remapped inputs: {self}");

        self
    }

    fn update_remapped_output_indices(&mut self, remap: Vec<Option<usize>>) {
        for part in self.parts.iter_mut() {
            match &mut part.mapping {
                PartMapping::Imm {
                    locations, ..
                } => locations.retain_mut(|location| match location {
                    FlowInputLocation::InputForOutput {
                        output_index, ..
                    } => {
                        if let Some(new_index) = remap[*output_index] {
                            *output_index = new_index;
                            true
                        } else {
                            false
                        }
                    },
                    FlowInputLocation::MemoryAddress {
                        ..
                    } => true,
                }),
                PartMapping::Register {
                    locations, ..
                } => locations.retain_mut(|location| match location {
                    FlowValueLocation::InputForOutput {
                        output_index, ..
                    } => {
                        if let Some(new_index) = remap[*output_index] {
                            *output_index = new_index;
                            true
                        } else {
                            false
                        }
                    },
                    FlowValueLocation::Output(output_index) => {
                        if let Some(new_index) = remap[*output_index] {
                            *output_index = new_index;
                            true
                        } else {
                            false
                        }
                    },
                    FlowValueLocation::MemoryAddress {
                        ..
                    } => true,
                }),
                PartMapping::MemoryComputation {
                    ..
                } => (),
            }
        }
    }

    /// Removes all dataflows that are always identity assignments. I.e., `A := A`.
    /// If a dataflow does not have a computation, it is not removed.
    /// This primarily occurs in flag outputs, because these are split after enumeration.
    pub fn remove_identity_assignments(mut self) -> Encoding<A, C> {
        info!("Removing identity assignments in: {self}");

        let mut remap = Vec::new();
        let mut index = 0;
        let mut new_index = 0;
        self.dataflows.outputs.retain(|output| {
            let result = output.inputs.len() != 1
                || output.inputs[0] != Source::Dest(output.target)
                || !output
                    .computation
                    .as_ref()
                    .map(|computation| computation.is_identity())
                    .unwrap_or(false)
                || self.parts.iter().any(|part| match &part.mapping {
                    PartMapping::Register {
                        locations, ..
                    } => {
                        let contains_output = locations.contains(&FlowValueLocation::Output(index));
                        let contains_input = locations.contains(&FlowValueLocation::InputForOutput {
                            output_index: index,
                            input_index: 0,
                        });

                        contains_input != contains_output
                    },
                    _ => false,
                });

            if !result {
                info!("Removing identity assignment {output:?}");
                remap.push(None);
            } else {
                remap.push(Some(new_index));
                new_index += 1;
            }

            index += 1;

            result
        });

        info!("Remapping output_indices: {remap:?}");

        self.update_remapped_output_indices(remap);

        info!("Removed identity assignments: {self}");

        self
    }
}

/// Error returned by [`Encoding::integrity_check`].
#[derive(Clone, Debug, thiserror::Error)]
pub enum IntegrityError {
    /// The output contains a reference to an immediate value of a non-existant part
    #[error("output {} contains a reference to an immediate value of a non-existant part", .output_index)]
    UnknownPartInOutputImm {
        /// The index of the output in the encoding
        output_index: usize,
    },

    /// The memory access contains a reference to an immediate value of a non-existant part.
    #[error("memory access {} contains a reference to an immediate value of a non-existant part", .memory_index)]
    UnknownPartInAddrImm {
        /// The index of the memory access in the encoding
        memory_index: usize,
    },

    /// Part has no valid mapping.
    #[error("part {} has no valid mapping", .part_index)]
    PartHasNoValidMapping {
        /// The index of the part in the encoding.
        part_index: usize,
    },

    /// The part mapping has a number of entries that is not equal to the number it should have.
    /// A part mapping should have `2**N` entries.
    #[error("the mapping of part {} ({} entries) does not match the part's size ({} bits)", .part_index, .mapping_entries, .part_bits)]
    MappingDoesNotMatchPartSize {
        /// The index of the part in the encoding.
        part_index: usize,

        /// The number of entries in the part
        mapping_entries: usize,

        /// The number of `Bit::Part(part_index)` bits in `encoding.bits`.
        part_bits: usize,
    },

    /// The part size does not correspond to the number of `Bit::Part(..)` bits in `self.bits`.
    #[error("the size of part {part_index} does not match the number of bits marked as BitKind::Part({part_index})", part_index = .part_index)]
    PartSizeDoesNotMatchBits {
        /// The index of the part in the encoding.
        part_index: usize,
    },
}

fn preview_pick_bit_value<T: Clone>(vec: &[T], good: impl Fn(&T) -> bool, bit_index: usize, bit_value: u8) -> (usize, usize) {
    let good_removed = vec
        .iter()
        .enumerate()
        .filter(|(index, _)| ((index >> bit_index) & 1) as u8 != bit_value)
        .filter(|(_, x)| good(x))
        .count();
    (good_removed, vec.len() / 2 - good_removed)
}

fn pick_bit_value<T: Clone>(vec: &[T], bit_index: usize, bit_value: u8) -> Vec<T> {
    vec.iter()
        .enumerate()
        .filter(|(index, _)| ((index >> bit_index) & 1) as u8 == bit_value)
        .map(|(_, x)| x.clone())
        .collect()
}

/// An error returned when instantiating an [`Encoding`] fails.
#[derive(Debug, Clone, thiserror::Error)]
pub enum InstantiationError {
    /// An invalid part value was passed, that doesn't map to any register.
    #[error("missing register mapping")]
    MissingRegisterMapping,

    /// An invalid part value was passed, that doesn't map to any memory computation
    #[error("missing memory computation mapping")]
    MissingMemoryComputationMapping,

    /// An invalid part value was passed, that doesn't map to any valid immediate value
    #[error("missing imm value mapping")]
    MissingImmValueMapping,
}

/// An error returned when [`Encoding::restrict_to`] fails.
#[derive(Debug, Clone, thiserror::Error)]
pub enum RestrictError {
    /// The provided filter does not overlap with the encoding.
    #[error("no overlap between restriction filter and encoding")]
    NoOverlap,
}

#[cfg(test)]
mod tests {
    use super::{ImmBitOrder, MappingOrBitOrder};
    use crate::arch::fake::*;
    use crate::arch::Arch;
    use crate::encoding::dataflows::{MemoryAccess, MemoryAccesses};
    use crate::encoding::{
        AccessKind, AddressComputation, Bit, Dataflow, Dataflows, Dest, Encoding, FlowInputLocation, FlowValueLocation, Inputs,
        Part, PartMapping, Size, Source,
    };
    use crate::instr::{Instruction, InstructionFilter};
    use crate::semantics::Computation;

    #[test_log::test]
    pub fn best_instr() {
        // Modelled after x86-64 instruction: C51CC6EFF8
        let instr = Instruction::new(&[0x07, 0x47]);
        let dataflows = Dataflows::<FakeArch, crate::encoding::AddressComputation> {
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
                    target: Dest::Reg(R1, Size::new(0, 0)),
                    inputs: Inputs::sorted(vec![Dest::Reg(R7, Size::new(0, 0)).into()]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
                Dataflow {
                    target: Dest::Reg(R1, Size::new(1, 1)),
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(1, 1)).into()]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
                Dataflow {
                    target: Dest::Reg(R1, Size::new(2, 2)),
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(2, 2)).into()]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
            ],
            found_dependent_bytes: false,
        };

        let encoding = Encoding {
            bits: vec![
                Bit::Part(0),
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Fixed(0),
                Bit::Part(2),
                Bit::Part(2),
                Bit::Part(2),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
            ],
            errors: std::iter::repeat(false).take(16).collect(),
            dataflows,
            parts: vec![
                Part {
                    size: 3,
                    value: 0b111,
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), None, Some(R2), Some(R3), Some(R4), Some(R5), Some(R6), Some(R7)],
                        locations: vec![FlowValueLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0,
                        }],
                    },
                },
                Part {
                    size: 3,
                    value: 0b100,
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R9), Some(R11), Some(R13), Some(R15), Some(R1), Some(R3), Some(R5), None],
                        locations: vec![
                            FlowValueLocation::Output(0),
                            FlowValueLocation::Output(1),
                            FlowValueLocation::Output(2),
                        ],
                    },
                },
                Part {
                    size: 3,
                    value: 0b111,
                    mapping: PartMapping::Register {
                        mapping: vec![
                            Some(R14),
                            Some(R12),
                            Some(R10),
                            Some(R8),
                            Some(R6),
                            Some(R4),
                            Some(R2),
                            Some(R0),
                        ],
                        locations: vec![
                            FlowValueLocation::InputForOutput {
                                output_index: 1,
                                input_index: 0,
                            },
                            FlowValueLocation::InputForOutput {
                                output_index: 2,
                                input_index: 0,
                            },
                        ],
                    },
                },
            ],
            write_ordering: Vec::new(),
        };

        println!("Encoding: {encoding}");

        let best_instr = encoding.best_instr().unwrap();
        let part_values = encoding.extract_parts(&best_instr);
        let instance = encoding.instantiate(&part_values).unwrap();
        println!("Best instance: {instance}");
        assert_eq!(best_instr, Instruction::new(&[0x01, 0x07]));
    }

    #[test_log::test]
    pub fn generate_filters1() {
        let instr = Instruction::new(&[0x01, 0xD0]);
        let dataflows = Dataflows::<FakeArch, crate::encoding::AddressComputation> {
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
                        Dest::Reg(R1, Size::new(0, 3)).into(),
                        Dest::Reg(R2, Size::new(0, 3)).into(),
                    ]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
                Dataflow {
                    target: Dest::Reg(R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(0, 5)).into()]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
                Dataflow {
                    target: Dest::Reg(RF, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Dest::Reg(R1, Size::new(0, 3)).into(),
                        Dest::Reg(R2, Size::new(0, 3)).into(),
                    ]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
            ],
            found_dependent_bytes: false,
        };

        let encoding = Encoding {
            bits: vec![
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Fixed(1),
                Bit::Fixed(1),
                Bit::Fixed(1),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
            ],
            errors: std::iter::repeat(false).take(16).collect(),
            dataflows,
            parts: vec![
                Part {
                    size: 3,
                    value: 0b000,
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3), None, Some(R5), Some(R6), Some(R8)],
                        locations: vec![
                            FlowValueLocation::Output(0),
                            FlowValueLocation::InputForOutput {
                                output_index: 0,
                                input_index: 0,
                            },
                            FlowValueLocation::InputForOutput {
                                output_index: 2,
                                input_index: 0,
                            },
                        ],
                    },
                },
                Part {
                    size: 3,
                    value: 0b010,
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3)],
                        locations: vec![
                            FlowValueLocation::InputForOutput {
                                output_index: 0,
                                input_index: 1,
                            },
                            FlowValueLocation::InputForOutput {
                                output_index: 2,
                                input_index: 1,
                            },
                        ],
                    },
                },
            ],
            write_ordering: Vec::new(),
        };

        println!("Encoding: {encoding}");

        let filters = encoding.filters();
        for filter in filters.iter() {
            println!("Filter: {filter:?}");
        }

        assert_eq!(
            filters,
            vec![
                InstructionFilter::parse("0000_001 11___0_1"),
                InstructionFilter::parse("0000_001 11___01_"),
                InstructionFilter::parse("00000001 11___0__"),
            ]
        );
    }

    #[test_log::test]
    pub fn generate_filters2() {
        let instr = Instruction::new(&[0x01, 0xD0]);
        let dataflows = Dataflows::<FakeArch, crate::encoding::AddressComputation> {
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
                        Dest::Reg(R1, Size::new(0, 3)).into(),
                        Dest::Reg(R2, Size::new(0, 3)).into(),
                    ]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
                Dataflow {
                    target: Dest::Reg(R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(0, 5)).into()]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
                Dataflow {
                    target: Dest::Reg(RF, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Dest::Reg(R1, Size::new(0, 3)).into(),
                        Dest::Reg(R2, Size::new(0, 3)).into(),
                    ]),
                    unobservable_external_inputs: false,
                    computation: None,
                },
            ],
            found_dependent_bytes: false,
        };

        let encoding = Encoding {
            bits: vec![
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Fixed(1),
                Bit::Fixed(1),
                Bit::Fixed(1),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
            ],
            errors: std::iter::repeat(false).take(16).collect(),
            dataflows,
            parts: vec![
                Part {
                    size: 3,
                    value: 0b000,
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3), None, Some(R5), Some(R6), Some(R8)],
                        locations: vec![
                            FlowValueLocation::Output(0),
                            FlowValueLocation::InputForOutput {
                                output_index: 0,
                                input_index: 0,
                            },
                            FlowValueLocation::InputForOutput {
                                output_index: 2,
                                input_index: 0,
                            },
                        ],
                    },
                },
                Part {
                    size: 3,
                    value: 0b010,
                    mapping: PartMapping::Register {
                        mapping: vec![Some(R0), Some(R1), Some(R2), Some(R3), None, Some(R5), Some(R6), Some(R8)],
                        locations: vec![
                            FlowValueLocation::InputForOutput {
                                output_index: 0,
                                input_index: 1,
                            },
                            FlowValueLocation::InputForOutput {
                                output_index: 2,
                                input_index: 1,
                            },
                        ],
                    },
                },
            ],
            write_ordering: Vec::new(),
        };

        println!("Encoding: {encoding}");

        let filters = encoding.filters();
        for filter in filters.iter() {
            println!("Filter: {filter:?}");
        }

        assert_eq!(
            filters,
            vec![
                InstructionFilter::parse("0000_001 11__10_1"),
                InstructionFilter::parse("0000_001 11__101_"),
                InstructionFilter::parse("00000001 11__10__"),
                InstructionFilter::parse("0000_001 11_1_0_1"),
                InstructionFilter::parse("0000_001 11_1_01_"),
                InstructionFilter::parse("00000001 11_1_0__"),
                InstructionFilter::parse("0000_001 110__0_1"),
                InstructionFilter::parse("0000_001 110__01_"),
                InstructionFilter::parse("00000001 110__0__"),
            ]
        );
    }

    fn e1() -> Encoding<FakeArch, AddressComputation> {
        let instr = Instruction::new(&[0x01, 0xD0]);
        Encoding {
            bits: vec![
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Part(1),
                Bit::Fixed(1),
                Bit::Fixed(1),
                Bit::Fixed(1),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Part(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
            ],
            errors: std::iter::repeat(false).take(16).collect(),
            dataflows: Dataflows::<FakeArch, crate::encoding::AddressComputation> {
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
                            Dest::Reg(R1, Size::new(0, 3)).into(),
                            Dest::Reg(R2, Size::new(0, 3)).into(),
                            Source::Imm(0),
                            Source::Imm(1),
                        ]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                    Dataflow {
                        target: Dest::Reg(RF, Size::new(0, 2)),
                        inputs: Inputs::sorted(vec![
                            Dest::Reg(R1, Size::new(0, 3)).into(),
                            Dest::Reg(R2, Size::new(0, 3)).into(),
                            Source::Imm(0),
                        ]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                    Dataflow {
                        target: Dest::Reg(R0, Size::qword()),
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::new(0, 5)).into(), Source::Imm(0)]),
                        unobservable_external_inputs: false,
                        computation: None,
                    },
                ],
                found_dependent_bytes: false,
            },
            parts: vec![
                Part {
                    size: 3,
                    value: 0b000,
                    mapping: PartMapping::Imm {
                        mapping: None,
                        locations: vec![
                            FlowInputLocation::InputForOutput {
                                output_index: 0,
                                input_index: 2,
                            },
                            FlowInputLocation::InputForOutput {
                                output_index: 1,
                                input_index: 2,
                            },
                            FlowInputLocation::InputForOutput {
                                output_index: 2,
                                input_index: 1,
                            },
                        ],
                        bits: None,
                    },
                },
                Part {
                    size: 3,
                    value: 0b010,
                    mapping: PartMapping::Imm {
                        mapping: None,
                        locations: vec![FlowInputLocation::InputForOutput {
                            output_index: 0,
                            input_index: 3,
                        }],
                        bits: None,
                    },
                },
            ],
            write_ordering: Vec::new(),
        }
    }

    fn e2() -> Encoding<FakeArch, ()> {
        Encoding::<FakeArch, ()> {
            bits: vec![
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
                Bit::Fixed(1),
                Bit::Fixed(0),
                Bit::Fixed(1),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(1),
                Bit::Fixed(1),
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
                    instr: Instruction::new(&[0xC5, 0x00, 0x00, 0x00, 0x00]),
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
        }
    }

    #[test]
    pub fn split_flags_output() {
        let mut encoding = e1();

        println!("Encoding: {encoding}");

        encoding.split_flag_output();

        println!("After split: {encoding}");

        assert_eq!(
            encoding,
            Encoding {
                bits: vec![
                    Bit::Part(0),
                    Bit::Part(0),
                    Bit::Fixed(0),
                    Bit::Part(1),
                    Bit::Part(1),
                    Bit::Part(1),
                    Bit::Fixed(1),
                    Bit::Fixed(1),
                    Bit::Fixed(1),
                    Bit::Fixed(0),
                    Bit::Fixed(0),
                    Bit::Part(0),
                    Bit::Fixed(0),
                    Bit::Fixed(0),
                    Bit::Fixed(0),
                    Bit::Fixed(0),
                ],
                errors: std::iter::repeat(false).take(16).collect(),
                dataflows: Dataflows::<FakeArch, crate::encoding::AddressComputation> {
                    addresses: MemoryAccesses {
                        instr: *encoding.instr(),
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
                            inputs: Inputs::unsorted(vec![
                                Dest::Reg(R1, Size::new(0, 3)).into(),
                                Dest::Reg(R2, Size::new(0, 3)).into(),
                                Source::Imm(0),
                                Source::Imm(1)
                            ]),
                            unobservable_external_inputs: false,
                            computation: None,
                        },
                        Dataflow {
                            target: Dest::Reg(R0, Size::qword()),
                            inputs: Inputs::unsorted(vec![Dest::Reg(R0, Size::new(0, 5)).into(), Source::Imm(0)]),
                            unobservable_external_inputs: false,
                            computation: None,
                        },
                        Dataflow {
                            target: Dest::Reg(RF, Size::new(0, 0)),
                            inputs: Inputs::unsorted(vec![
                                Dest::Reg(R1, Size::new(0, 3)).into(),
                                Dest::Reg(R2, Size::new(0, 3)).into(),
                                Source::Imm(0),
                                Source::Imm(1),
                                Dest::Reg(RF, Size::new(0, 0)).into()
                            ]),
                            unobservable_external_inputs: false,
                            computation: None,
                        },
                        Dataflow {
                            target: Dest::Reg(RF, Size::new(1, 1)),
                            inputs: Inputs::unsorted(vec![
                                Dest::Reg(R1, Size::new(0, 3)).into(),
                                Dest::Reg(R2, Size::new(0, 3)).into(),
                                Source::Imm(0),
                                Source::Imm(1),
                                Dest::Reg(RF, Size::new(1, 1)).into()
                            ]),
                            unobservable_external_inputs: false,
                            computation: None,
                        },
                        Dataflow {
                            target: Dest::Reg(RF, Size::new(2, 2)),
                            inputs: Inputs::unsorted(vec![
                                Dest::Reg(R1, Size::new(0, 3)).into(),
                                Dest::Reg(R2, Size::new(0, 3)).into(),
                                Source::Imm(0),
                                Source::Imm(1),
                                Dest::Reg(RF, Size::new(2, 2)).into()
                            ]),
                            unobservable_external_inputs: false,
                            computation: None,
                        },
                    ],
                    found_dependent_bytes: false,
                },
                parts: vec![
                    Part {
                        size: 3,
                        value: 0b000,
                        mapping: PartMapping::Imm {
                            mapping: None,
                            locations: vec![
                                FlowInputLocation::InputForOutput {
                                    output_index: 0,
                                    input_index: 2
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 1,
                                    input_index: 1
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 2,
                                    input_index: 2
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 3,
                                    input_index: 2
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 4,
                                    input_index: 2
                                },
                            ],
                            bits: None,
                        },
                    },
                    Part {
                        size: 3,
                        value: 0b010,
                        mapping: PartMapping::Imm {
                            mapping: None,
                            locations: vec![
                                FlowInputLocation::InputForOutput {
                                    output_index: 0,
                                    input_index: 3
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 2,
                                    input_index: 3
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 3,
                                    input_index: 3
                                },
                                FlowInputLocation::InputForOutput {
                                    output_index: 4,
                                    input_index: 3
                                },
                            ],
                            bits: None,
                        }
                    }
                ],
                write_ordering: Vec::new(),
            }
        )
    }

    #[test]
    pub fn instantiate_instr() {
        // 0000a001 11bbb0aa
        let e = e1();
        println!("{e}");
        assert_eq!(
            *e.instantiate(&[0b111, 0b100]).unwrap().instr(),
            Instruction::new(&[0b0000_1001, 0b1110_0011])
        );
        assert_eq!(
            *e.instantiate(&[0b000, 0b001]).unwrap().instr(),
            Instruction::new(&[0b0000_0001, 0b1100_1000])
        );

        // 00000000 aaaaaaaa aaaaaaaa aaaaaaaa aaaaaaaa
        let e = e2();
        println!("{e}");
        assert_eq!(
            *e.instantiate(&[0x1234_5678]).unwrap().instr(),
            Instruction::new(&[0xC5, 0x12, 0x34, 0x56, 0x78])
        );
    }

    fn assert_accesses_equal<A: Arch, C: Computation>(e: &Encoding<A, C>, other: &Encoding<A, C>, bits: &[usize]) {
        let instr = *e.instr();
        for val in 0..1u64 << bits.len() {
            let instr = {
                let mut x = instr;
                for (n, &bit_index) in bits.iter().enumerate() {
                    x.set_nth_bit_from_right(bit_index, (val >> n) as u8 & 1);
                }

                x
            };

            if e.filters().iter().any(|f| f.matches(&instr)) && other.filters().iter().any(|f| f.matches(&instr)) {
                let lhs_parts = e.extract_parts(&instr);
                let rhs_parts = other.extract_parts(&instr);
                let lhs = e.instantiate(&lhs_parts).unwrap();
                let rhs = other.instantiate(&rhs_parts).unwrap();

                for (lhs, rhs) in lhs.addresses.iter().zip(rhs.addresses.iter()) {
                    if lhs.has_fixed_addr() && rhs.has_fixed_addr() {
                        assert_eq!(
                            lhs.compute_fixed_addr(),
                            rhs.compute_fixed_addr(),
                            "For value=0b{val:b}, the dataflows differ: {lhs} vs {rhs}"
                        );
                    } else {
                        assert_eq!(lhs, rhs, "For value=0b{val:b}, the dataflows differ: {lhs} vs {rhs}");
                    }
                }
            }
        }
    }

    #[test]
    pub fn remove_bit_memory_bitorder() {
        let instr = Instruction::new(&[0xf0]);
        let base_calculation = AddressComputation::unscaled_sum(1).with_offset(15);
        let e = Encoding {
            bits: vec![
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Part(0),
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(1),
                Bit::Fixed(1),
            ],
            errors: std::iter::repeat(false).take(16).collect(),
            dataflows: Dataflows::<FakeArch, crate::encoding::AddressComputation> {
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
                            inputs: Inputs::unsorted(vec![Source::Imm(0)]),
                            size: 2..2,
                            calculation: base_calculation,
                            alignment: 1,
                        },
                    ],
                    use_trap_flag: false,
                },
                outputs: vec![],
                found_dependent_bytes: false,
            },
            parts: vec![Part {
                size: 3,
                value: 0b110,
                mapping: PartMapping::Imm {
                    mapping: Some(MappingOrBitOrder::BitOrder(vec![
                        ImmBitOrder::Positive(5),
                        ImmBitOrder::Positive(6),
                        ImmBitOrder::Negative(7),
                    ])),
                    locations: vec![FlowInputLocation::MemoryAddress {
                        memory_index: 1,
                        input_index: 0,
                    }],
                    bits: None,
                },
            }],
            write_ordering: Vec::new(),
        };

        println!("Before: {e}");

        // e = 11aaa000
        // e3= 11a1a000
        let mut e3 = e.clone();
        e3.make_bit_fixed(3).unwrap();

        println!("After: {e3}");

        assert_accesses_equal(&e, &e3, &[3, 4, 5]);
        assert_eq!(e3.dataflows.addresses.memory[1].calculation, base_calculation);

        // e = 11aaa000
        // e4= 11a1a000
        let mut e4 = e.clone();
        e4.make_bit_fixed(4).unwrap();

        println!("After: {e4}");

        assert_accesses_equal(&e, &e4, &[3, 4, 5]);
        assert_eq!(
            e4.dataflows.addresses.memory[1].calculation,
            base_calculation.with_added_offset(64)
        );

        // e = 11aaa000
        // e5= 111aa000
        let mut e5 = e.clone();
        e5.make_bit_fixed(5).unwrap();

        println!("After: {e5}");

        assert_accesses_equal(&e, &e5, &[3, 4, 5]);
        assert_eq!(
            e5.dataflows.addresses.memory[1].calculation,
            base_calculation.with_added_offset(-128)
        );
    }

    #[test]
    pub fn iter_instrs() {
        let e = Encoding {
            bits: vec![
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Fixed(0),
                Bit::Part(0),
                Bit::Part(0),
                Bit::Fixed(1),
                Bit::Fixed(1),
            ],
            errors: std::iter::repeat(false).take(16).collect(),
            dataflows: Dataflows::<FakeArch, crate::encoding::AddressComputation> {
                addresses: MemoryAccesses {
                    instr: Instruction::new(&[0x03]),
                    memory: vec![MemoryAccess {
                        kind: AccessKind::Executable,
                        inputs: Inputs::sorted(vec![Dest::Reg(R0, Size::qword()).into()]),
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
                mapping: PartMapping::Register {
                    mapping: vec![Some(R0), Some(R1), None, Some(R3)],
                    locations: vec![FlowValueLocation::MemoryAddress {
                        memory_index: 0,
                        input_index: 0,
                    }],
                },
            }],
            write_ordering: Vec::new(),
        };

        let instrs = e.iter_instrs(&[None], true).collect::<Vec<_>>();

        assert_eq!(
            instrs,
            vec![
                Instruction::new(&[0b0000_0011]),
                Instruction::new(&[0b0001_0011]),
                Instruction::new(&[0b0011_0011]),
            ]
        )
    }
}
