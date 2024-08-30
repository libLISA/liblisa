use std::collections::HashMap;
use std::ops::Not;

use itertools::Itertools;
use log::trace;

use crate::arch::{Arch, Register};
use crate::compare::{EncodingComparisonOptions, PartIndexMapping};
use crate::encoding::bitpattern::{Bit, FlowInputLocation, FlowValueLocation, ImmBit, Part, PartMapping};
use crate::encoding::dataflows::{Dataflow, Dest, Size, Source};
use crate::encoding::Encoding;
use crate::semantics::default::codegen::codegen_computation;
use crate::semantics::default::codegen::smt::Z3CodeGen;
use crate::semantics::default::computation::AsComputationRef;
use crate::semantics::{Computation, IoType, ARG_NAMES};
use crate::smt::{SatResult, SmtBV, SmtBool, SmtModel, SmtModelRef, SmtSolver};
use crate::state::Location;
use crate::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};
use crate::utils::EitherIter;
use crate::value::{AsValue, OwnedValue, ValueType};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FilledInput<A: Arch> {
    Concrete(Source<A>),
    Part(PartIndex, Option<Size>),
}

impl<A: Arch> FilledInput<A> {
    pub fn size(&self) -> Option<Size> {
        match self {
            FilledInput::Concrete(s) => s.size(),
            FilledInput::Part(_, size) => *size,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FilledOutput<A: Arch> {
    Concrete(Dest<A>),
    Part(PartIndex, Size),
}

impl<A: Arch> FilledOutput<A> {
    fn overlapping_area(&self, other: &FilledOutput<A>) -> Option<Size> {
        match (self, other) {
            (FilledOutput::Concrete(lhs), FilledOutput::Concrete(rhs)) => lhs.overlapping_area(rhs),
            (FilledOutput::Part(lhs_index, lhs_size), FilledOutput::Part(rhs_index, rhs_size)) if lhs_index == rhs_index => {
                lhs_size.overlapping_area(*rhs_size)
            },
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FilledLocation<A: Arch> {
    Concrete(Location<A>),
    Part(PartIndex),
}

impl<A: Arch> From<FilledInput<A>> for FilledLocation<A> {
    fn from(value: FilledInput<A>) -> Self {
        match value {
            FilledInput::Concrete(source) => FilledLocation::Concrete(Location::from(source.unwrap_dest())),
            FilledInput::Part(index, _) => FilledLocation::Part(index),
        }
    }
}

impl<A: Arch> From<FilledOutput<A>> for FilledLocation<A> {
    fn from(value: FilledOutput<A>) -> Self {
        match value {
            FilledOutput::Concrete(dest) => FilledLocation::Concrete(Location::from(dest)),
            FilledOutput::Part(index, _) => FilledLocation::Part(index),
        }
    }
}

/// Represents the equivalence between two encodings.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ComputationEquivalence {
    /// All computations are equal.
    Equal,

    /// No cases were found where computations were provably not equal, but at least one of the comparisons timed out.
    EqualOrTimeout,

    /// At least one computation is not equal.
    NotEqual,
}

#[derive(Debug)]
enum SolverResult<'ctx, S: SmtSolver<'ctx>> {
    Equal,
    EqualOrTimeout,
    NotEqual(Option<S::Model>),
}

struct LocationToBvMap<'ctx, A: Arch, S: SmtSolver<'ctx>> {
    map: HashMap<FilledLocation<A>, S::BV>,
    instr: S::BV,
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> LocationToBvMap<'ctx, A, S> {
    pub fn new(context: &mut S) -> Self {
        Self {
            map: HashMap::new(),
            instr: context.new_bv_const("instr", 128),
        }
    }

    pub fn get(&mut self, context: &mut S, key: FilledLocation<A>) -> S::BV {
        let mask = match key {
            FilledLocation::Concrete(Location::Reg(reg)) => reg.mask(),
            _ => None,
        };
        let bv = self
            .map
            .entry(key)
            .or_insert_with_key(|key: &FilledLocation<A>| context.new_bv_const(format!("{key:?}"), 256))
            .clone();
        if let Some(mask) = mask {
            bv & context.bv_from_u64(mask, 256)
        } else {
            bv
        }
    }

    pub fn get_raw(&mut self, context: &mut S, key: FilledLocation<A>) -> &S::BV {
        self.map
            .entry(key)
            .or_insert_with_key(|key: &FilledLocation<A>| context.new_bv_const(format!("{key:?}"), 256))
    }

    pub fn get_instr(&self) -> &S::BV {
        &self.instr
    }

    pub fn instr_bits(&self, bits: impl Iterator<Item = usize>) -> S::BV {
        bits.map(|index| self.instr.clone().extract(index as u32, index as u32))
            .reduce(|a, b| b.concat(a))
            .unwrap()
    }
}

struct PreparedComputation<'a, 'ctx, C, S: SmtSolver<'ctx>> {
    computation: &'a C,
    z3_inputs: Vec<S::BV>,
    part_assertions: Vec<S::Bool>,
    area: Size,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PartIndex {
    A(usize),
    B(usize),
    AB(usize),
}

impl PartIndex {
    pub fn new(mapping: &PartIndexMapping, index: usize, is_a: bool) -> PartIndex {
        if is_a {
            Self::from_a(mapping, index)
        } else {
            Self::from_b(mapping, index)
        }
    }

    pub fn from_a(mapping: &PartIndexMapping, index: usize) -> PartIndex {
        if mapping.try_a_dataflow_part_to_b(index).is_some() {
            PartIndex::AB(index)
        } else {
            PartIndex::A(index)
        }
    }

    pub fn from_b(mapping: &PartIndexMapping, index: usize) -> PartIndex {
        if let Some(a_index) = mapping.try_b_dataflow_part_to_a(index) {
            PartIndex::AB(a_index)
        } else {
            PartIndex::B(index)
        }
    }

    fn is_ab(&self) -> bool {
        matches!(self, PartIndex::AB(_))
    }
}

impl ComputationEquivalence {
    fn prepare_computation<'a, 'ctx, A: Arch, C, S: SmtSolver<'ctx>>(
        mapping: &PartIndexMapping, is_a: bool, encoding: &'a Encoding<A, C>, output_index: usize, area: Size, context: &mut S,
        location_to_bv: &mut LocationToBvMap<'ctx, A, S>,
    ) -> Option<PreparedComputation<'a, 'ctx, C, S>> {
        let flow = encoding.dataflows.output_dataflow(output_index);

        assert!(flow.target.size().contains(&area));

        let area_offset = flow.target.size().start_byte;
        let area = Size::new(area.start_byte - area_offset, area.end_byte - area_offset);
        let computation = flow.computation.as_ref()?;

        let part_assertions = encoding
            .parts
            .iter()
            .enumerate()
            .flat_map(|(part_index, part)| match &part.mapping {
                PartMapping::Register {
                    mapping: part_mapping, ..
                } => {
                    let bits = location_to_bv.instr_bits(
                        encoding
                            .bits
                            .iter()
                            .enumerate()
                            .filter(|(_, &bit)| bit == Bit::Part(part_index))
                            .map(|(index, _)| index),
                    );

                    let part_index = PartIndex::new(mapping, part_index, is_a);
                    if !part_index.is_ab() {
                        let location = FilledLocation::<A>::Part(part_index);

                        let part_val = location_to_bv.get_raw(context, location).clone();
                        EitherIter::Left(
                            part_mapping
                                .iter()
                                .enumerate()
                                .flat_map(|(index, mapping)| {
                                    mapping.as_ref().map(|&reg| {
                                        let concrete =
                                            location_to_bv.get_raw(context, FilledLocation::Concrete(Location::Reg(reg)));
                                        bits.clone()._eq(context.bv_from_u64(index as u64, part.size as u32)).not()
                                            | part_val.clone()._eq(concrete.clone())
                                    })
                                })
                                .collect::<Vec<_>>()
                                .into_iter(),
                        )
                    } else {
                        EitherIter::Right([].into_iter())
                    }
                },
                _ => EitherIter::Right([].into_iter()),
            })
            .collect::<Vec<_>>();

        // TODO: Use create_filled_inputs to skip the first part
        let z3_inputs = flow
            .inputs
            .iter()
            .enumerate()
            .map(|(input_index, input)| {
                let part_info = encoding.parts.iter().enumerate().find(|(_, part)| match &part.mapping {
                    PartMapping::Imm {
                        locations, ..
                    } => locations.contains(&FlowInputLocation::InputForOutput {
                        output_index,
                        input_index,
                    }),
                    PartMapping::Register {
                        locations, ..
                    } => locations.contains(&FlowValueLocation::InputForOutput {
                        output_index,
                        input_index,
                    }),
                    _ => false,
                });

                match part_info {
                    Some((
                        part_index,
                        Part {
                            mapping: PartMapping::Imm {
                                bits, ..
                            },
                            size,
                            ..
                        },
                    )) => {
                        let mut bv = location_to_bv
                            .instr_bits(
                                encoding
                                    .bits
                                    .iter()
                                    .enumerate()
                                    .filter(|&(_, &bit)| bit == Bit::Part(part_index))
                                    .map(|(index, _)| index),
                            )
                            .zero_ext(128 - *size as u32);
                        if let Some(bits) = bits {
                            let mut n = 0;
                            bv = bits
                                .iter()
                                .map(|bit| match bit {
                                    ImmBit::Is0 => context.bv_from_u64(0, 1),
                                    ImmBit::Is1 => context.bv_from_u64(1, 1),
                                    ImmBit::Fill => {
                                        let v = bv.clone().extract(n, n);
                                        n += 1;
                                        v
                                    },
                                })
                                .reduce(|a, b| b.concat(a))
                                .unwrap();

                            bv = bv.zero_ext(128 - bits.len() as u32);
                        }

                        bv
                    },
                    rest => {
                        let filled_input = match rest {
                            Some((part_index, _)) => FilledInput::Part(PartIndex::new(mapping, part_index, is_a), input.size()),
                            None => FilledInput::Concrete(*input),
                        };

                        match filled_input {
                            FilledInput::Concrete(Source::Imm(_)) => {
                                unreachable!("immediate should have been handled in other match-branch")
                            },
                            FilledInput::Concrete(Source::Const {
                                value, ..
                            }) => context.bv_from_u64(value, 128),
                            filled_input => {
                                let input_size = filled_input.size().unwrap_or(Size::new(0, 15));
                                let input_bit_size = input_size.num_bytes() as u32 * 8;

                                let key = FilledLocation::from(filled_input);
                                let mut bv = location_to_bv.get(context, key);
                                bv = bv.extract(input_size.end_byte as u32 * 8 + 7, input_size.start_byte as u32 * 8);

                                if let Source::Dest(dest) = input {
                                    if let ValueType::Bytes(_) = dest.value_type() {
                                        bv = bv.swap_bytes(input_size.num_bytes());
                                    }
                                }

                                if input_bit_size < 128 {
                                    bv = bv.zero_ext(128 - input_bit_size)
                                };

                                bv
                            },
                        }
                    },
                }
            })
            .collect::<Vec<_>>();

        Some(PreparedComputation {
            area,
            computation,
            z3_inputs,
            part_assertions,
        })
    }

    fn build_outputs<'a, A: Arch, C: Computation>(
        mapping: &'a PartIndexMapping, is_a: bool, encoding: &'a Encoding<A, C>,
    ) -> impl Iterator<Item = (FilledOutput<A>, (usize, &'a Dataflow<A, C>))> + 'a {
        encoding
            .dataflows
            .outputs
            .iter()
            .enumerate()
            .map(move |(output_index, flow)| {
                let target = encoding
                    .parts
                    .iter()
                    .enumerate()
                    .find(|(_, part)| match &part.mapping {
                        PartMapping::Register {
                            locations, ..
                        } => locations.contains(&FlowValueLocation::Output(output_index)),
                        _ => false,
                    })
                    .map(|(part_index, _)| FilledOutput::Part(PartIndex::new(mapping, part_index, is_a), flow.target.size()))
                    .unwrap_or_else(|| FilledOutput::Concrete(flow.target));
                (target, (output_index, flow))
            })
    }

    fn create_filled_inputs<A: Arch, C: Computation>(
        mapping: &PartIndexMapping, output_index: usize, encoding: &Encoding<A, C>, is_a: bool,
    ) -> Vec<FilledInput<A>> {
        encoding
            .dataflows
            .output_dataflow(output_index)
            .inputs
            .iter()
            .enumerate()
            .map(|(input_index, input)| {
                let part_info = encoding.parts.iter().enumerate().find(|(_, part)| match &part.mapping {
                    PartMapping::Imm {
                        locations, ..
                    } => locations.contains(&FlowInputLocation::InputForOutput {
                        output_index,
                        input_index,
                    }),
                    PartMapping::Register {
                        locations, ..
                    } => locations.contains(&FlowValueLocation::InputForOutput {
                        output_index,
                        input_index,
                    }),
                    _ => false,
                });

                match part_info {
                    Some((
                        part_index,
                        Part {
                            mapping: PartMapping::Imm {
                                ..
                            },
                            ..
                        },
                    )) => FilledInput::Concrete(Source::Imm(part_index)),
                    Some((part_index, _)) => FilledInput::Part(PartIndex::new(mapping, part_index, is_a), input.size()),
                    None => FilledInput::Concrete(*input),
                }
            })
            .collect()
    }

    // TODO: Does this actually improve performance?
    fn is_fast_equal<A: Arch, C: Computation + AsComputationRef>(
        mapping: &PartIndexMapping, a: &Encoding<A, C>, b: &Encoding<A, C>, output_index_a: usize, output_index_b: usize,
    ) -> bool {
        let flow_a = a.dataflows.output_dataflow(output_index_a);
        let flow_b = b.dataflows.output_dataflow(output_index_b);

        // Abort if we're not comparing identically-sized targets
        if flow_a.target().size() != flow_b.target().size() {
            return false
        }

        let a_inputs = Self::create_filled_inputs(mapping, output_index_a, a, true);
        let b_inputs = Self::create_filled_inputs(mapping, output_index_b, b, false);

        // Slow path if inputs aren't identical
        // TODO: Allow inputs to be in different order
        if a_inputs != b_inputs {
            trace!("Need slow path: input differences {a_inputs:?} {b_inputs:?}");
            return false
        }

        // Abort for anything that uses immediate values
        if a_inputs
            .iter()
            .any(|input| matches!(input, FilledInput::Concrete(Source::Imm(_))))
        {
            trace!("Need slow path: immediate values");
            return false
        }

        if let (Some(computation_a), Some(computation_b)) = (&flow_a.computation, &flow_b.computation) {
            // We return true if the computations are exactly identical
            // That is, the computations have the same operations, same input interpretations, same constants, and same output types
            let result = computation_a.as_internal() == computation_b.as_internal();
            trace!("Computation comparison result: {result:?}");
            result
        } else {
            false
        }
    }

    fn reconstruct_inputs_from_model<'ctx, A: Arch, C: Computation, S: SmtSolver<'ctx>>(
        mapping: &PartIndexMapping, output_index: usize, encoding: &Encoding<A, C>, is_a: bool,
        location_to_bv: &mut LocationToBvMap<'ctx, A, S>, context: &mut S, model: &S::Model,
    ) -> Vec<OwnedValue> {
        let flow = encoding.dataflows.output_dataflow(output_index);
        let mut inputs = Vec::new();
        for (input, loc) in flow
            .inputs
            .iter()
            .zip(Self::create_filled_inputs(mapping, output_index, encoding, is_a))
        {
            match input {
                Source::Dest(dest) => {
                    let size = dest.size();
                    let bv = location_to_bv.get_raw(context, FilledLocation::from(loc));
                    trace!("{input} -> {loc:?} -> {bv} with size {size:?}");
                    let bv = model.get_const_interp(bv).map(|bv| {
                        let bv = bv.extract(size.end_byte as u32 * 8 + 7, size.start_byte as u32 * 8);
                        bv.simplify()
                    });

                    trace!("Trying to set {dest} to {bv:?}");

                    inputs.push(match dest.value_type() {
                        ValueType::Num => OwnedValue::Num(bv.map(|bv| bv.as_u64().unwrap()).unwrap_or(0)),
                        ValueType::Bytes(n) => {
                            if n <= 8 {
                                let val = bv.map(|bv| bv.as_u64().unwrap()).unwrap_or(0);
                                OwnedValue::Bytes(val.to_le_bytes()[..n].to_vec())
                            } else {
                                let lo = bv
                                    .as_ref()
                                    .map(|bv| {
                                        bv.clone().extract(63, 0).simplify().as_u64().unwrap_or_else(|| {
                                            panic!("Unable to extract 63..0 from {bv} (dest={dest:?}, size={size:?})")
                                        })
                                    })
                                    .unwrap_or(0);
                                let hi = bv
                                    .map(|bv| bv.extract(n as u32 * 8 - 1, 64).simplify().as_u64().unwrap())
                                    .unwrap_or(0);
                                let val = lo as u128 | (hi as u128) << 64;
                                let bytes = val.to_le_bytes();

                                OwnedValue::Bytes(bytes[..n].to_vec())
                            }
                        },
                    });
                },
                Source::Const {
                    value, ..
                } => inputs.push(OwnedValue::Num(*value)),
                Source::Imm(part_index) => match &encoding.parts[*part_index].mapping {
                    PartMapping::Imm {
                        bits, ..
                    } => {
                        let instr = model.get_const_interp(location_to_bv.get_instr());
                        let part_value = encoding
                            .bits
                            .iter()
                            .enumerate()
                            .filter(|(_, &bit)| bit == Bit::Part(*part_index))
                            .enumerate()
                            .map(|(shift, (index, _))| {
                                instr
                                    .as_ref()
                                    .map(|instr| instr.clone().extract(index as u32, index as u32).simplify().as_u64().unwrap())
                                    .unwrap_or(0)
                                    << shift
                            })
                            .reduce(|a, b| a | b)
                            .unwrap();

                        let interpreted_value = bits
                            .as_ref()
                            .map(|bits| bits.interpret_value(part_value))
                            .unwrap_or(part_value);
                        trace!("Immediate value: 0x{part_value:X} -> {bits:?} -> 0x{interpreted_value:X}");

                        inputs.push(OwnedValue::Num(interpreted_value));
                    },
                    _ => unreachable!(),
                },
            }
        }
        inputs
    }

    /// Determines the equalvalence of two encodings.
    pub fn of<'ctx, A: Arch, C: Computation + PartialEq + AsComputationRef, S: SmtSolver<'ctx>>(
        mapping: &PartIndexMapping, options: &EncodingComparisonOptions, a: &Encoding<A, C>, b: &Encoding<A, C>, context: &mut S,
    ) -> ComputationEquivalence {
        // TODO: Add exclusion constraints for any imm parts that have exclusion entries in their mapping.

        trace!("Comparing outputs of: {a} vs {b}");
        let mut result = ComputationEquivalence::Equal;
        let a_outputs = Self::build_outputs(mapping, true, a);
        let mut b_outputs_by_location = {
            let mut m = HashMap::new();
            for (k, (output_index, flow)) in Self::build_outputs(mapping, false, b) {
                let mut map = FixedBitmapU64::<8>::new_all_zeros(512);
                map.set_many(flow.target.size().iter_byte_indices());

                let key = FilledLocation::from(k);

                m.entry(key).or_insert_with(Vec::new).push((k, (output_index, flow, map)));
            }

            m
        };

        for (target_a, (output_index_a, flow_a)) in a_outputs {
            let mut unseen_a = FixedBitmapU64::<8>::new_all_zeros(512);
            unseen_a.set_many(flow_a.target.size().iter_byte_indices());

            if skip_because_of_write_ordering(a, output_index_a) {
                continue
            }

            let key = FilledLocation::from(target_a);
            if let Some(b_outputs) = b_outputs_by_location.get_mut(&key) {
                for (target_b, (output_index_b, _, unseen_b)) in b_outputs.iter_mut() {
                    if let Some(area) = target_a.overlapping_area(target_b) {
                        trace!("Comparing {target_a:?} vs {target_b:?}");
                        unseen_a.clear_many(area.iter_byte_indices());
                        unseen_b.clear_many(area.iter_byte_indices());

                        if skip_because_of_write_ordering(b, *output_index_b) {
                            continue
                        }

                        if Self::is_fast_equal(mapping, a, b, output_index_a, *output_index_b) {
                            continue
                        }
                        let mut location_to_bv = LocationToBvMap::new(context);

                        let prepared_a =
                            Self::prepare_computation(mapping, true, a, output_index_a, area, context, &mut location_to_bv);
                        let prepared_b =
                            Self::prepare_computation(mapping, false, b, *output_index_b, area, context, &mut location_to_bv);

                        match (prepared_a, prepared_b) {
                            (None, None) => (),
                            (None, Some(_)) | (Some(_), None) => {
                                if !options.treat_missing_as_equal {
                                    trace!("Computation missing for target {target_a:?}");
                                    return ComputationEquivalence::NotEqual
                                }
                            },
                            (Some(prepared_a), Some(prepared_b)) => {
                                match Self::check_computations_equivalent(&prepared_a, &prepared_b, context) {
                                    SolverResult::Equal => (),
                                    SolverResult::EqualOrTimeout => result = ComputationEquivalence::EqualOrTimeout,
                                    SolverResult::NotEqual(model) => {
                                        if let Some(model) = model {
                                            let inputs_a = Self::reconstruct_inputs_from_model(
                                                mapping,
                                                output_index_a,
                                                a,
                                                true,
                                                &mut location_to_bv,
                                                context,
                                                &model,
                                            );
                                            let inputs_b = Self::reconstruct_inputs_from_model(
                                                mapping,
                                                *output_index_b,
                                                b,
                                                false,
                                                &mut location_to_bv,
                                                context,
                                                &model,
                                            );

                                            trace!("Reconstructed a_inputs: {inputs_a:02X?}");
                                            trace!("Reconstructed b_inputs: {inputs_b:02X?}");

                                            let result_a = prepared_a.computation.evaluate(&inputs_a);
                                            trace!("Result for computation a: {result_a:X?}");

                                            let result_b = prepared_b.computation.evaluate(&inputs_b);
                                            trace!("Result for computation b: {result_b:X?}");

                                            let result_a = result_a.as_value().slice(prepared_a.area);
                                            let result_b = result_b.as_value().slice(prepared_b.area);

                                            trace!("Sliced results: {result_a:X?} vs {result_b:X?}");

                                            trace!(
                                                "Arg interpretations: {:?} vs {:?}",
                                                prepared_a.computation.arg_interpretation(),
                                                prepared_b.computation.arg_interpretation()
                                            );

                                            assert!(
                                                result_a != result_b,
                                                "Z3 translation is incorrect: {target_a:?} / {target_b:?} in {a} / {b}\n\n\nmodel={model:?}\n\ninputs_a={inputs_a:02X?}\ninputs_b={inputs_b:02X?}\nresult_a={result_a:02X?}\nresult_b={result_b:02X?}"
                                            );
                                        }

                                        return ComputationEquivalence::NotEqual
                                    },
                                }
                            },
                        }
                    }
                }
            }

            // Check if all the outputs we could not find in b were identity assignments in a
            if !unseen_a.is_all_zeros() {
                trace!(
                    "Missing from b: {target_a:?} bytes [{:?}]",
                    unseen_a.iter_one_indices().format(", ")
                );
                for index in unseen_a.iter_one_indices() {
                    let area = Size::new(index, index);
                    let mut location_to_bv = LocationToBvMap::new(context);
                    if let Some(prepared) =
                        Self::prepare_computation(mapping, false, a, output_index_a, area, context, &mut location_to_bv)
                    {
                        let original = location_to_bv.get(context, FilledLocation::from(target_a));
                        match Self::check_computation_is_identity_assingment(prepared, context, original.clone(), area) {
                            ComputationEquivalence::Equal => (),
                            ComputationEquivalence::EqualOrTimeout => result = ComputationEquivalence::EqualOrTimeout,
                            ComputationEquivalence::NotEqual => return ComputationEquivalence::NotEqual,
                        }
                    } else {
                        let flow = a.dataflows.output_dataflow(output_index_a);
                        let could_be_identity = flow.inputs.iter().any(|&input| input == Source::Dest(flow.target));

                        if !could_be_identity {
                            return ComputationEquivalence::NotEqual
                        }
                    }
                }
            }
        }

        // Check if all the outputs we could not find in a were identity assignments in b
        for b_outputs in b_outputs_by_location.into_values() {
            for (target_b, (output_index_b, _, unseen_b)) in b_outputs.into_iter() {
                if !unseen_b.is_all_zeros() {
                    trace!(
                        "Output in b did not appear in a: {:?} bytes {:?}",
                        target_b,
                        unseen_b.iter_one_indices().format(", ")
                    );

                    for index in unseen_b.iter_one_indices() {
                        let area = Size::new(index, index);
                        let mut location_to_bv = LocationToBvMap::new(context);
                        if let Some(prepared) =
                            Self::prepare_computation(mapping, false, b, output_index_b, area, context, &mut location_to_bv)
                        {
                            let original = location_to_bv.get(context, FilledLocation::from(target_b));
                            match Self::check_computation_is_identity_assingment(prepared, context, original.clone(), area) {
                                ComputationEquivalence::Equal => (),
                                ComputationEquivalence::EqualOrTimeout => result = ComputationEquivalence::EqualOrTimeout,
                                ComputationEquivalence::NotEqual => return ComputationEquivalence::NotEqual,
                            }
                        } else {
                            let flow = b.dataflows.output_dataflow(output_index_b);
                            let could_be_identity = flow.inputs.iter().any(|&input| input == Source::Dest(flow.target));

                            if !could_be_identity {
                                return ComputationEquivalence::NotEqual
                            }
                        }
                    }
                }
            }
        }

        trace!("Output comparison result: {result:?}");

        result
    }

    fn check_computations_equivalent<'a, 'ctx, C: Computation + PartialEq + AsComputationRef, S: SmtSolver<'ctx>>(
        a: &PreparedComputation<'a, 'ctx, C, S>, b: &PreparedComputation<'a, 'ctx, C, S>, context: &'a mut S,
    ) -> SolverResult<'ctx, S> {
        trace!(
            "Comparing: {{ {} }} == {{ {} }}",
            a.computation.display(ARG_NAMES),
            b.computation.display(ARG_NAMES)
        );

        let a_area = match a.computation.as_internal().output_type() {
            IoType::Integer {
                ..
            } => a.area,
            IoType::Bytes {
                num_bytes,
            } => Size::new(num_bytes - 1 - a.area.end_byte, num_bytes - 1 - a.area.start_byte),
        };

        let b_area = match b.computation.as_internal().output_type() {
            IoType::Integer {
                ..
            } => b.area,
            IoType::Bytes {
                num_bytes,
            } => Size::new(num_bytes - 1 - b.area.end_byte, num_bytes - 1 - b.area.start_byte),
        };

        trace!("Accounting for output types, areas are a={a_area:?}, b={b_area:?}");
        // TODO: Fast path: If computations and inputs are equivalent, return equivalent

        let mut g_a = Z3CodeGen::<S>::new(context, a.z3_inputs.clone());
        let smt_a = codegen_computation(&mut g_a, a.computation);
        let mut g_b = Z3CodeGen::<S>::new(context, b.z3_inputs.clone());
        let smt_b = codegen_computation(&mut g_b, b.computation);
        let smt_a = smt_a.as_bv();
        let smt_b = smt_b.as_bv();
        let target_byte_size = a.area.num_bytes();
        assert_eq!(target_byte_size, b.area.num_bytes());

        let smt_a = smt_a
            .clone()
            .extract(a_area.end_byte as u32 * 8 + 7, a_area.start_byte as u32 * 8);
        let smt_b = smt_b
            .clone()
            .extract(b_area.end_byte as u32 * 8 + 7, b_area.start_byte as u32 * 8);
        let condition = smt_a.clone()._eq(smt_b.clone()).not();

        let mut assertions = Vec::new();

        for assertion in a.part_assertions.iter().chain(b.part_assertions.iter()) {
            assertions.push(assertion.clone());
        }

        assertions.push(condition.clone());
        assertions.push(smt_a.clone()._eq(context.new_bv_const("lhs", a.area.num_bytes() as u32 * 8)));
        assertions.push(smt_b.clone()._eq(context.new_bv_const("rhs", b.area.num_bytes() as u32 * 8)));
        let result = match context.check_assertions(&assertions) {
            SatResult::Unsat => {
                trace!(
                    "Equivalent: {{ {} }} == {{ {} }}",
                    a.computation.display(ARG_NAMES),
                    b.computation.display(ARG_NAMES)
                );
                SolverResult::Equal
            },
            SatResult::Unknown => {
                trace!(
                    "Unable to prove equivalence between {} and {}",
                    a.computation.display(ARG_NAMES),
                    b.computation.display(ARG_NAMES)
                );
                trace!("Condition: {}", condition.simplify());
                SolverResult::EqualOrTimeout
            },
            SatResult::Sat(model_ref) => {
                trace!(
                    "Computations not equivalent: {} ({:?}) vs {} ({:?})",
                    a.computation.display(ARG_NAMES),
                    a.area,
                    b.computation.display(ARG_NAMES),
                    b.area
                );
                trace!(
                    "Output types: {:?} vs {:?}",
                    a.computation.as_internal().output_encoding(),
                    b.computation.as_internal().output_encoding()
                );
                trace!("SimplifiedLhs: {}; SimplifiedRhs: {}", smt_a.simplify(), smt_b.simplify());
                trace!("Model: {model_ref:?}");
                let model = model_ref.to_model();

                SolverResult::NotEqual(model)
            },
        };

        result
    }

    fn check_computation_is_identity_assingment<'ctx, C: Computation + PartialEq + AsComputationRef, S: SmtSolver<'ctx>>(
        prep: PreparedComputation<'_, 'ctx, C, S>, context: &mut S, original: S::BV, original_area: Size,
    ) -> ComputationEquivalence {
        let mut g_a = Z3CodeGen::new(context, prep.z3_inputs);
        let smt_a = codegen_computation(&mut g_a, prep.computation);
        let smt_a = smt_a.as_bv();

        let a_area = match prep.computation.as_internal().output_type() {
            IoType::Integer {
                ..
            } => prep.area,
            IoType::Bytes {
                num_bytes,
            } => Size::new(num_bytes - 1 - prep.area.end_byte, num_bytes - 1 - prep.area.start_byte),
        };

        let smt_a = smt_a
            .clone()
            .extract(a_area.end_byte as u32 * 8 + 7, a_area.start_byte as u32 * 8);
        let smt_b = original.extract(original_area.end_byte as u32 * 8 + 7, original_area.start_byte as u32 * 8);

        let condition = smt_a._eq(smt_b).not();

        // trace!("Checking: {condition}");
        let mut assertions = Vec::new();

        for assertion in prep.part_assertions.iter() {
            assertions.push(assertion.clone());
        }

        assertions.push(condition.clone());
        let result = match context.check_assertions(&assertions) {
            SatResult::Unsat => {
                trace!("Identity assignment proven: {{ {} }}", prep.computation.display(ARG_NAMES));
                ComputationEquivalence::Equal
            },
            SatResult::Unknown => {
                trace!(
                    "Unable to prove that the computation is an identity assignment: {}",
                    prep.computation.display(ARG_NAMES)
                );
                ComputationEquivalence::EqualOrTimeout
            },
            SatResult::Sat(model_ref) => {
                trace!(
                    "Computation is not the identity assignment: {}",
                    prep.computation.display(ARG_NAMES)
                );
                trace!("Condition: {}", condition.simplify());
                trace!("Model: {model_ref:?}");

                ComputationEquivalence::NotEqual
            },
        };

        result
    }
}

fn skip_because_of_write_ordering<A: Arch, C: Computation>(encoding: &Encoding<A, C>, output_index: usize) -> bool {
    let target = encoding.dataflows.output_dataflow(output_index).target();
    encoding.write_ordering.iter()
        .any(|wo|
            wo.part_values.iter().all(Option::is_none)
                && wo.output_index_order.iter()
                .skip_while(|&&index| index != output_index)
                .skip(1)
                .any(|&overwrite_index| {
                    let other_target = encoding.dataflows.output_dataflow(overwrite_index).target();
                    if other_target.overlaps(target) {
                        trace!("Output index {overwrite_index} supersedes current output {output_index} (target {target:?}) in {encoding}");
                        assert!(other_target.contains(target), "TODO: Non-covering output {other_target:?} will overwrite part of {target:?}: output {output_index} (target {target:?}) in {encoding}");
                        true
                    } else {
                        false
                    }
                })
        )
}
