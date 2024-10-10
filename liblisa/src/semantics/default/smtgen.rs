//! Provides [`Z3Model`] and [`ConcreteZ3Model`], SMT models that can be generated for uninstantiated encodings.
//!
//! [`Z3Model`] uses part indices in its representation,
//! while [`ConcreteZ3Model`] uses a bitvector representation of the instruction to translate part mappings into SMT expressions.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

use log::{debug, trace};

use crate::arch::{Arch, Register};
use crate::encoding::bitpattern::{Bit, FlowInputLocation, FlowValueLocation, ImmBit, ImmBits, Part, PartMapping, PART_NAMES};
use crate::encoding::dataflows::{Dataflow, Dest, Size, Source};
use crate::encoding::Encoding;
use crate::semantics::default::codegen::codegen_computation;
use crate::semantics::default::codegen::smt::Z3CodeGen;
use crate::semantics::default::computation::AsComputationRef;
use crate::semantics::Computation;
use crate::smt::{SmtBV, SmtBool, SmtSolver};
use crate::state::{Location, SplitDests};
use crate::utils::bitmap::{BitmapSlice, GrowingBitmap};
use crate::utils::EitherIter;
use crate::value::ValueType;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum FilledInput<A: Arch> {
    Concrete(Source<A>),
    Part {
        part_index: PartIndex,
        size: Option<Size>,
        is_bytes: bool,
    },
}

impl<A: Arch> FilledInput<A> {
    pub fn size(&self) -> Option<Size> {
        match self {
            FilledInput::Concrete(s) => s.size(),
            FilledInput::Part {
                size, ..
            } => *size,
        }
    }

    fn is_bytes(&self) -> bool {
        match self {
            FilledInput::Concrete(Source::Dest(dest)) => matches!(dest.value_type(), ValueType::Bytes(_)),
            FilledInput::Part {
                is_bytes, ..
            } => *is_bytes,
            _ => false,
        }
    }
}

/// An output, which might be a concrete [`Dest`] or a target that depends on a part in the instruction bitstring.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FilledOutput<A: Arch> {
    /// A destination that is not influenced by a part value.
    Concrete(Dest<A>),

    /// A destination whose target depends on the value of a part.
    Part(PartIndex, Size),
}

impl<A: Arch> FilledOutput<A> {
    fn size(&self) -> Size {
        match self {
            FilledOutput::Concrete(dest) => dest.size(),
            FilledOutput::Part(_, size) => *size,
        }
    }
}

/// A storage location, which might be a concrete [`Location`] or a location that depends on a part in the instruction bitstring.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FilledLocation<A: Arch> {
    /// A location that is not influenced by a part value.
    Concrete(Location<A>),

    /// A location whose target depends on the value of a part.
    Part(PartIndex),
}

impl<A: Arch> FilledLocation<A> {
    fn bit_size(&self, sizes: &Sizes) -> u32 {
        match self {
            FilledLocation::Concrete(Location::Reg(reg)) => reg.byte_size() as u32 * 8,
            FilledLocation::Concrete(Location::Memory(_)) => 256,
            FilledLocation::Part(part_index) => sizes.part_sizes[part_index.0] as u32,
        }
    }
}

impl<A: Arch> From<FilledInput<A>> for FilledLocation<A> {
    fn from(value: FilledInput<A>) -> Self {
        match value {
            FilledInput::Concrete(source) => FilledLocation::Concrete(Location::from(source.unwrap_dest())),
            FilledInput::Part {
                part_index, ..
            } => FilledLocation::Part(part_index),
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

/// A container that maps storage locations to SMT solver bitvectors.
pub struct StorageLocations<'ctx, A: Arch, S: SmtSolver<'ctx>> {
    map: HashMap<FilledLocation<A>, S::BV>,
    instr: S::BV,
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> StorageLocations<'ctx, A, S> {
    /// Creates a new, empty mapping.
    pub fn new(context: &mut S) -> Self {
        Self {
            map: HashMap::new(),
            instr: context.new_bv_const("instr", 128),
        }
    }

    fn name(key: &FilledLocation<A>) -> String {
        match key {
            FilledLocation::Concrete(Location::Reg(reg)) => format!("r{reg}"),
            FilledLocation::Concrete(Location::Memory(memory_index)) => format!("m{memory_index}"),
            FilledLocation::Part(part_index) => format!("part{}", PART_NAMES[part_index.0].to_uppercase()),
        }
    }

    /// Retrieves the mapping for the provided location `key`.
    /// If the location has no mapping, a new SMT bitvector constant is created.
    /// If the register is a zero register, a bitvector with value 0 is returned.
    ///
    /// Masks the result by the mask of the location.
    ///
    /// # Problems
    /// This function returns the raw bitvector value of the location.
    /// For byte values ([`ValueType::Bytes`]), this causes an inconsistency:
    /// The values are not stored in the same order as the output of computations.
    /// So a simple assertion of `input_bv == output_bv` would fail.
    ///
    /// You should use the function [`StorageLocations::get_sized`] instead, which automatically performs this byte swapping when needed.
    #[deprecated = "use StorageLocatinos::get_sized instead"]
    pub fn get(&mut self, context: &mut S, key: FilledLocation<A>, sizes: &Sizes) -> S::BV {
        self.get_internal(context, key, sizes)
    }

    fn get_internal(&mut self, context: &mut S, key: FilledLocation<A>, sizes: &Sizes) -> S::BV {
        match key {
            FilledLocation::Concrete(Location::Reg(reg)) if reg.is_zero() => {
                return context.bv_from_u64(0, reg.byte_size() as u32 * 8)
            },
            _ => (),
        }

        let mask = match key {
            FilledLocation::Concrete(Location::Reg(reg)) => reg.mask(),
            _ => None,
        };
        let bv = self
            .map
            .entry(key)
            .or_insert_with_key(|key: &FilledLocation<A>| context.new_bv_const(Self::name(key), key.bit_size(sizes)))
            .clone();
        if let Some(mask) = mask {
            bv & context.bv_from_u64(mask, key.bit_size(sizes))
        } else {
            bv
        }
    }

    /// Retrieves the mapping for the provided location `key`.
    /// If the location has no mapping, a new SMT bitvector constant is created.
    /// If the register is a zero register, a bitvector with value 0 is returned.
    ///
    /// Crops the result to the provided `input_size`.
    pub fn get_sized(
        &mut self, context: &mut S, key: FilledLocation<A>, sizes: &Sizes, input_size: Size, is_bytes: bool,
    ) -> S::BV {
        let mut bv = self.get_internal(context, key, sizes);
        bv = bv.extract(input_size.end_byte as u32 * 8 + 7, input_size.start_byte as u32 * 8);

        if is_bytes {
            bv = bv.swap_bytes(input_size.num_bytes());
        }

        bv
    }

    /// Retrieves the mapping for the provided location `key`.
    /// If the location has no mapping, a new SMT bitvector constant is created.
    /// If the register is a zero register, a bitvector with value 0 is returned.
    ///
    /// Does not mask or crop the result in any way.
    pub fn get_raw(&mut self, context: &mut S, key: FilledLocation<A>, sizes: &Sizes) -> S::BV {
        match key {
            FilledLocation::Concrete(Location::Reg(reg)) if reg.is_zero() => {
                return context.bv_from_u64(0, reg.byte_size() as u32 * 8)
            },
            _ => (),
        }

        self.map
            .entry(key)
            .or_insert_with_key(|key: &FilledLocation<A>| context.new_bv_const(Self::name(key), key.bit_size(sizes)))
            .clone()
    }

    /// Returns the bitvector constant representing the instruction bitstring.
    pub fn get_instr(&self) -> &S::BV {
        &self.instr
    }

    /// Returns a bitvector constructed of the bits in the instruction bitvector at the bit indices in `bits`.
    pub fn instr_bits(&self, bits: impl Iterator<Item = usize>) -> S::BV {
        bits.map(|index| self.instr.clone().extract(index as u32, index as u32))
            .reduce(|a, b| b.concat(a))
            .unwrap()
    }

    /// Iterates over all locations in this container
    pub fn iter(&self) -> impl Iterator<Item = (&FilledLocation<A>, &S::BV)> {
        self.map.iter()
    }
}

#[derive(Clone, Debug)]
struct PreparedComputation<'a, 'ctx, C, S: SmtSolver<'ctx>> {
    computation: &'a C,
    z3_inputs: Vec<S::BV>,
    part_assertions: Vec<S::Bool>,
}

/// The bit sizes of the parts in an encoding.
#[derive(Default)]
pub struct Sizes {
    part_sizes: Vec<usize>,
}

impl Sizes {
    /// Extracts the part sizes from the encoding.
    pub fn from_encoding<C, A: Arch>(encoding: &Encoding<A, C>) -> Sizes {
        Sizes {
            part_sizes: encoding
                .parts
                .iter()
                .map(|part| match &part.mapping {
                    PartMapping::Imm {
                        ..
                    } => part.size,
                    PartMapping::MemoryComputation {
                        ..
                    } => 0,
                    PartMapping::Register {
                        mapping, ..
                    } => {
                        let sizes = mapping.iter().flatten().map(|reg| reg.byte_size()).collect::<Vec<_>>();

                        assert!(sizes.windows(2).all(|x| x[0] == x[1]));

                        sizes[0] * 8
                    },
                })
                .collect(),
        }
    }
}

impl<'a, 'ctx, C, S: SmtSolver<'ctx>> PreparedComputation<'a, 'ctx, C, S> {
    fn create_part_assertions<A: Arch>(
        context: &mut S, encoding: &'a Encoding<A, C>, location_to_bv: &mut StorageLocations<'ctx, A, S>, sizes: &Sizes,
    ) -> Vec<S::Bool> {
        encoding
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

                    let part_index = PartIndex(part_index);
                    let location = FilledLocation::<A>::Part(part_index);

                    let part_val = location_to_bv.get_raw(context, location, sizes).clone();
                    EitherIter::Left(
                        part_mapping
                            .iter()
                            .enumerate()
                            .flat_map(|(index, mapping)| {
                                mapping.as_ref().map(|&reg| {
                                    let concrete =
                                        location_to_bv.get_raw(context, FilledLocation::Concrete(Location::Reg(reg)), sizes);
                                    !bits.clone()._eq(context.bv_from_u64(index as u64, part.size as u32))
                                        | part_val.clone()._eq(concrete.clone())
                                })
                            })
                            .collect::<Vec<_>>()
                            .into_iter(),
                    )
                },
                _ => EitherIter::Right([].into_iter()),
            })
            .collect::<Vec<_>>()
    }

    fn filled_inputs<A: Arch>(output_index: usize, encoding: &Encoding<A, C>) -> impl Iterator<Item = FilledInput<A>> + '_ {
        encoding
            .dataflows
            .output_dataflow(output_index)
            .inputs
            .iter()
            .enumerate()
            .map(move |(input_index, input)| {
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
                    Some((part_index, _)) => FilledInput::Part {
                        part_index: PartIndex(part_index),
                        size: input.size(),
                        is_bytes: match input {
                            Source::Dest(dest) => matches!(dest.value_type(), ValueType::Bytes(_)),
                            _ => false,
                        },
                    },
                    None => FilledInput::Concrete(*input),
                }
            })
    }

    fn create_imm<A: Arch>(
        context: &mut S, location_to_bv: &mut StorageLocations<'ctx, A, S>, encoding: &'a Encoding<A, C>, part_index: usize,
        size: usize, bits: &'a Option<ImmBits>,
    ) -> S::BV {
        let mut bv = location_to_bv
            .instr_bits(encoding.part_bit_indices(part_index))
            .zero_ext(128 - size as u32);
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
    }

    fn create_normal<A: Arch>(
        context: &mut S, filled_input: FilledInput<A>, location_to_bv: &mut StorageLocations<'ctx, A, S>, sizes: &Sizes,
    ) -> S::BV {
        match filled_input {
            FilledInput::Concrete(Source::Imm(_)) => unreachable!("immediate should have been handled in other match-branch"),
            FilledInput::Concrete(Source::Const {
                value, ..
            }) => context.bv_from_u64(value, 128),
            filled_input => {
                let input_size = filled_input.size().unwrap_or(Size::new(0, 15));
                let input_bit_size = input_size.num_bytes() as u32 * 8;

                let key = FilledLocation::from(filled_input);
                let mut bv = location_to_bv.get_sized(context, key, sizes, input_size, filled_input.is_bytes());

                if input_bit_size < 128 {
                    bv = bv.zero_ext(128 - input_bit_size)
                }

                bv
            },
        }
    }

    pub fn prepare<A: Arch>(
        encoding: &'a Encoding<A, C>, output_index: usize, storage_locations: &mut StorageLocations<'ctx, A, S>, context: &mut S,
    ) -> Option<PreparedComputation<'a, 'ctx, C, S>> {
        let sizes = Sizes::from_encoding(encoding);
        let flow = encoding.dataflows.output_dataflow(output_index);
        let computation = flow.computation.as_ref()?;

        // TODO: Use create_filled_inputs to skip the first part
        let z3_inputs = Self::filled_inputs(output_index, encoding)
            .map(|filled_input| {
                if let FilledInput::Concrete(Source::Imm(part_index)) = filled_input {
                    if let Part {
                        mapping: PartMapping::Imm {
                            bits, ..
                        },
                        size,
                        ..
                    } = &encoding.parts[part_index]
                    {
                        Self::create_imm(context, storage_locations, encoding, part_index, *size, bits)
                    } else {
                        Self::create_normal(context, filled_input, storage_locations, &sizes)
                    }
                } else {
                    Self::create_normal(context, filled_input, storage_locations, &sizes)
                }
            })
            .collect::<Vec<_>>();

        Some(PreparedComputation {
            computation,
            z3_inputs,
            part_assertions: Self::create_part_assertions(context, encoding, storage_locations, &sizes),
        })
    }
}

/// The index of a part in an encoding.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PartIndex(usize);

/// The output of a dataflow, which might still depend on the value of a part.
#[derive(Clone, Debug)]
pub struct IntermediateOutput<'ctx, A: Arch, S: SmtSolver<'ctx>> {
    target: FilledOutput<A>,
    name: S::BV,
    smt: Option<S::BV>,
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> IntermediateOutput<'ctx, A, S> {
    /// Returns the SMT expression for this output.
    pub fn smt(&self) -> Option<&S::BV> {
        self.smt.as_ref()
    }

    /// Returns the target location of the output.
    pub fn target(&self) -> FilledOutput<A> {
        self.target
    }

    /// Returns the SMT bitvector constant of the output.
    pub fn name(&self) -> &S::BV {
        &self.name
    }
}

/// An SMT computation for a concrete output of an encoding.
#[derive(Clone)]
pub struct ConcreteOutput<'ctx, A: Arch, S: SmtSolver<'ctx>> {
    target: Dest<A>,
    smt: Option<S::BV>,
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> Debug for ConcreteOutput<'ctx, A, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConcreteOutput")
            .field("target", &self.target)
            .field("smt", &self.smt)
            .finish()
    }
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> ConcreteOutput<'ctx, A, S> {
    /// Returns the target of the output.
    pub fn target(&self) -> Dest<A> {
        self.target
    }

    /// Returns the SMT expression for this output.
    pub fn smt(&self) -> Option<&S::BV> {
        self.smt.as_ref()
    }
}

/// The name of a part
#[derive(Clone, Debug)]
pub struct PartName<'ctx, S: SmtSolver<'ctx>> {
    name: S::BV,
    smt: S::BV,
}

impl<'ctx, S: SmtSolver<'ctx>> PartName<'ctx, S> {
    /// Returns the SMT bitvector constant of this part.
    pub fn name(&self) -> &S::BV {
        &self.name
    }

    /// Returns the SMT expression for this part.
    pub fn smt(&self) -> &S::BV {
        &self.smt
    }
}

/// An SMT solver mode of an encoding's semantics.
#[derive(Clone, Debug)]
pub struct Z3Model<'ctx, A: Arch, S: SmtSolver<'ctx>> {
    // TODO: Add constraints on the instruction bitstring here...
    constraints: Vec<S::Bool>,
    intermediate_outputs: Vec<IntermediateOutput<'ctx, A, S>>,
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> Z3Model<'ctx, A, S> {
    fn build_outputs<C: Computation + AsComputationRef>(
        encoding: &Encoding<A, C>,
    ) -> impl Iterator<Item = (FilledOutput<A>, (usize, &'_ Dataflow<A, C>))> + '_ {
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
                    .map(|(part_index, _)| FilledOutput::Part(PartIndex(part_index), flow.target.size()))
                    .unwrap_or_else(|| FilledOutput::Concrete(flow.target));
                (target, (output_index, flow))
            })
    }

    /// Constructs an SMT model for the provided encoding.
    pub fn of<'a, C: Computation + AsComputationRef>(
        encoding: &'a Encoding<A, C>, storage: &mut StorageLocations<'ctx, A, S>, context: &mut S,
    ) -> Self {
        // TODO: Add exclusion constraints for any imm parts that have exclusion entries in their mapping.

        trace!("Building z3 model for: {encoding}");
        let mut constraints = Vec::new();
        let intermediate_outputs = Self::build_outputs(encoding)
            .map(|(output, (output_index, _flow))| {
                // TODO: Compose output of multiple outputs according to write ordering
                let prepared = PreparedComputation::prepare(encoding, output_index, storage, context);
                let size = output.size().num_bytes() as u32 * 8;

                let smt = prepared.map(|prepared| {
                    // TODO: Generate less constraints by using the parts themselves similar to how we map the outputs
                    constraints.extend(prepared.part_assertions);

                    let mut gen = Z3CodeGen::new(context, prepared.z3_inputs.clone());
                    let smt = codegen_computation(&mut gen, prepared.computation);
                    let result = smt.as_bv();
                    result.clone().extract(size - 1, 0)
                });

                IntermediateOutput {
                    target: output,
                    name: context.new_bv_const(format!("val{output_index}"), size),
                    smt,
                }
            })
            .collect::<Vec<_>>();

        Z3Model {
            constraints,
            intermediate_outputs,
        }
    }

    /// Returns the intermediate outputs in the model.
    ///
    /// These are all the dataflows.
    /// Some outputs may already have a concrete destination.
    /// Other outputs' destinations may depend on part values in the instruction bitstring.
    pub fn intermediate_outputs(&self) -> &[IntermediateOutput<'ctx, A, S>] {
        self.intermediate_outputs.as_slice()
    }

    /// Returns a set of constraints on the part values in the instruction bitstring.
    pub fn constraints(&self) -> &[S::Bool] {
        &self.constraints
    }

    /// Builds an SMT model that only uses concrete outputs.
    ///
    /// Outputs that depend on a part value are rewritten as follows:
    ///
    /// For each possible part value, the output is computed.
    /// Then, for each output, an expression is formed of the following shape:
    ///
    /// ```ignore
    /// let new_value = if part_value == EXPECTED_VALUE {
    ///     intermediate_output_bv
    /// } else {
    ///     old_value
    /// };
    /// ```
    pub fn compute_concrete_outputs<C: Computation>(
        &self, encoding: &Encoding<A, C>, storage: &mut StorageLocations<'ctx, A, S>, context: &mut S,
    ) -> ConcreteZ3Model<'ctx, A, S> {
        let mut output_splits = SplitDests::<A>::new();
        for part in encoding.parts.iter() {
            if let PartMapping::Register {
                mapping,
                locations,
            } = &part.mapping
            {
                for &location in locations.iter() {
                    if let FlowValueLocation::Output(output_index) = location {
                        let output = encoding.dataflows.output_dataflow(output_index);
                        for &reg in mapping.iter() {
                            if let Some(reg) = reg {
                                output_splits.split(Dest::Reg(reg, output.target().size()));
                            }
                        }
                    }
                }
            }
        }

        for output in encoding.dataflows.output_dataflows() {
            output_splits.split(*output.target());
        }

        let mut outputs = HashMap::new();
        let mut fixed_output = GrowingBitmap::new_all_ones(self.intermediate_outputs.len());
        let mut parts_needed = GrowingBitmap::new_all_zeros(encoding.parts.len());
        for (part_index, part) in encoding.parts.iter().enumerate() {
            if let PartMapping::Register {
                mapping,
                locations,
            } = &part.mapping
            {
                for &location in locations.iter() {
                    if let FlowValueLocation::Output(output_index) = location {
                        fixed_output.reset(output_index);
                        let output = encoding.dataflows.output_dataflow(output_index);
                        for (part_value, &reg) in mapping.iter().enumerate() {
                            if let Some(reg) = reg {
                                parts_needed.set(part_index);
                                outputs
                                    .entry(Dest::<A>::Reg(reg, output.target().size()))
                                    .or_insert_with(Vec::new)
                                    .push(Case {
                                        output_index,
                                        part_index,
                                        part_value,
                                    });
                            }
                        }
                    }
                }
            }
        }

        let part_mappings = parts_needed
            .iter()
            .enumerate()
            .map(|(part_index, needed)| {
                if needed {
                    Some(PartName {
                        name: context.new_bv_const(
                            format!("instrPart{}", PART_NAMES[part_index].to_uppercase()),
                            encoding.part_size(part_index) as u32,
                        ),
                        smt: storage.instr_bits(encoding.part_bit_indices(part_index)).simplify(),
                    })
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        let fixed_outputs = fixed_output
            .iter_one_indices()
            .flat_map(|output_index| {
                let output = &encoding.dataflows[output_index];
                output_splits.get(*output.target()).map(move |dest| (output_index, dest))
            })
            .collect::<Vec<_>>();

        debug!("Fixed outputs: {fixed_outputs:?}");

        let mut fixed_output_choices = HashMap::new();
        for &(output_index, target) in fixed_outputs.iter() {
            if let Some(seen_index) = fixed_output_choices.remove(&target) {
                if let Some(wo) = encoding
                    .write_ordering
                    .iter()
                    .find(|w| w.output_index_order.contains(&seen_index) && w.output_index_order.contains(&output_index))
                {
                    let seen_priority = wo.output_index_order.iter().position(|n| n == &seen_index).unwrap();
                    let output_priority = wo.output_index_order.iter().position(|n| n == &output_index).unwrap();

                    debug!(
                        "Fixing conflict between outputs {output_index} and {seen_index}: priorities {output_priority} vs {seen_priority} according to {wo:?}"
                    );
                    if seen_priority > output_priority {
                        fixed_output_choices.insert(target, seen_index);
                    } else {
                        fixed_output_choices.insert(target, output_index);
                    }
                } else {
                    fixed_output_choices.insert(target, output_index);
                }
            } else {
                fixed_output_choices.insert(target, output_index);
            }
        }

        let concrete_outputs = fixed_output_choices
            .into_iter()
            .map(|(target, output_index)| {
                let output = encoding.dataflows.output_dataflow(output_index);
                let smt = self.intermediate_outputs[output_index].smt().cloned();
                let smt = if let Some((before, overlapping, _)) = output.target().size().split_by_overlap(target.size()) {
                    let skip_before = before.map(|s| s.num_bytes()).unwrap_or(0);
                    let take = overlapping.num_bytes();
                    smt.map(|smt| smt.extract((skip_before + take) as u32 * 8 - 1, skip_before as u32 * 8))
                } else {
                    smt
                };

                ConcreteOutput {
                    target,
                    smt,
                }
            })
            .chain(outputs.into_iter().map(|(target, mut cases)| {
                println!("Target {target:?} has cases {cases:?}");

                let smt = if cases
                    .iter()
                    .any(|case| self.intermediate_outputs[case.output_index].smt.is_none())
                {
                    None
                } else {
                    let key = FilledLocation::from(FilledOutput::Concrete(target));
                    let is_bytes = matches!(target.value_type(), ValueType::Bytes(_));
                    let mut smt = storage.get_sized(context, key, &Sizes::default(), target.size(), is_bytes);

                    if cases.len() > 1 {
                        let mut relevant_write_orderings = Vec::new();
                        for case in cases.iter() {
                            trace!("Case: {case:?}");
                            let relevant = encoding
                                .write_ordering
                                .iter()
                                .filter(|order| {
                                    order.part_values[case.part_index]
                                        .map(|val| val == case.part_value as u64)
                                        .unwrap_or(true)
                                })
                                .filter(|order| !order.output_index_order.is_empty())
                                .collect::<Vec<_>>();
                            trace!("Relevant write orders: {:?}", relevant);
                            relevant_write_orderings.extend(relevant);
                        }

                        let orders = relevant_write_orderings
                            .iter()
                            .map(|o| &o.output_index_order)
                            .collect::<HashSet<_>>();

                        assert!(orders.len() <= 1);

                        if let Some(order) = orders.into_iter().next() {
                            debug!("Ordering to assume: {order:?}");

                            debug!("Sorting {cases:?} according to {:?}", order);
                            cases.sort_by_key(|case| order.iter().rev().position(|&o| o == case.output_index));
                        }
                    }

                    debug!("Cases: {cases:?}");
                    for case in cases.iter().rev() {
                        let part_value: &S::BV = part_mappings[case.part_index].as_ref().unwrap().name();
                        let required_value =
                            context.bv_from_u64(case.part_value as u64, encoding.part_size(case.part_index) as u32);
                        let condition = part_value.clone()._eq(required_value);

                        let new_value = self.intermediate_outputs[case.output_index].name();
                        assert_eq!(new_value.get_size(), smt.get_size());

                        smt = condition.ite_bv(new_value.clone(), smt);
                    }

                    Some(smt)
                };

                ConcreteOutput {
                    target,
                    smt,
                }
            }))
            .collect::<Vec<_>>();

        ConcreteZ3Model {
            intermediate_values_needed: fixed_output.flipped().iter_one_indices().collect::<Vec<_>>(),
            part_names: part_mappings.into_iter().flatten().collect(),
            concrete_outputs,
        }
    }
}

/// A case where a specific value for a specific part determines the output that will be written.
#[derive(Copy, Clone, Debug)]
struct Case {
    output_index: usize,
    part_index: usize,
    part_value: usize,
}

/// A concrete SMT model of an encoding's semantics, where all outputs have been instantiated and no longer contain any references to encoding parts.
#[derive(Clone, Debug)]
pub struct ConcreteZ3Model<'ctx, A: Arch, S: SmtSolver<'ctx>> {
    part_names: Vec<PartName<'ctx, S>>,
    concrete_outputs: Vec<ConcreteOutput<'ctx, A, S>>,
    intermediate_values_needed: Vec<usize>,
}

impl<'ctx, A: Arch, S: SmtSolver<'ctx>> ConcreteZ3Model<'ctx, A, S> {
    /// Returns all concrete outputs in the model.
    pub fn concrete_outputs(&self) -> &[ConcreteOutput<'ctx, A, S>] {
        &self.concrete_outputs
    }

    /// Returns the part names of the model.
    pub fn part_names(&self) -> &[PartName<'ctx, S>] {
        self.part_names.as_ref()
    }

    /// Returns which intermediate indices need to be asserted to obtain correct results in the final output.
    pub fn intermediate_values_needed(&self) -> &[usize] {
        &self.intermediate_values_needed
    }
}
