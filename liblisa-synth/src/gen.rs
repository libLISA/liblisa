use std::iter::repeat_with;

use arrayvec::ArrayVec;
use itertools::Itertools;
use liblisa::arch::{Arch, Register};
use liblisa::encoding::bitpattern::{FlowInputLocation, PartMapping};
use liblisa::encoding::dataflows::{Dataflows, Dest, Source};
use liblisa::encoding::Encoding;
use liblisa::instr::Instruction;
use liblisa::oracle::MappableArea;
use liblisa::semantics::InputValues;
use liblisa::state::random::{randomized_bytes_into_buffer, randomized_value, StateGen};
use liblisa::state::{AsSystemState, Location, SystemState};
use liblisa::value::{AsValue, MutValue, OwnedValue};
use log::{debug, error, info};
use rand::seq::IteratorRandom;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

#[derive(Clone, Debug)]
pub struct TestCase<A: Arch> {
    pub state: SystemState<A>,
    pub part_values: ArrayVec<u64, 32>,
}

impl<A: Arch> AsSystemState<A> for TestCase<A> {
    type Output<'a> = &'a SystemState<A>;

    fn as_system_state(&self) -> Self::Output<'_> {
        &self.state
    }
}

pub struct TestCaseGen<A: Arch> {
    encoding: Encoding<A, ()>,
    locations: Vec<Location<A>>,
    interesting_inputs: Vec<(usize, InputValues)>,
}

pub struct TestCaseGenWithBase<'a, A: Arch, M: MappableArea> {
    inner: &'a TestCaseGen<A>,
    state_gen: StateGen<'a, A, M>,
    base_state: SystemState<A>,
}

impl<A: Arch> TestCaseGen<A> {
    /// Similar to Self::new, but does not:
    ///     - Copy interesting inputs from SynthesisLoop
    ///     - Check for duplicate outputs
    pub fn new_raw(encoding: &Encoding<A, ()>, output_indices: &[usize], rng: &mut impl Rng) -> Option<Self> {
        let part_values = encoding
            .parts
            .iter()
            .map(|p| match &p.mapping {
                PartMapping::Imm {
                    locations,
                    bits,
                    ..
                } if bits.is_some()
                    || locations
                        .iter()
                        .any(|loc| matches!(loc, FlowInputLocation::MemoryAddress { .. })) =>
                {
                    Some(randomized_value(rng) & (((1u128 << p.size) - 1) as u64))
                },
                PartMapping::MemoryComputation {
                    ..
                }
                | PartMapping::Register {
                    ..
                } => Some(rng.gen_range(0..1 << p.size)),
                _ => None,
            })
            .collect::<ArrayVec<_, 32>>();

        let encoding = encoding.instantiate_partially(&part_values).ok()?;
        let locations = encoding
            .dataflows
            .output_dataflows()
            .enumerate()
            .filter(|(output_index, _)| output_indices.contains(output_index))
            .flat_map(|(_, flow)| flow.inputs.iter())
            .flat_map(|source| match source {
                Source::Dest(d) => Some(Location::from(d)),
                Source::Imm(_) => None,
                Source::Const {
                    ..
                } => None,
            })
            .unique()
            .collect::<Vec<_>>();

        Some(Self {
            encoding,
            locations,
            interesting_inputs: Vec::new(),
        })
    }

    fn randomized_parts(&self, rng: &mut impl Rng) -> ArrayVec<u64, 32> {
        self.encoding
            .parts
            .iter()
            .map(|part| randomized_value(rng) & (((1u128 << part.size) - 1) as u64))
            .collect()
    }

    pub(crate) fn instance(&self) -> &Dataflows<A, ()> {
        &self.encoding.dataflows
    }

    pub fn add_interesting_input(&mut self, output_index: usize, inputs: InputValues) {
        self.interesting_inputs.push((output_index, inputs));
    }

    pub fn with_mappable_area<'a, M: MappableArea>(
        &'a self, mappable_area: &'a M, rng: &mut impl Rng,
    ) -> Option<TestCaseGenWithBase<'a, A, M>> {
        let state_gen = StateGen::new(&self.instance().addresses, mappable_area).ok()?;
        let base_state = state_gen.randomize_new(rng).ok()?;

        info!("Instance = {}", self.instance());
        debug!("Debug = {:?}", self.instance());

        Some(TestCaseGenWithBase {
            inner: self,
            state_gen,
            base_state,
        })
    }

    fn instr_from_part_values(&self, part_values: &[u64]) -> Instruction {
        self.encoding.all_part_values_to_instr(part_values)
    }
}

impl<A: Arch, M: MappableArea> TestCaseGenWithBase<'_, A, M> {
    pub fn instance(&self) -> &Dataflows<A, ()> {
        self.inner.instance()
    }

    fn generate_cases_with_equalities<'l>(&'l self, rng: &mut impl Rng) -> impl Iterator<Item = TestCase<A>> + 'l {
        let mut rng2 = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
        let mut rng3 = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
        repeat_with(move || self.inner.instance().output_dataflows().choose(&mut rng3))
            .take(250)
            .flatten()
            .flat_map(move |dataflow| {
                if dataflow.inputs.len() > 1 && dataflow.inputs.iter().any(|s| s.can_modify()) {
                    let mut rng = Xoshiro256PlusPlus::seed_from_u64(rng2.gen());

                    Some(
                        repeat_with(move || {
                            Some({
                                let source1_index = rng.gen_range(0..dataflow.inputs.len());
                                let source1 = &dataflow.inputs[source1_index];
                                let source2_index = loop {
                                    let n = rng.gen_range(0..dataflow.inputs.len());
                                    if n != source1_index {
                                        break n;
                                    }
                                };
                                let source2 = &dataflow.inputs[source2_index];

                                if let Source::Dest(source1_as_dest) = source1 {
                                    if source1_as_dest.is_flags()
                                        || matches!(source1_as_dest, Dest::Reg(reg, _) if reg.mask().is_some())
                                    {
                                        return None;
                                    }

                                    match self.state_gen.randomize_new_with_locations(
                                        &self.base_state,
                                        &self.inner.locations,
                                        &mut rng,
                                    ) {
                                        Ok(mut state) => {
                                            let part_values = self.inner.randomized_parts(&mut rng);
                                            state.memory_mut().get_mut(0).modify_data(|bytes| {
                                                let instr = self.inner.instr_from_part_values(&part_values);
                                                bytes.copy_from_slice(instr.bytes());
                                            });

                                            let as_le = rng.gen();
                                            let (val, num_bytes_in_val) = match source2 {
                                                Source::Imm(index) => (
                                                    OwnedValue::Num(part_values[*index]),
                                                    (self.inner.encoding.parts[*index].size + 7) / 8,
                                                ),
                                                Source::Dest(d) => (state.get_dest(d).to_owned_value(), d.size().num_bytes()),
                                                Source::Const {
                                                    value,
                                                    num_bits,
                                                } => (OwnedValue::Num(*value), (num_bits + 7) / 8),
                                            };
                                            state.modify_dest(source1_as_dest, |mut target| {
                                                if as_le {
                                                    target.fill_le_from_value(num_bytes_in_val, &val.as_value())
                                                } else {
                                                    target.fill_be_from_value(&val.as_value())
                                                }
                                            });

                                            if rng.gen() {
                                                let mask = source1_as_dest.mask();
                                                let num_bits = mask
                                                    .map(|m| 64 - m.leading_zeros() as u64)
                                                    .unwrap_or(source1_as_dest.size().num_bytes() as u64 * 8);
                                                state.modify_dest(source1_as_dest, |target| match target {
                                                    MutValue::Num(n) => {
                                                        *n = (*n ^ (1 << rng.gen_range(0..num_bits))) & mask.unwrap_or(u64::MAX)
                                                    },
                                                    MutValue::Bytes(b) => {
                                                        let bit = rng.gen_range(0..num_bits);
                                                        b[(bit / 8) as usize] ^= 1 << (bit & 7);
                                                    },
                                                });
                                            }

                                            if self.state_gen.adapt(&mut state, false) {
                                                Some(TestCase {
                                                    state,
                                                    part_values,
                                                })
                                            } else {
                                                None
                                            }
                                        },
                                        _ => None,
                                    }
                                } else {
                                    None
                                }
                            })
                        })
                        .take(1000)
                        .flatten()
                        .flatten()
                        .take(10),
                    )
                } else {
                    None
                }
            })
            .flatten()
    }

    fn generate_cases_from_interesting_inputs<'l>(&'l self, rng: &mut impl Rng) -> impl Iterator<Item = TestCase<A>> + 'l {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
        self.inner.interesting_inputs.iter().flat_map(move |(index, inputs)| {
            let mut rng = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
            repeat_with(move || {
                let mut state = self
                    .state_gen
                    .randomize_new_with_locations(&self.base_state, &self.inner.locations, &mut rng)
                    .ok()?;
                let mut part_values = self.inner.randomized_parts(&mut rng);

                let dataflow = self.inner.instance().output_dataflow(*index);
                for (source, val) in dataflow.inputs.iter().zip(inputs.iter()) {
                    if let Source::Dest(dest) = source {
                        state.modify_dest(dest, |mut target| target.copy_from(val))
                    } else if let Source::Imm(index) = source {
                        part_values[*index] = val.unwrap_num();
                    }
                }

                if dataflow.inputs.is_empty() {
                    return None
                }

                let source1_index = rng.gen_range(0..dataflow.inputs.len());
                let source1 = &dataflow.inputs[source1_index];

                if let Source::Imm(imm_index) = *source1 {
                    let num_bits = self.inner.encoding.parts[imm_index].size;
                    let num_bytes = (num_bits + 7) / 8;
                    let mask = !(u64::MAX << num_bits);
                    match rng.gen::<u8>() & 3 {
                        // Modify entire dest
                        0 => part_values[imm_index] = randomized_value(&mut rng) & mask,
                        // Modify single byte
                        1 => {
                            let new_byte = rng.gen::<u8>() as u64;
                            part_values[imm_index] =
                                (part_values[imm_index] ^ (new_byte << (rng.gen_range(0..num_bytes) * 8))) & mask;
                        },
                        // Modify single bit
                        2 | 3 => part_values[imm_index] = (part_values[imm_index] ^ (1 << rng.gen_range(0..num_bits))) & mask,
                        _ => unreachable!(),
                    }

                    state.memory_mut().get_mut(0).modify_data(|bytes| {
                        let instr = self.inner.instr_from_part_values(&part_values);
                        bytes.copy_from_slice(instr.bytes());
                    });

                    Some(TestCase {
                        state,
                        part_values,
                    })
                } else if let Source::Dest(source1_as_dest) = source1 {
                    if source1_as_dest.is_flags() || matches!(source1_as_dest, Dest::Reg(reg, _) if reg.mask().is_some()) {
                        return None;
                    }

                    let size = source1_as_dest.size();
                    let num_bytes = size.num_bytes();
                    let num_bits = num_bytes * 8;
                    let u64_mask = source1_as_dest.mask().unwrap_or(u64::MAX >> (64 - num_bits));
                    match rng.gen::<u8>() & 3 {
                        // Modify entire dest
                        0 => state.modify_dest(source1_as_dest, |target| match target {
                            MutValue::Num(n) => *n = randomized_value(&mut rng) & u64_mask,
                            MutValue::Bytes(b) => randomized_bytes_into_buffer(&mut rng, b),
                        }),
                        // Modify single byte
                        1 => state.modify_dest(source1_as_dest, |target| {
                            let mask = source1_as_dest.mask();
                            match target {
                                MutValue::Num(n) => {
                                    let new_byte = rng.gen::<u8>() as u64;
                                    *n = (*n ^ (new_byte << (rng.gen_range(0..num_bytes) * 8))) & mask.unwrap_or(u64::MAX)
                                },
                                MutValue::Bytes(b) => {
                                    let byte = rng.gen_range(0..num_bytes);
                                    b[byte] = rng.gen();
                                },
                            }
                        }),
                        // Modify all bytes that have a certain value
                        2 => {
                            let index = rng.gen_range(0..num_bytes);

                            let original_value = state.get_dest(source1_as_dest).select_byte(index);
                            let new_value = rng.gen::<u8>();

                            for source in dataflow.inputs.iter() {
                                if let Source::Dest(dest) = source {
                                    state.modify_dest(dest, |target| match target {
                                        MutValue::Num(v) => {
                                            let mask = dest.mask().unwrap_or(u64::MAX >> (64 - num_bits));
                                            let mut bytes = v.to_ne_bytes();
                                            for b in bytes.iter_mut() {
                                                if *b == original_value {
                                                    *b = new_value;
                                                }
                                            }

                                            let n = u64::from_ne_bytes(bytes);
                                            *v = n & mask;
                                        },
                                        MutValue::Bytes(bytes) => {
                                            for b in bytes.iter_mut() {
                                                if *b == original_value {
                                                    *b = new_value;
                                                }
                                            }
                                        },
                                    })
                                }
                            }
                        },
                        // Modify single bit
                        3 => state.modify_dest(source1_as_dest, |target| {
                            let num_bits = source1_as_dest
                                .mask()
                                .map(|m| 64 - m.leading_zeros() as u64)
                                .unwrap_or(source1_as_dest.size().num_bytes() as u64 * 8);
                            match target {
                                MutValue::Num(n) => *n = (*n ^ (1 << rng.gen_range(0..num_bits))) & u64_mask,
                                MutValue::Bytes(b) => {
                                    let bit = rng.gen_range(0..num_bits);
                                    b[(bit / 8) as usize] ^= 1 << (bit & 7);
                                },
                            }
                        }),
                        _ => unreachable!(),
                    }

                    if self.state_gen.adapt(&mut state, false) {
                        state.memory_mut().get_mut(0).modify_data(|bytes| {
                            let instr = self.inner.instr_from_part_values(&part_values);
                            bytes.copy_from_slice(instr.bytes());
                        });

                        Some(TestCase {
                            state,
                            part_values,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .take(1000)
            .flatten()
            .take(10)
        })
    }

    pub fn iter(&self, rng: &mut impl Rng, scale_factor: usize) -> impl Iterator<Item = TestCase<A>> + '_ {
        let mut rng1 = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
        let mut rng2 = Xoshiro256PlusPlus::seed_from_u64(rng.gen());
        let test_cases = repeat_with(move || {
            self.state_gen
                .randomize_new_with_locations(&self.base_state, &self.inner.locations, &mut rng1)
        })
        .take(10_000)
        .flat_map(|state| {
            if let Err(e) = &state {
                error!("State generation error: {e}");
            }

            state.ok()
        })
        .map(move |mut state| {
            let part_values = self.inner.randomized_parts(&mut rng2);
            state.memory_mut().get_mut(0).modify_data(|bytes| {
                let instr = self.inner.instr_from_part_values(&part_values);
                bytes.copy_from_slice(instr.bytes());
            });

            TestCase {
                state,
                part_values,
            }
        })
        .take(scale_factor);
        let test_cases_with_equality = self.generate_cases_with_equalities(rng).take(5 * scale_factor);
        let test_cases_from_interesting = self.generate_cases_from_interesting_inputs(rng);

        test_cases
            .interleave(test_cases_with_equality)
            .interleave(test_cases_from_interesting)
    }
}
