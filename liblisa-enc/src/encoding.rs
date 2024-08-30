use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::iter::repeat_with;
use std::time::Instant;

use itertools::Itertools;
use liblisa::arch::Arch;
use liblisa::encoding::bitpattern::{
    Bit, FlowInputLocation, FlowOutputLocation, FlowValueLocation, ImmBitOrder, MappingOrBitOrder, Part, PartMapping, PartValue,
};
use liblisa::encoding::dataflows::{AddressComputation, Dataflows, Source};
use liblisa::encoding::Encoding;
use liblisa::oracle::{Oracle, OracleError};
use liblisa::state::random::{RandomizationError, RemapError, StateGen};
use log::{debug, error, info, trace, warn};
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;
use thiserror::Error;

use crate::cache::EncodingAnalysisCache;
use crate::changes::{ThresholdValues, *};
use crate::cleanup::{
    remove_incorrect_generalizations, remove_incorrect_memory_computations, remove_useless_bits, DontCareValidator,
};

/// Infers [`Encoding`]s.
pub struct EncodingAnalysis<'borrow, A: Arch, O: Oracle<A>, C: EncodingAnalysisCache<A>> {
    o: &'borrow mut O,
    cache: &'borrow C,
    dataflows: &'borrow Dataflows<A, ()>,
    threshold_values: ThresholdValues<A>,
    found_dependent_bytes: bool,
}

/// Error returned when [`EncodingAnalysis`] fails.
#[derive(Error, Debug)]
pub enum EncodingError<A: Arch> {
    #[error("Not supported")]
    NotSupported,

    #[error("Randomization failed: {}", .0)]
    RandomizationFailed(RandomizationError),

    #[error("Remapping failed: {}", .0)]
    RemapFailed(RemapError<A>),

    #[error("Oracle error: {}", .0)]
    Oracle(OracleError),
}

impl<A: Arch> From<RandomizationError> for EncodingError<A> {
    fn from(e: RandomizationError) -> Self {
        EncodingError::RandomizationFailed(e)
    }
}

impl<A: Arch> From<RemapError<A>> for EncodingError<A> {
    fn from(e: RemapError<A>) -> Self {
        EncodingError::RemapFailed(e)
    }
}

impl<A: Arch> From<OracleError> for EncodingError<A> {
    fn from(e: OracleError) -> Self {
        EncodingError::Oracle(e)
    }
}

#[derive(Debug)]
enum CurrentMappedValue<A: Arch> {
    Reg(A::Reg),
    Computation(AddressComputation),
    MemoryOffset(i64),
    None,
}

fn guess_bit_order(bits: Vec<(usize, Option<usize>)>, index: usize) -> Option<ImmBitOrder> {
    let deltas = bits
        .windows(2)
        .map(|v| match v {
            [(_, Some(old)), (_, Some(new))] => Some(*new as i64 - *old as i64),
            _ => None,
        })
        .collect::<Vec<_>>();

    info!("Guessing memory access of bit {}", index);
    info!("Bits: {:?}", bits);
    info!("Deltas: {:?}", deltas);

    for repeat_len in 2..deltas.len() {
        if deltas.iter().enumerate().all(|(index, n)| {
            if let Some(n) = n {
                index
                    .checked_sub(repeat_len)
                    .map(|prev_index| match deltas.get(prev_index) {
                        Some(Some(delta)) => delta == n,
                        _ => true,
                    })
                    .unwrap_or(true)
            } else {
                true
            }
        }) {
            let index = bits.iter().position(|&(n, _)| n == index).unwrap();
            let repeated_deltas = (0..repeat_len)
                .map(|delta_index| {
                    for k in 0..deltas.len() / repeat_len + 1 {
                        let index = delta_index + repeat_len * k;
                        if let Some(Some(delta)) = deltas.get(index) {
                            return Some(delta);
                        }
                    }

                    None
                })
                .collect::<Vec<_>>();
            info!("Repeat length is {repeat_len} with repeated_deltas={repeated_deltas:?}");

            // Checking forwards
            for (start_index, (_, bit_value)) in (0..index).zip(bits.iter()).rev() {
                debug!("  - checking (fwd) start_index={start_index} with bit_value={bit_value:?}");
                if let Some(bit_value) = bit_value {
                    let bit_index = repeat_with(|| repeated_deltas.iter())
                        .flatten()
                        .skip(start_index)
                        .take(index - start_index)
                        .try_fold(*bit_value, |a, &b| b.map(|&b| a.wrapping_add(b as usize)));
                    if let Some(bit_index) = bit_index {
                        info!("Guessed index: {}", bit_index);

                        // TODO: Can/should we ever guess negative?
                        return Some(ImmBitOrder::Positive(bit_index));
                    } else {
                        info!("Unable to guess from bit_value={bit_value} at start_index={start_index}");
                    }
                }
            }

            // Checking backwards
            for (start_index, (_, bit_value)) in (index + 1..bits.len()).zip(bits.iter().skip(index + 1)) {
                debug!("  - checking (bwd) start_index={start_index} with bit_value={bit_value:?}");

                if let Some(bit_value) = bit_value {
                    let bit_index = repeat_with(|| repeated_deltas.iter())
                        .flatten()
                        .take(start_index)
                        .collect::<Vec<_>>()
                        .into_iter()
                        .rev()
                        .take(start_index - index)
                        .try_fold(*bit_value, |a, &b| b.map(|&b| a.wrapping_sub(b as usize)));
                    if let Some(bit_index) = bit_index {
                        info!("Guessed index: {}", bit_index);

                        // TODO: Can/should we ever guess negative?
                        return Some(ImmBitOrder::Positive(bit_index));
                    } else {
                        info!("Unable to guess from bit_value={bit_value} at start_index={start_index}");
                    }
                }
            }
        }
    }

    warn!("Unable to find pattern");
    None
}

fn count_around<A: Arch, F: FnMut(&Change<A>) -> bool>(changes: &[Change<A>], index: usize, mut check: F) -> usize {
    let mut around = 0;
    let mut pos = index;
    while pos >= 1 {
        pos -= 1;
        if check(&changes[pos]) {
            around += 1;
        } else {
            break;
        }
    }

    let mut pos = index;
    while pos < changes.len() - 1 {
        pos += 1;
        if check(&changes[pos]) {
            around += 1;
        } else {
            break;
        }
    }

    around
}

fn register_locations_valid_with<A: Arch>(locations: &[ChangeLocation], changes: &[Change<A>]) -> bool {
    changes.iter().all(|other| match other {
        Change::Register {
            locations: other_locations,
            ..
        } => {
            // other_locations must either be a subset of locations, or not contain any of the same registers for the current change to be valid
            debug!(
                "Checking: {:?} subset or distinct from {:?} {} {}",
                locations,
                other_locations,
                other_locations.iter().all(|other| locations.contains(other)),
                other_locations.iter().all(|other| !locations.contains(other))
            );
            other_locations.iter().all(|other| locations.contains(other))
                || other_locations.iter().all(|other| !locations.contains(other))
        },
        _ => true,
    })
}

fn cleanup_bit_changes<A: Arch>(bit_changes: &mut [Change<A>]) {
    let mut v = HashSet::new();
    let mut start_index = None;

    // Expand scope for consecutive ValueImms that have overlapping output_indexes
    // Rationale behind this: it's very unlikely that two immediate values will be used in partially different, but also partially
    // equivalent outputs. In the case that this does happen, we can still correctly learn semantics if we allow the semantics to
    // contain some logic for splitting the two values. On the other hand, if we end up with multiple separate parts in the case
    // where there is only one (but for some reason, we can't conclusively detect this) semantics become pretty much impossible
    // to learn correctly. Therefore, it is preferrable to have these joined here.
    // TODO: Handle memory_indexes?
    for index in 0..bit_changes.len() {
        debug!(
            "Expanding scope for ValueImms in change #{:2}: {:?}",
            index, bit_changes[index]
        );
        if let Change::ValueImm {
            output_indexes, ..
        } = &bit_changes[index]
        {
            if let Some(start_index) = start_index
                && output_indexes.iter().any(|index| v.contains(index))
            {
                // There is at least some overlap between earlier items
                for index in output_indexes {
                    v.insert(*index);
                }

                // Make sure all earlier items use the expanded locations
                let new_output_indexes: Vec<usize> = v.iter().copied().sorted().collect();
                for change in bit_changes[start_index..=index].iter_mut() {
                    if let Change::ValueImm {
                        output_indexes,
                    } = change
                    {
                        output_indexes.clone_from(&new_output_indexes);
                    }
                }
            } else {
                start_index = Some(index);
                v = output_indexes.iter().copied().collect();
            }
        } else {
            start_index = None;
            v.clear()
        }
    }

    for index in 0..bit_changes.len() {
        debug!(
            "Picking the best change from Change::Multiple in change #{:2}: {:?}",
            index, bit_changes[index]
        );
        if let Change::Multiple(items) = &bit_changes[index] {
            let mut items_copy = items.clone();
            items_copy.retain(|item| match item {
                Change::Register {
                    locations, ..
                } => register_locations_valid_with(locations, bit_changes),
                _ => unreachable!("Choice between: {item:?}"),
            });

            // If we have a definitive choice that already does the exact thing we're considering for this bit,
            // we should not pick it for this bit.
            items_copy.retain(|item| match item {
                Change::Register {
                    locations,
                    from,
                    to,
                } => bit_changes.iter().any(|change| match change {
                    Change::Register {
                        locations: other_locations,
                        from: other_from,
                        to: other_to,
                    } => from == other_from && to == other_to && locations.iter().all(|l| other_locations.contains(l)),
                    _ => false,
                }),
                _ => unreachable!(),
            });

            if items_copy.len() > 1 {
                warn!("Multiple choices, picking the first of: {:?}", items_copy);
                items_copy.drain(1..);
            }

            let mut new_change = Change::Multiple(items_copy);
            new_change.normalize();

            bit_changes[index] = new_change;
        }
    }

    // Clean up changes by:
    // - removing Imm values of too few bits
    // - folding memory errors in to Imms if possible
    for index in 0..bit_changes.len() {
        debug!("Cleaning #{:2}: {:?}", index, bit_changes[index]);
        match &bit_changes[index] {
            Change::UnknownMemoryError {
                access_index,
            } => {
                let mut around = None;
                let mut real_addresses = 0;
                let memory_around = count_around(bit_changes, index, |change| match change {
                    Change::MemoryOffset {
                        locations, ..
                    } if locations.contains(&FlowOutputLocation::MemoryAccess(*access_index)) => {
                        around = Some(change.clone());
                        real_addresses += 1;
                        true
                    },
                    Change::UnknownMemoryError {
                        access_index: i,
                    } if i == access_index => true,
                    _ => false,
                });

                if memory_around >= 4 && real_addresses >= (memory_around * 3 / 4).saturating_sub(2) {
                    bit_changes[index] = match around.unwrap() {
                        Change::MemoryOffset {
                            locations: memory_indexes,
                            offset,
                            decreasing,
                            ..
                        } => {
                            // TODO: Guess the bit indices
                            Change::MemoryOffset {
                                bit_indexes: Vec::new(),
                                locations: memory_indexes,
                                decreasing,
                                offset,
                                guessed: true,
                            }
                        },
                        _ => unreachable!(),
                    };
                } else {
                    bit_changes[index] = Change::Invalid;
                }
            },
            Change::ValueImm {
                output_indexes: _,
            } => {
                if count_around(bit_changes, index, |change| change == &bit_changes[index]) < 3 {
                    bit_changes[index] = Change::Invalid;
                }
            },
            Change::MemoryOffset {
                locations, ..
            } => {
                if count_around(bit_changes, index, |change| match change {
                    Change::UnknownMemoryError {
                        access_index,
                    } => locations.contains(&FlowOutputLocation::MemoryAccess(*access_index)),
                    Change::MemoryOffset {
                        locations: memory_indexes,
                        ..
                    } => memory_indexes == locations,
                    _ => false,
                }) < 2
                {
                    bit_changes[index] = Change::Invalid;
                }
            },
            Change::MemoryComputation {
                memory_indexes: locations,
                ..
            } => {
                // See comment for Change::Register below.
                if !bit_changes.iter().all(|other| match other {
                    Change::MemoryComputation {
                        memory_indexes: other_locations,
                        ..
                    } => {
                        // other_locations must either be a subset of locations, or not contain any of the same registers for the current change to be valid
                        debug!(
                            "Checking: {:?} subset or distinct from {:?} {} {}",
                            locations,
                            other_locations,
                            other_locations.iter().all(|other| locations.contains(other)),
                            other_locations.iter().all(|other| !locations.contains(other))
                        );
                        other_locations.iter().all(|other| locations.contains(other))
                            || other_locations.iter().all(|other| !locations.contains(other))
                    },
                    _ => true,
                }) {
                    bit_changes[index] = Change::Invalid;
                }
            },
            Change::Register {
                locations, ..
            } => {
                // If there are multiple bits that change overlapping locations, only use the one with locations such that for all other bits the locations is a subset of this one; If there is no such bit, don't use any of them. For example, this problem occurs with the "swap output register" of add eax,edx. The bit switches the output from the first to the second operand. However, this means that every bit depends on every other bit, which would mean we would have to enumerate 127 different register combinations (which defeats the point of identifying them separately). An easier solution is to see the "swap output register" bit as a non-register bit.

                if !register_locations_valid_with(locations, bit_changes) {
                    bit_changes[index] = Change::Invalid;
                }
            },
            Change::Multiple(_) => unreachable!(),
            Change::None | Change::Invalid | Change::Error => {},
        }
    }

    debug!("Cleaned up:");
    for (index, change) in bit_changes.iter().enumerate() {
        debug!("Change #{:2}: {:?}", index, change);
    }
}

type CreatedParts<'a, A> = (Vec<Bit>, Vec<(Part<A>, CurrentMappedValue<A>, ChangeBase<'a, A>)>);

fn create_parts<'a, A: Arch>(dataflows: &mut Dataflows<A, ()>, bit_changes: &'a [Change<A>]) -> CreatedParts<'a, A> {
    let instr = dataflows.addresses.instr;
    let mut bits = Vec::new();
    let mut mapping = HashMap::<_, usize>::new();
    let mut part_info: Vec<(Part<A>, CurrentMappedValue<A>, ChangeBase<A>)> = Vec::new();
    for (bit_index, change) in bit_changes.iter().enumerate() {
        let base = change.as_base();

        // We remove AddressImms and ValueImms from the mapping if the current bit is not part of the sequence. This makes sure
        // AddressImms and ValueImms are always consecutive.
        mapping.retain(|key, _| match key {
            ChangeBase::ValueImm {
                ..
            } => key == &base,
            _ => true,
        });

        let bit_value = instr.nth_bit_from_right(bit_index);
        match change {
            Change::None => bits.push(Bit::DontCare),
            Change::Invalid | Change::Error => bits.push(Bit::Fixed(bit_value)),
            change => {
                let index = if let Some(part_index) = mapping.get(&base) {
                    let entry = &mut part_info[*part_index].0;
                    entry.value |= (bit_value as u64) << entry.size;
                    entry.size += 1;
                    if let PartMapping::Imm {
                        mapping: Some(MappingOrBitOrder::BitOrder(bit_order)),
                        ..
                    } = &mut entry.mapping
                    {
                        if let Change::MemoryOffset {
                            bit_indexes,
                            decreasing,
                            guessed,
                            offset,
                            locations: memory_indexes,
                        } = change
                        {
                            if *guessed {
                                let order = bit_changes
                                    .iter()
                                    .enumerate()
                                    .flat_map(|(index, c)| match c {
                                        Change::MemoryOffset {
                                            locations: mi,
                                            offset: o,
                                            guessed,
                                            bit_indexes,
                                            ..
                                        } if mi == memory_indexes && o == offset => {
                                            if *guessed {
                                                Some((index, None))
                                            } else {
                                                Some((index, Some(bit_indexes[0])))
                                            }
                                        },
                                        _ => None,
                                    })
                                    .collect::<Vec<_>>();

                                if let Some(guessed) = guess_bit_order(order, bit_index) {
                                    bit_order.push(guessed);
                                } else {
                                    bits.push(Bit::Fixed(bit_value));
                                    continue;
                                }
                            } else {
                                assert_eq!(bit_indexes.len(), 1);
                                bit_order.push(if *decreasing as u8 != bit_value {
                                    ImmBitOrder::Negative(bit_indexes[0])
                                } else {
                                    ImmBitOrder::Positive(bit_indexes[0])
                                });
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    *part_index
                } else {
                    trace!("Not in mapping: {:?}! Already in mapping are: {:?}", change, mapping);
                    let part_index = part_info.len();
                    part_info.push((
                        Part {
                            size: 1,
                            value: bit_value as u64,
                            mapping: match &change {
                                Change::None
                                | Change::Invalid
                                | Change::Error
                                | Change::UnknownMemoryError {
                                    access_index: _,
                                }
                                | Change::Multiple(_) => unreachable!(),
                                Change::Register {
                                    locations, ..
                                } => PartMapping::Register {
                                    locations: locations.iter().map(FlowValueLocation::from).collect::<Vec<_>>(),
                                    mapping: Vec::new(),
                                },
                                Change::ValueImm {
                                    output_indexes,
                                } => PartMapping::Imm {
                                    locations: dataflows.insert_imm_value(output_indexes.iter().copied(), part_index),
                                    mapping: None,
                                    bits: None,
                                },
                                Change::MemoryOffset {
                                    locations: memory_indexes,
                                    offset,
                                    bit_indexes,
                                    decreasing,
                                    guessed,
                                } => {
                                    if *guessed {
                                        let order = bit_changes
                                            .iter()
                                            .enumerate()
                                            .flat_map(|(index, c)| match c {
                                                Change::MemoryOffset {
                                                    locations: mi,
                                                    offset: o,
                                                    guessed,
                                                    bit_indexes,
                                                    ..
                                                } if mi == memory_indexes && o == offset => {
                                                    if *guessed {
                                                        Some((index, None))
                                                    } else {
                                                        Some((index, Some(bit_indexes[0])))
                                                    }
                                                },
                                                _ => None,
                                            })
                                            .collect::<Vec<_>>();

                                        if let Some(guessed) = guess_bit_order(order, bit_index) {
                                            let locations = dataflows.insert_memory_imms(memory_indexes, *offset, part_index);
                                            PartMapping::Imm {
                                                locations: locations.into_iter().collect(),
                                                mapping: Some(MappingOrBitOrder::BitOrder(vec![guessed])),
                                                bits: None,
                                            }
                                        } else {
                                            bits.push(Bit::Fixed(bit_value));
                                            continue;
                                        }
                                    } else {
                                        let locations = dataflows.insert_memory_imms(memory_indexes, *offset, part_index);
                                        assert_eq!(bit_indexes.len(), 1);
                                        PartMapping::Imm {
                                            locations: locations.into_iter().collect(),
                                            mapping: Some(MappingOrBitOrder::BitOrder(vec![if *decreasing as u8 != bit_value {
                                                ImmBitOrder::Negative(bit_indexes[0])
                                            } else {
                                                ImmBitOrder::Positive(bit_indexes[0])
                                            }])),
                                            bits: None,
                                        }
                                    }
                                },
                                Change::MemoryComputation {
                                    memory_indexes, ..
                                } => PartMapping::MemoryComputation {
                                    mapping: Vec::new(),
                                    memory_indexes: memory_indexes.clone(),
                                },
                            },
                        },
                        match &change {
                            Change::Register {
                                from, ..
                            } => CurrentMappedValue::Reg(*from),
                            Change::MemoryComputation {
                                from, ..
                            } => CurrentMappedValue::Computation(*from),
                            Change::MemoryOffset {
                                offset, ..
                            } => CurrentMappedValue::MemoryOffset(*offset),
                            _ => CurrentMappedValue::None,
                        },
                        base.clone(),
                    ));
                    mapping.insert(base, part_index);

                    part_index
                };

                bits.push(Bit::Part(index));
            },
        }
    }

    (bits, part_info)
}

struct PartMappingFilling<A: Arch> {
    parts: Vec<Part<A>>,
    invalid_change_indices: Vec<usize>,
}

impl<'borrow, A: Arch, O: Oracle<A> + 'borrow, C: EncodingAnalysisCache<A>> EncodingAnalysis<'borrow, A, O, C> {
    #[allow(clippy::too_many_arguments)]
    fn enum_values<T: Clone, R: Rng>(
        &mut self, rng: &mut R, size: usize, bits: &[Bit], part_index: usize, check: impl Fn(&Change<A>) -> T,
        base: &ChangeBase<A>, mapped_value: T, invalid_value: T,
    ) -> Result<Vec<T>, EncodingError<A>> {
        let instr = self.dataflows.addresses.instr;
        let mut mapping = Vec::new();
        let start = Instant::now();
        info!(
            "Enumerating values for part {:?} with size {:?} with base {:?}",
            part_index, size, base
        );
        for v in 0..1u64.checked_shl(size as u32).unwrap() {
            let mut new_instr = instr;
            let mut k = 0;
            for (index, bit) in bits.iter().enumerate() {
                match bit {
                    Bit::Part(n) if *n == part_index => {
                        new_instr = new_instr.with_nth_bit_from_right(index, (v >> k) as u8 & 1);
                        k += 1;
                    },
                    _ => {},
                }
            }

            info!(
                "Instruction variant {:?}, {:X} for value {:b} (base: {:X}, equal={:?})",
                new_instr,
                new_instr,
                v,
                instr,
                new_instr == instr
            );
            if new_instr == instr {
                mapping.push(mapped_value.clone());
            } else {
                let mappable = self.o.mappable_area();
                let mut change = ChangeAnalysis {
                    cache: self.cache,
                    dataflows: self.dataflows,
                    state_gen: StateGen::new(&self.dataflows.addresses, &mappable)?,
                    o: self.o,
                    use_trap_flag: &mut false,
                    threshold_values: &self.threshold_values,
                    found_dependent_bytes: &mut self.found_dependent_bytes,
                }
                .detect_change(rng, &new_instr)?;
                change.sort();
                let change = if let Change::Multiple(items) = &mut change {
                    items
                        .iter()
                        .find(|item| &item.as_base() == base)
                        .cloned()
                        .unwrap_or(Change::Invalid)
                } else {
                    change
                };

                if &change.as_base() == base {
                    info!("{:b} ({:X}) = {:?}", v, new_instr, change);
                    mapping.push(check(&change));
                } else {
                    error!(
                        "Checking {:?} gave a different change: {:?} but expected {:?}",
                        instr, change, base
                    );
                    mapping.push(invalid_value.clone());
                }
            }
        }

        info!("Enumerated values in {}ms", start.elapsed().as_millis());

        Ok(mapping)
    }

    fn fill_part_mapping<R: Rng>(
        &mut self, rng: &mut R, mut part_info: Vec<(Part<A>, CurrentMappedValue<A>, ChangeBase<A>)>, bits: &[Bit],
    ) -> Result<PartMappingFilling<A>, EncodingError<A>> {
        let parts_with_memory_offsets = part_info
            .iter()
            .flat_map(|(part, cur, _)| {
                if let (
                    PartMapping::Imm {
                        locations,
                        mapping: Some(MappingOrBitOrder::BitOrder(_)),
                        ..
                    },
                    CurrentMappedValue::MemoryOffset(offset),
                ) = (&part.mapping, cur)
                {
                    Some((*offset, locations.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        info!("Parts with memory offset: {:?}", parts_with_memory_offsets);
        let mut invalid_change_indices = Vec::new();
        for (index, (part, reg_or_size, base)) in part_info.iter_mut().enumerate() {
            let base: &ChangeBase<A> = base;
            match (&mut part.mapping, reg_or_size) {
                (
                    PartMapping::Register {
                        mapping, ..
                    },
                    CurrentMappedValue::Reg(mapped_value),
                ) => {
                    *mapping = self.enum_values(
                        rng,
                        part.size,
                        bits,
                        index,
                        |change| {
                            if let Change::Register {
                                to, ..
                            } = change
                            {
                                Some(*to)
                            } else {
                                None
                            }
                        },
                        base,
                        Some(*mapped_value),
                        None,
                    )?;

                    if mapping.iter().filter(|x| x.is_some()).count() <= 1 {
                        invalid_change_indices.push(index);
                    }
                },
                (
                    PartMapping::Imm {
                        locations,
                        mapping,
                        ..
                    },
                    CurrentMappedValue::None,
                ) => {
                    if part.size <= 6
                        && !locations
                            .iter()
                            .any(|loc| matches!(loc, FlowInputLocation::MemoryAddress { .. }))
                    {
                        let base_output_indices = locations
                            .iter()
                            .flat_map(|loc| match loc {
                                FlowInputLocation::InputForOutput {
                                    output_index, ..
                                } => Some(*output_index),
                                FlowInputLocation::MemoryAddress {
                                    ..
                                } => None,
                            })
                            .collect::<Vec<_>>();

                        let mapping_values = self.enum_values(
                            rng,
                            part.size,
                            bits,
                            index,
                            |change| {
                                if let Change::ValueImm {
                                    output_indexes,
                                } = change
                                {
                                    debug!("ValueImm comparison: {:?} vs {:?}", base_output_indices, output_indexes);
                                    if &base_output_indices == output_indexes {
                                        PartValue::Valid
                                    } else {
                                        PartValue::Invalid
                                    }
                                } else {
                                    PartValue::Invalid
                                }
                            },
                            base,
                            PartValue::Valid,
                            PartValue::Invalid,
                        )?;

                        if mapping_values.iter().filter(|x| x.is_invalid()).count() >= part.size {
                            info!("Mapping: {:?}, missing more than {} arguments, removing", mapping, part.size);
                            invalid_change_indices.push(index);
                        }

                        *mapping = Some(MappingOrBitOrder::Mapping(mapping_values));
                    }
                },
                (
                    PartMapping::Imm {
                        ..
                    },
                    CurrentMappedValue::MemoryOffset(_),
                ) => (),
                (
                    PartMapping::MemoryComputation {
                        mapping,
                        memory_indexes,
                    },
                    CurrentMappedValue::Computation(mapped_value),
                ) => {
                    let extra_imm = parts_with_memory_offsets
                        .iter()
                        .find(|(_, locations)| {
                            locations.iter().any(|loc| match loc {
                                FlowInputLocation::MemoryAddress {
                                    memory_index, ..
                                } => memory_indexes.contains(memory_index),
                                _ => unreachable!(),
                            })
                        })
                        .map(|(offset, _)| *offset);
                    info!("Extra imm for MemoryComputation({:?}) = {:?}", memory_indexes, extra_imm);
                    *mapping = self.enum_values(
                        rng,
                        part.size,
                        bits,
                        index,
                        |change| {
                            if let Change::MemoryComputation {
                                to, ..
                            } = change
                            {
                                let mut result = *to;
                                if let Some(offset) = extra_imm {
                                    result.add_constant_term();
                                    result.offset = result.offset.wrapping_sub(offset);
                                }

                                Some(result)
                            } else {
                                None
                            }
                        },
                        base,
                        Some({
                            let mut result = *mapped_value;
                            if let Some(offset) = extra_imm {
                                result.add_constant_term();
                                result.offset = result.offset.wrapping_sub(offset);
                            }

                            result
                        }),
                        None,
                    )?;

                    if mapping.iter().filter(|x| x.is_some()).count() <= 1 {
                        invalid_change_indices.push(index);
                    }
                },
                other => unreachable!("{other:?}"),
            }
        }

        Ok(PartMappingFilling {
            parts: part_info.into_iter().map(|(x, ..)| x).collect(),
            invalid_change_indices,
        })
    }

    fn bit_changes<R: Rng>(&mut self, rng: &mut R) -> Result<(Vec<Change<A>>, bool), EncodingError<A>> {
        let instr = self.dataflows.addresses.instr;
        let mut bit_changes = Vec::new();
        let mut use_trap_flag = self.dataflows.addresses.use_trap_flag;

        info!("Analyzing base instruction: {:?}", instr);
        for bit in 0..instr.bit_len() {
            let start = Instant::now();
            let new_instr = instr.with_nth_bit_from_right_flipped(bit);
            info!("Checking (bit {} flipped)  : {:?} {:X}", bit, new_instr, new_instr);
            let mappable = self.o.mappable_area();
            let change = ChangeAnalysis {
                cache: self.cache,
                dataflows: self.dataflows,
                state_gen: StateGen::new(&self.dataflows.addresses, &mappable)?,
                o: self.o,
                use_trap_flag: &mut use_trap_flag,
                threshold_values: &self.threshold_values,
                found_dependent_bytes: &mut self.found_dependent_bytes,
            }
            .detect_change(rng, &new_instr)?;
            info!("Final change: {:?} in {}ms", change, start.elapsed().as_millis());
            bit_changes.push(change);
        }

        // Sort all changes to make sure they (read: the locations stored in the change) are identical if we end up comparing them
        for change in bit_changes.iter_mut() {
            change.sort();
        }

        Ok((bit_changes, use_trap_flag))
    }

    pub fn infer<'a>(
        o: &'a mut O, cache: &'a C, original_dataflows: &'a Dataflows<A, ()>,
    ) -> Result<Encoding<A, ()>, EncodingError<A>> {
        info!("Inferring encoding for {}", original_dataflows);
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let mappable_area = o.mappable_area();
        let state_gen = StateGen::new(&original_dataflows.addresses, &mappable_area)?;
        let threshold_values = cache.infer_threshold_values(o, original_dataflows, &state_gen);

        let mut builder = EncodingAnalysis {
            o,
            cache,
            dataflows: original_dataflows,
            threshold_values,
            found_dependent_bytes: original_dataflows.found_dependent_bytes,
        };

        let mut dataflows = original_dataflows.clone();
        let (mut bit_changes, use_trap_flag) = builder.bit_changes(&mut rng)?;
        cleanup_bit_changes(&mut bit_changes);

        info!("Bit changes = {:?}", bit_changes);

        let errors = bit_changes
            .iter()
            .map(|change| matches!(change, Change::Error))
            .collect::<Vec<_>>();

        let (bits, parts) = create_parts(&mut dataflows, &bit_changes);

        info!("Filling parts: {:?} {:?}", bits, parts);

        let PartMappingFilling {
            mut parts,
            mut invalid_change_indices,
        } = builder.fill_part_mapping(&mut rng, parts, &bits)?;

        info!(
            "Invalid indices for {:X}: {:?}",
            dataflows.addresses.instr, invalid_change_indices
        );

        invalid_change_indices.sort();
        let mut n = 0;
        let mut remapping = Vec::new();
        for index in 0..parts.len() {
            if !invalid_change_indices.contains(&index) {
                remapping.push(Some(n));
                n += 1;
            } else {
                remapping.push(None);
            }
        }

        for &index in invalid_change_indices.iter().rev() {
            parts.remove(index);
        }

        let mut bits = bits;
        for (bit_index, bit) in bits.iter_mut().enumerate() {
            match bit {
                Bit::Part(n) => {
                    if let Some(remapped) = remapping[*n] {
                        *n = remapped;
                    } else {
                        *bit = Bit::Fixed(dataflows.addresses.instr.nth_bit_from_right(bit_index));
                    }
                },
                Bit::Fixed(_) | Bit::DontCare => {},
            }
        }

        for part in parts.iter_mut() {
            match &mut part.mapping {
                PartMapping::Imm {
                    locations, ..
                } => {
                    for location in locations.iter_mut() {
                        // Adjust locations such that they refer to the correct entry again
                        let (inputs, input_index) = match location {
                            FlowInputLocation::InputForOutput {
                                output_index,
                                input_index,
                            } => (&dataflows.outputs[*output_index].inputs, input_index),
                            FlowInputLocation::MemoryAddress {
                                memory_index,
                                input_index,
                            } => (&dataflows.addresses.memory[*memory_index].inputs, input_index),
                        };

                        let before = inputs
                            .iter()
                            .take(*input_index)
                            .filter(|i| matches!(i, Source::Imm(n) if invalid_change_indices.contains(n)))
                            .count();

                        *input_index -= before;
                    }
                },
                PartMapping::Register {
                    locations, ..
                } => {
                    for location in locations.iter_mut() {
                        // Adjust locations such that they refer to the correct entry again
                        let (inputs, input_index) = match location {
                            FlowValueLocation::InputForOutput {
                                output_index,
                                input_index,
                            } => (&dataflows.outputs[*output_index].inputs, input_index),
                            FlowValueLocation::MemoryAddress {
                                memory_index,
                                input_index,
                            } => (&dataflows.addresses.memory[*memory_index].inputs, input_index),
                            FlowValueLocation::Output(_) => continue,
                        };

                        let before = inputs
                            .iter()
                            .take(*input_index)
                            .filter(|i| matches!(i, Source::Imm(n) if invalid_change_indices.contains(n)))
                            .count();

                        *input_index -= before;
                    }
                },
                PartMapping::MemoryComputation {
                    ..
                } => continue,
            };
        }

        let mut memory_offsets = vec![None; dataflows.addresses.memory.len()];
        for (part_index, part) in parts.iter().enumerate() {
            if let PartMapping::Imm {
                locations,
                mapping: Some(MappingOrBitOrder::BitOrder(bit_order)),
                ..
            } = &part.mapping
            {
                for location in locations.iter() {
                    if let FlowInputLocation::MemoryAddress {
                        memory_index, ..
                    } = location
                    {
                        let expected_offset = bits
                            .iter()
                            .enumerate()
                            .filter(|(_, bit)| bit == &&Bit::Part(part_index))
                            .zip(bit_order.iter())
                            .map(|((index, _), order)| (order, dataflows.addresses.instr.nth_bit_from_right(index) as u64))
                            .fold(0, |acc: u64, (bit, bit_value)| {
                                acc.wrapping_add(match bit {
                                    ImmBitOrder::Positive(bit) => bit_value << bit,
                                    ImmBitOrder::Negative(bit) => (!(bit_value << bit)).wrapping_add(1),
                                })
                            }) as i64;
                        let base_offset = original_dataflows.addresses.memory[*memory_index].calculation.offset;

                        info!(
                            "For {:?} {:?} Offset difference: 0x{:X} vs 0x{:X}",
                            part, location, expected_offset, base_offset
                        );
                        memory_offsets[*memory_index] = Some(
                            memory_offsets[*memory_index]
                                .unwrap_or(0i64)
                                .wrapping_add(base_offset.wrapping_sub(expected_offset)),
                        );

                        // TODO: Verify this memory offset with some more dataflows. Preferrably the dataflows we already generated before (to detect changes / enumerate registers / etc.)?
                    }
                }
            }
        }

        // Remove Imms from dataflows as well
        dataflows = dataflows.map(
            dataflows.addresses.instr,
            |_, source| match source {
                Source::Imm(n) => remapping[*n].map(Source::Imm),
                other => Some(*other),
            },
            |memory_index, calculation| {
                let mut new = *calculation;
                if let Some(offset) = memory_offsets[memory_index] {
                    new.offset = offset;
                }

                Some(new)
            },
        );

        let mut encoding = Encoding::<A, ()> {
            bits,
            errors,
            dataflows,
            parts,
            write_ordering: Vec::new(),
        };
        encoding.dataflows.addresses.use_trap_flag = use_trap_flag;
        encoding.dataflows.found_dependent_bytes = builder.found_dependent_bytes;

        info!("Removing incorrect memory computations in {}", encoding);

        remove_incorrect_memory_computations(o, cache, &mut encoding);
        remove_useless_bits(&mut encoding);

        // First remove incorrect bits in parts, because we will also modify part values when
        // validating DontCare bits.
        let s = Instant::now();
        remove_incorrect_generalizations(o, &mut encoding);

        info!(
            "Removed incorrect generalizations in {}ms: {}",
            s.elapsed().as_millis(),
            encoding
        );

        remove_useless_bits(&mut encoding);

        if encoding.bits.iter().any(|b| matches!(b, Bit::DontCare)) {
            // Make sure the DontCare bits really don't make a difference
            DontCareValidator::new(original_dataflows).validate_dontcare(o, &mut encoding)?;
        }

        remove_useless_bits(&mut encoding);

        info!("Final encoding: {}", encoding);

        match encoding.integrity_check() {
            Ok(_) => (),
            Err(e) => panic!("Inferred encoding does not pass integrity check: {e}: {encoding}\n\n{encoding:?}"),
        }

        Ok(encoding)
    }
}

#[cfg(test)]
mod tests {
    use liblisa::encoding::bitpattern::ImmBitOrder;
    use test_log::test;

    use crate::encoding::guess_bit_order;

    #[test]
    pub fn test_guess_bit_order_fwd() {
        let order = (0..32)
            .map(|n| n % 8 + (24 - (n / 8 * 8)))
            .enumerate()
            .map(|(index, n)| (index, if (24..28).contains(&index) { None } else { Some(n) }))
            .collect::<Vec<_>>();
        println!("Order: {order:?}");

        assert_eq!(guess_bit_order(order.clone(), 24).unwrap(), ImmBitOrder::Positive(0));
        assert_eq!(guess_bit_order(order.clone(), 25).unwrap(), ImmBitOrder::Positive(1));
        assert_eq!(guess_bit_order(order.clone(), 26).unwrap(), ImmBitOrder::Positive(2));
        assert_eq!(guess_bit_order(order, 27).unwrap(), ImmBitOrder::Positive(3));
    }

    #[test]
    pub fn test_guess_bit_order_bwd() {
        let order = (0..32)
            .map(|n| n % 8 + (24 - (n / 8 * 8)))
            .enumerate()
            .map(|(index, n)| (index, if (0..16).contains(&index) { None } else { Some(n) }))
            .collect::<Vec<_>>();
        println!("Order: {order:?}");

        assert_eq!(guess_bit_order(order.clone(), 0).unwrap(), ImmBitOrder::Positive(24));
        assert_eq!(guess_bit_order(order.clone(), 1).unwrap(), ImmBitOrder::Positive(25));
        assert_eq!(guess_bit_order(order.clone(), 7).unwrap(), ImmBitOrder::Positive(31));
        assert_eq!(guess_bit_order(order.clone(), 8).unwrap(), ImmBitOrder::Positive(16));
        assert_eq!(guess_bit_order(order, 9).unwrap(), ImmBitOrder::Positive(17));
    }
}
