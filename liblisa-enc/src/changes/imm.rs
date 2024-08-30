use std::cmp::Ordering;
use std::collections::HashMap;
use std::marker::PhantomData;

use liblisa::arch::Register;
use liblisa::encoding::dataflows::{Dataflow, Dest, Size, Source};
use liblisa::oracle::{MappableArea, OracleError};
use liblisa::state::random::{randomized_bytes_into_buffer, randomized_value};
use liblisa::state::{Location, SystemState, SystemStateIoPair};
use liblisa::value::{AsValue, MutValue, OwnedValue, Value};
use log::{debug, info, trace};
use serde::de::Visitor;
use serde::ser::SerializeSeq;
use serde::{Deserialize, Serialize, Serializer};

use super::*;

pub(crate) struct ImmAnalysis<'a, A: Arch, O: Oracle<A>> {
    pub(crate) o: &'a mut O,
    pub(crate) dataflows: &'a Dataflows<A, ()>,
    pub(crate) state_gen: &'a StateGen<'a, A, O::MappableArea>,
}

impl<'a, A: Arch, O: Oracle<A>> ImmAnalysis<'a, A, O> {
    fn check_dataflow_observation(
        &mut self, index: usize, output: &Dataflow<A, ()>, mut current_change: Change<A>, left: SystemStateIoPair<A>,
        right: SystemStateIoPair<A>,
    ) -> Change<A> {
        let state_old = left.state_in;
        let state_new = right.state_in;
        let left = left.state_out;
        let right = right.state_out;

        let left_loc = &output.target;
        let right_loc = match &mut current_change {
            Change::Register {
                locations,
                from,
                to,
            } if locations.contains(&ChangeLocation::Output(index)) => {
                // If locations contains this output, the register should match
                assert_eq!(left_loc, &Location::Reg(*from));
                Dest::Reg(*to, left_loc.size())
            },
            _ => *left_loc,
        };

        let left_val = left.get_dest(left_loc);
        let right_val = right.get_dest(&right_loc);
        trace!(
            "Comparing {:?} vs {:?} ==> {:?} vs {:?}",
            left_loc, right_loc, left_val, right_val
        );
        if left_val != right_val {
            let location = index;
            match &mut current_change {
                Change::ValueImm {
                    output_indexes: ref mut locations,
                    ..
                } => {
                    if !locations.contains(&location) {
                        locations.push(location);
                    }
                },
                Change::MemoryOffset {
                    locations, ..
                } => {
                    let location = FlowOutputLocation::Output(index);
                    if !locations.contains(&location) {
                        locations.push(location);
                    }
                },
                Change::None => {
                    current_change = Change::ValueImm {
                        output_indexes: vec![location],
                    };
                },
                change => {
                    debug!(
                        "Found difference: {:?} vs {:?} ==> {:?} vs {:?}",
                        left_loc, right_loc, left_val, right_val
                    );
                    debug!(
                        "Detected an imm value between {:?} and {:?} that we can't handle because we're already tracking another change: {:?}; Inputs were: {:X?} {:X?}; Outputs were: {:X?} {:X?}",
                        left_loc, right_loc, change, state_old, state_new, left, right
                    );
                    return Change::Invalid;
                },
            }
        }

        current_change
    }

    fn verify_dataflow_imm_base(
        &mut self, state_new: &SystemState<A>, mut current_change: Change<A>,
    ) -> Result<Change<A>, RandomizationError> {
        match self.state_gen.remap(state_new) {
            Ok(mut state_old) => {
                match &current_change {
                    Change::Register {
                        locations,
                        from,
                        to,
                    } if locations.iter().any(ChangeLocation::is_input) => {
                        state_old.set_location(&Location::Reg(*from), state_new.location(&Location::Reg(*to)));
                    },
                    _ => (),
                };

                if self.state_gen.adapt(&mut state_old, false) {
                    let [(_, base_result), (_, new_result)] = self.o.batch_observe([&state_old, state_new]);

                    trace!(
                        "Trying to find an imm value with inputs: {:X?} {:X?}; Outputs: {:X?} {:X?}",
                        state_old, state_new, base_result, new_result
                    );

                    // We compare the two results we got. One from instr and one from new_instr. If the results aren't equal, this might be an immediate value.
                    // This happens often enough to be important to check; For example, the encoding for add al, al contains a bit that swaps the operand order. This does not give different results, so we don't want to identify it as an immediate value.
                    match (base_result, new_result) {
                        (Ok(left), Ok(right)) => {
                            // Check outputs
                            for (index, output) in self.dataflows.output_dataflows().enumerate() {
                                if output.unobservable_external_inputs {
                                    continue;
                                }

                                current_change = self.check_dataflow_observation(
                                    index,
                                    output,
                                    current_change,
                                    SystemStateIoPair {
                                        state_in: &state_old,
                                        state_out: &left,
                                    },
                                    SystemStateIoPair {
                                        state_in: state_new,
                                        state_out: &right,
                                    },
                                );
                                if current_change.is_invalid_or_error() {
                                    return Ok(current_change);
                                }
                            }
                        },
                        // TODO: Should these errors be equal?
                        (Err(_e1), Err(_e2)) => {},
                        // Changing of an immediate value might cause a computation error, but not sure.
                        // Should just hope for another case where both results are Ok(_)
                        (Ok(_), Err(OracleError::ComputationError)) | (Err(OracleError::ComputationError), Ok(_)) => {},
                        // We might get a general fault because of alignment.
                        (Ok(_), Err(OracleError::GeneralFault)) | (Err(OracleError::GeneralFault), Ok(_)) => {},
                        (Err(OracleError::MultipleInstructionsExecuted), _)
                        | (_, Err(OracleError::MultipleInstructionsExecuted)) => {
                            return Err(RandomizationError::OracleError(OracleError::MultipleInstructionsExecuted))
                        },
                        (a, b) => {
                            debug!(
                                "Imm value check failed because of inconsistent output: {:X?} vs {:X?} on: {:X?} vs {:X?}",
                                a, b, state_old, state_new
                            );
                            return Ok(Change::Invalid);
                        },
                    }
                }
            },
            Err(e) => {
                trace!("find_dataflow_imm remap failed: {}", e);
            },
        }

        // TODO: Maybe change None -> Invalid if we were not able to do any observations?

        Ok(current_change)
    }

    // TODO: This function will incorrectly report 'No immediate value' if all adapts() fail. It would be nicer to have a separate ImmError, which could fold in to adjacent Imms if there are any, or become an Invalid if there are none. This does not seem to happen very often in practice, so it's not implemented for now.
    /// Some outputs have an "abrupt" value change. Rather than slowly changing over time, they switch from one value to another at a specific point.
    /// A good example are output flags in a comparison. An overflow flag will switch from 0 to 1 at one specific point.
    /// It can sometimes be hard to find random states that get close to this "edge".
    /// We need to find this edge to find some immediate values. For example, imagine we only found states where:
    ///
    /// 1) RAX = 100
    /// 2) RAX = 500
    /// 3) RAX = 721
    ///
    /// Given two instructions cmp RAX, 724 and cmp RAX, 725, we would conclude that there is no difference given the 3 examples we found.
    ///
    /// The threshold values represent the cases where the base instruction switched values (i.e. 724 and 725 in the example).
    /// We're going to apply those threshold values to the new instruction, and check to make sure it still functions the same.
    fn find_dataflow_imm_internal<R: Rng>(
        &mut self, rng: &mut R, new_state_gen: &StateGen<'a, A, O::MappableArea>, new_dataflows: &Dataflows<A, ()>,
        threshold_values: &ThresholdValues<A>, mut current_change: Change<A>,
    ) -> Result<Change<A>, RandomizationError> {
        let base_accesses = &self.dataflows.addresses;
        debug_assert_eq!(base_accesses.memory.len(), new_state_gen.accesses.memory.len());
        for _ in 0..1_000 {
            let state_new = new_state_gen.randomize_new(rng)?;
            current_change = self.verify_dataflow_imm_base(&state_new, current_change)?;

            if current_change.is_invalid_or_error() {
                return Ok(current_change);
            }
        }

        for (output_index, flow) in self.dataflows.output_dataflows().enumerate() {
            // We're going to manually generate the destination in the dataflow accurding to the current_change.
            // We'll keep the original size of the old target.
            // This way, we make sure to evaluate all source bytes that will end up in the dataflow.
            // If we've permitted sources or destinations with different sizes, we'll consider any imm values that we find to be invalid.
            let old_dest = flow.target;
            let new_dest = match (&current_change, &old_dest) {
                (
                    Change::Register {
                        locations,
                        from,
                        to,
                    },
                    Dest::Reg(reg, size),
                ) if locations.contains(&ChangeLocation::Output(output_index)) => {
                    assert_eq!(from, reg);
                    Dest::Reg(*to, *size)
                },
                (Change::Multiple(_), _) => unreachable!(),
                (
                    Change::Invalid
                    | Change::Error
                    | Change::UnknownMemoryError {
                        ..
                    },
                    _,
                ) => return Ok(current_change),
                (_, target) => *target,
            };

            info!("Checking old_dest={:?}, new_dest={:?}", old_dest, new_dest);
            'next: for old_source in flow.inputs.iter() {
                let values = threshold_values
                    .threshold_values
                    .get(&ThresholdValueKey(old_dest, *old_source));
                for threshold_value in values.iter().flat_map(|v| v.iter()) {
                    let base_state = self.state_gen.randomize_new(rng)?;
                    let old_state_in = {
                        let mut s = base_state.clone();
                        for (input, value) in flow.inputs.iter().zip(threshold_value.base_inputs.iter()) {
                            if input == old_source {
                                s.set_dest(&(*input).unwrap_dest(), &threshold_value.new_value.as_value());
                            } else {
                                s.set_dest(&(*input).unwrap_dest(), &value.as_value());
                            }
                        }

                        if !self.state_gen.adapt(&mut s, false) {
                            continue;
                        }

                        s
                    };

                    let new_state_in = {
                        let mut s = base_state.clone();
                        s.memory_mut()
                            .get_mut(0)
                            .modify_data(|data| data.copy_from_slice(new_dataflows.instr().bytes()));

                        let mut modified = Vec::new();
                        for (input_index, (input, value)) in
                            flow.inputs.iter().zip(threshold_value.base_inputs.iter()).enumerate()
                        {
                            let new_input = match (&current_change, input) {
                                (
                                    Change::Register {
                                        locations,
                                        from,
                                        to,
                                    },
                                    Source::Dest(Dest::Reg(reg, size)),
                                ) if locations.contains(&ChangeLocation::InputForOutput {
                                    output_index,
                                    input_index,
                                }) =>
                                {
                                    assert_eq!(from, reg);
                                    if to.is_zero() {
                                        // TODO: Cannot change RIZ
                                        continue
                                    }

                                    Source::Dest(Dest::Reg(*to, *size))
                                },
                                (Change::Multiple(_), _) => unreachable!(),
                                (
                                    Change::Invalid
                                    | Change::Error
                                    | Change::UnknownMemoryError {
                                        ..
                                    },
                                    _,
                                ) => return Ok(current_change),
                                (_, source) => *source,
                            };

                            let new_value = if input == old_source {
                                threshold_value.new_value.as_value()
                            } else {
                                value.as_value()
                            };

                            trace!(
                                "Input {input:?} at output_index={output_index},input_index={input_index} translated with {current_change:?} = {new_input:?}"
                            );
                            if modified.contains(&new_input) {
                                if s.get_dest(&new_input.unwrap_dest()) != new_value {
                                    debug!(
                                        "Cannot check {:X?} because input {:X?} would be set multiple times",
                                        threshold_value.base_inputs, new_input
                                    );
                                    continue 'next;
                                }
                            } else {
                                modified.push(new_input);
                            }

                            s.set_dest(&new_input.unwrap_dest(), &new_value);
                        }

                        if !new_state_gen.adapt(&mut s, true) {
                            continue;
                        }

                        s
                    };

                    let [(old_state_in, old_state_out), (new_state_in, new_state_out)] =
                        self.o.batch_observe([old_state_in, new_state_in]);
                    if let (Ok(old_state_out), Ok(new_state_out)) = (old_state_out, new_state_out) {
                        trace!(
                            "Compared {:?} with {:?} resulting in {:?} vs {:?}",
                            old_state_in, new_state_in, old_state_out, new_state_out
                        );
                        let old_value = old_state_out.get_dest(&old_dest);
                        let new_value = new_state_out.get_dest(&new_dest);
                        if old_value != new_value {
                            match &mut current_change {
                                Change::ValueImm {
                                    output_indexes: ref mut locations,
                                    ..
                                } => {
                                    if !locations.contains(&output_index) {
                                        locations.push(output_index);
                                    }
                                },
                                Change::MemoryOffset {
                                    locations, ..
                                } => {
                                    let location = FlowOutputLocation::Output(output_index);
                                    if !locations.contains(&location) {
                                        locations.push(location);
                                    }
                                },
                                Change::None => {
                                    current_change = Change::ValueImm {
                                        output_indexes: vec![output_index],
                                    };
                                },
                                change => {
                                    debug!(
                                        "Found difference: old_dest={:?} vs new_dest={:?} ==> {:?} vs {:?}",
                                        old_dest, new_dest, old_value, new_value
                                    );
                                    debug!(
                                        "Detected an imm value between {:?} and {:?} that we can't handle because we're already tracking another change: {:?}; Inputs were: old_in={:X?} new_in={:X?}; Outputs were: old_out={:X?} new_out={:X?}",
                                        old_dest, new_dest, change, old_state_in, new_state_in, old_state_out, new_state_out
                                    );

                                    return Ok(Change::Invalid);
                                },
                            }
                        }
                    }
                }
            }
        }

        Ok(current_change)
    }

    pub(crate) fn find_dataflow_imm<R: Rng>(
        &mut self, rng: &mut R, new_state_gen: &StateGen<'a, A, O::MappableArea>, new_dataflows: &Dataflows<A, ()>,
        threshold_values: &ThresholdValues<A>, mut current_change: Change<A>,
    ) -> Result<Change<A>, RandomizationError> {
        if let Change::Multiple(items) = &mut current_change {
            let mut valid_changes = Vec::new();
            for (index, change) in items.iter_mut().enumerate() {
                info!("Change {index} = {change:?}");

                let is_guaranteed_invalid = valid_changes.iter().any(|valid| match (valid, &change) {
                    (
                        Change::Register {
                            locations: locations_a,
                            from: from_a,
                            to: to_a,
                        },
                        Change::Register {
                            locations: locations_b,
                            from: from_b,
                            to: to_b,
                        },
                    ) if from_a == from_b && to_a == to_b => {
                        locations_a.iter().any(|loc| !locations_b.contains(loc))
                            && locations_b.iter().all(|loc| locations_a.contains(loc))
                    },
                    _ => false,
                });

                if is_guaranteed_invalid {
                    *change = Change::Invalid;
                    info!("Discarding {index}");
                } else {
                    *change =
                        self.find_dataflow_imm_internal(rng, new_state_gen, new_dataflows, threshold_values, change.clone())?;
                    info!("Result {index} = {change:?}");
                }

                if !change.is_invalid_or_error() {
                    valid_changes.push(change.clone());
                }
            }

            current_change.normalize();
            Ok(current_change)
        } else {
            self.find_dataflow_imm_internal(rng, new_state_gen, new_dataflows, threshold_values, current_change)
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
struct ThresholdValue {
    base_inputs: Vec<OwnedValue>,
    new_value: OwnedValue,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(bound(serialize = "", deserialize = ""))]
struct ThresholdValueKey<A: Arch>(Dest<A>, Source<A>);

/// A set of I/O examples for a destination, that identify the specific behavior of that destination.
///
/// For example, if a destination is the result of a `x < y` comparison, the I/O examples would contain (at least) one example where `x < y`, one example where `x + 1 = y`, one example where `x = y` and one example where `!(x < y)`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ThresholdValues<A: Arch> {
    threshold_values: HashMap<ThresholdValueKey<A>, Vec<ThresholdValue>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum ThresholdValueRow {
    Bytes(Vec<Vec<u8>>),
    Nums(Vec<u64>),
}

impl ThresholdValueRow {
    pub fn get(&self, index: usize) -> OwnedValue {
        match self {
            ThresholdValueRow::Bytes(v) => OwnedValue::Bytes(v[index].clone()),
            ThresholdValueRow::Nums(v) => OwnedValue::Num(v[index]),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            ThresholdValueRow::Bytes(v) => v.len(),
            ThresholdValueRow::Nums(v) => v.len(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ThresholdValuesByRow {
    rows: Vec<ThresholdValueRow>,
    new_value: ThresholdValueRow,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(serialize = "", deserialize = ""))]
struct SerializedThresholdValueEntry<A: Arch>(ThresholdValueKey<A>, ThresholdValuesByRow);

impl<A: Arch> Serialize for ThresholdValues<A>
where
    ThresholdValueKey<A>: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut list = serializer.serialize_seq(Some(self.threshold_values.len()))?;
        for (k, v) in &self.threshold_values {
            let by_row = ThresholdValuesByRow {
                rows: v
                    .first()
                    .map(|t| {
                        t.base_inputs
                            .iter()
                            .enumerate()
                            .map(|(index, val)| match val {
                                OwnedValue::Num(_) => {
                                    ThresholdValueRow::Nums(v.iter().map(|t| t.base_inputs[index].unwrap_num()).collect())
                                },
                                OwnedValue::Bytes(_) => ThresholdValueRow::Bytes(
                                    v.iter().map(|t| t.base_inputs[index].unwrap_bytes().to_vec()).collect(),
                                ),
                            })
                            .collect()
                    })
                    .unwrap_or_else(Vec::new),
                new_value: v
                    .first()
                    .map(|t| match t.new_value {
                        OwnedValue::Num(_) => ThresholdValueRow::Nums(v.iter().map(|t| t.new_value.unwrap_num()).collect()),
                        OwnedValue::Bytes(_) => {
                            ThresholdValueRow::Bytes(v.iter().map(|t| t.new_value.unwrap_bytes().to_vec()).collect())
                        },
                    })
                    .unwrap_or_else(|| ThresholdValueRow::Nums(Vec::new())),
            };

            list.serialize_element(&SerializedThresholdValueEntry(k.clone(), by_row))?;
        }
        list.end()
    }
}

struct ThresholdValuesVisitor<A: Arch>(PhantomData<A>);

impl<'de, A: Arch> Visitor<'de> for ThresholdValuesVisitor<A> {
    type Value = ThresholdValues<A>;

    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
        S: serde::de::SeqAccess<'de>,
    {
        let mut threshold_values = ThresholdValues::default();

        while let Some(SerializedThresholdValueEntry(k, v)) = seq.next_element()? {
            let values = (0..v.new_value.len())
                .map(|index| ThresholdValue {
                    base_inputs: v.rows.iter().map(|row| row.get(index)).collect(),
                    new_value: v.new_value.get(index),
                })
                .collect();

            threshold_values.threshold_values.insert(k, values);
        }

        Ok(threshold_values)
    }

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a list of ThresholdValues")
    }
}

impl<'de, A: Arch> Deserialize<'de> for ThresholdValues<A> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_seq(ThresholdValuesVisitor(PhantomData))
    }
}

/// An efficent JSON representation of [`ThresholdValues`].
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(bound(serialize = "", deserialize = ""))]
pub struct JsonThresholdValue<A: Arch>(ThresholdValueKey<A>, Vec<ThresholdValue>);

/// A collection of [`JsonThresholdValue`]s.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
#[serde(bound(serialize = "", deserialize = ""))]
pub struct JsonThresholdValues<A: Arch> {
    threshold_values: Vec<JsonThresholdValue<A>>,
}

impl<A: Arch> JsonThresholdValues<A> {
    pub fn into_threshold_values(self) -> ThresholdValues<A> {
        ThresholdValues {
            threshold_values: self
                .threshold_values
                .into_iter()
                .map(|JsonThresholdValue(key, value)| (key, value))
                .collect(),
        }
    }
}

struct JsonThresholdValuesVisitor<A: Arch>(PhantomData<A>);

impl<'de, A: Arch> Visitor<'de> for JsonThresholdValuesVisitor<A> {
    type Value = JsonThresholdValues<A>;

    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
        S: serde::de::SeqAccess<'de>,
    {
        let mut threshold_values = JsonThresholdValues::default();

        while let Some(v) = seq.next_element()? {
            threshold_values.threshold_values.push(v);
        }

        Ok(threshold_values)
    }

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a list of JsonThresholdValues")
    }
}

impl<'de, A: Arch> Deserialize<'de> for JsonThresholdValues<A> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_seq(JsonThresholdValuesVisitor(PhantomData))
    }
}

impl<A: Arch> ThresholdValues<A> {
    fn middle(low: &OwnedValue, high: &OwnedValue, little_endian: bool) -> Option<OwnedValue> {
        match (low, high) {
            (OwnedValue::Num(low), OwnedValue::Num(high)) => {
                let (low, high) = if little_endian {
                    (low.swap_bytes(), high.swap_bytes())
                } else {
                    (*low, *high)
                };

                if low + 1 < high {
                    let result = low + (high - low) / 2;
                    Some(OwnedValue::Num(if little_endian { result.swap_bytes() } else { result }))
                } else {
                    // Less than 2 difference
                    None
                }
            },
            (OwnedValue::Bytes(a), OwnedValue::Bytes(b)) => {
                if little_endian {
                    assert_eq!(a.len(), b.len());

                    // Compute the sum of the two arrays
                    let mut carry = 0;
                    let mut result = a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| {
                            let sum = u16::from(*a) + u16::from(*b) + carry;
                            carry = sum >> 8;

                            sum as u8
                        })
                        .collect::<Vec<_>>();

                    // Divide by two
                    for b in result.iter_mut().rev() {
                        let new_b = (carry << 7) as u8 | (*b >> 1);
                        carry = *b as u16 & 1;
                        *b = new_b;
                    }

                    if &result == a || &result == b {
                        None
                    } else {
                        Some(OwnedValue::Bytes(result))
                    }
                } else {
                    assert_eq!(a.len(), b.len());

                    // Compute the sum of the two arrays
                    let mut carry = 0;
                    let mut result = a
                        .iter()
                        .rev()
                        .zip(b.iter().rev())
                        .map(|(a, b)| {
                            let sum = u16::from(*a) + u16::from(*b) + carry;
                            carry = sum >> 8;

                            sum as u8
                        })
                        .collect::<Vec<_>>();

                    // Do the last reverse separately, so that the carry is computed the right way in the iterator.
                    result.reverse();

                    // Divide by two
                    for b in result.iter_mut() {
                        let new_b = (carry << 7) as u8 | (*b >> 1);
                        carry = *b as u16 & 1;
                        *b = new_b;
                    }

                    if &result == a || &result == b {
                        None
                    } else {
                        Some(OwnedValue::Bytes(result))
                    }
                }
            },
            (OwnedValue::Num(_), OwnedValue::Bytes(_)) | (OwnedValue::Bytes(_), OwnedValue::Num(_)) => unreachable!(),
        }
    }

    fn less_than(a: &OwnedValue, b: &OwnedValue, little_endian: bool) -> bool {
        match (a, b) {
            (OwnedValue::Num(a), OwnedValue::Num(b)) => {
                if little_endian {
                    a.swap_bytes() < b.swap_bytes()
                } else {
                    a < b
                }
            },
            (OwnedValue::Bytes(a), OwnedValue::Bytes(b)) => {
                if little_endian {
                    for (a, b) in a.iter().rev().zip(b.iter().rev()) {
                        match a.cmp(b) {
                            Ordering::Less => return true,
                            Ordering::Greater => return false,
                            _ => (),
                        }
                    }

                    false
                } else {
                    for (a, b) in a.iter().zip(b.iter()) {
                        match a.cmp(b) {
                            Ordering::Less => return true,
                            Ordering::Greater => return false,
                            _ => (),
                        }
                    }

                    false
                }
            },
            _ => unreachable!(),
        }
    }

    fn infer_single_threshold<O: Oracle<A>, M: MappableArea>(
        oracle: &mut O, state_gen: &StateGen<A, M>, source: &Dest<A>, dest: &Dest<A>,
        (base_a, base_b): (&SystemState<A>, &SystemState<A>), (out_a, out_b): (&Value<'_>, &Value<'_>), little_endian: bool,
    ) -> Option<OwnedValue> {
        let in_a = base_a.get_dest(source).to_owned_value();
        let in_b = base_b.get_dest(source).to_owned_value();

        let (mut low, mut high, out_low, _out_high) = if Self::less_than(&in_a, &in_b, little_endian) {
            (in_a, in_b, out_a, out_b)
        } else {
            (in_b, in_a, out_b, out_a)
        };

        trace!(
            "low = {:X?}, high = {:X?}, out_low = {:X?}, out_high = {:X?}",
            low, high, out_low, _out_high
        );

        while let Some(mid) = Self::middle(&low, &high, little_endian) {
            trace!("mid = {:X?} (between {:X?} and {:X?})", mid, low, high);
            let state = {
                let mut s = base_a.clone();
                s.set_dest(source, &mid.as_value());
                if !state_gen.adapt(&mut s, false) {
                    return None;
                }

                s
            };

            if let Ok(state_out) = oracle.observe(&state) {
                let d = state_out.get_dest(dest);
                trace!("With mid={:X?}, output = {:X?}", mid, d);
                if &d != out_low {
                    high = mid;
                } else {
                    low = mid;
                }
            } else {
                return None;
            }
        }

        Some(high)
    }

    pub fn infer<O: Oracle<A>, M: MappableArea, R: Rng>(
        oracle: &mut O, rng: &mut R, state_gen: &StateGen<A, M>, dataflows: &Dataflows<A, ()>,
    ) -> ThresholdValues<A> {
        let mut values: HashMap<ThresholdValueKey<A>, Vec<ThresholdValue>> = HashMap::new();

        for output in dataflows.output_dataflows() {
            let dest = &output.target;
            let dest_size = dest.size();
            for byte in 0..dest_size.num_bytes() {
                let single_dest_byte = dest.with_size(Size::new(dest_size.start_byte + byte, dest_size.start_byte + byte));
                for source in output.inputs.iter() {
                    let source = (*source).unwrap_dest();
                    for _ in 0..1000 {
                        let state_a = state_gen.randomize_new(rng).unwrap();
                        let state_b = {
                            let mut s = state_a.clone();
                            s.modify_dest(&source, |value| match value {
                                MutValue::Num(n) => {
                                    if let Some(mask) = source.mask() {
                                        *n = rng.gen::<u64>() & mask
                                    } else {
                                        *n = randomized_value(rng)
                                    }
                                },
                                MutValue::Bytes(b) => randomized_bytes_into_buffer(rng, b),
                            });

                            if !state_gen.adapt(&mut s, false) {
                                continue
                            }

                            s
                        };

                        if let (Ok(output_a), Ok(output_b)) = (oracle.observe(&state_a), oracle.observe(&state_b)) {
                            let val_a = output_a.get_dest(&single_dest_byte);
                            let val_b = output_b.get_dest(&single_dest_byte);
                            if val_a != val_b {
                                for little_endian in [false, true] {
                                    let threshold = Self::infer_single_threshold(
                                        oracle,
                                        state_gen,
                                        &source,
                                        &single_dest_byte,
                                        (&state_a, &state_b),
                                        (&val_a, &val_b),
                                        little_endian,
                                    );
                                    trace!(
                                        "Number threshold (little_endian={}) found for {:X?} -> {:X?}: {:X?}",
                                        little_endian, source, single_dest_byte, threshold
                                    );

                                    if let Some(threshold) = threshold {
                                        values
                                            .entry(ThresholdValueKey(*dest, Source::Dest(source)))
                                            .or_default()
                                            .push(ThresholdValue {
                                                base_inputs: output
                                                    .inputs
                                                    .iter()
                                                    .map(|input| state_a.get_dest(&(*input).unwrap_dest()).to_owned_value())
                                                    .collect(),
                                                new_value: threshold,
                                            });
                                    }
                                }
                            }
                        }
                    }

                    for _ in 0..10 {
                        let state_a = {
                            let mut s = state_gen.randomize_new(rng).unwrap();
                            s.modify_dest(&source, |value| match value {
                                MutValue::Num(n) => *n = 0,
                                MutValue::Bytes(b) => b.fill(0),
                            });

                            if !state_gen.adapt(&mut s, false) {
                                continue
                            }

                            s
                        };

                        for index in 0..source.size().num_bytes() * 8 {
                            let bit_to_set = 1u64.checked_shl(index as u32).unwrap_or(0);
                            if let Some(mask) = source.mask()
                                && bit_to_set & mask == 0
                            {
                                continue;
                            }

                            let state_b = {
                                let mut s = state_a.clone();
                                s.modify_dest(&source, |value| match value {
                                    MutValue::Num(n) => *n = bit_to_set,
                                    MutValue::Bytes(b) => b[index / 8] |= 1 << (index % 8),
                                });

                                if !state_gen.adapt(&mut s, false) {
                                    continue
                                }

                                s
                            };

                            let base_inputs = output
                                .inputs
                                .iter()
                                .map(|input| state_a.get_dest(&(*input).unwrap_dest()).to_owned_value())
                                .collect();
                            let new_value = state_b.get_dest(&source).to_owned_value();

                            trace!(
                                "Adding bit check for {:X?} -> {:X?}: {:X?} = {:X?}",
                                source, single_dest_byte, base_inputs, new_value
                            );

                            values
                                .entry(ThresholdValueKey(*dest, Source::Dest(source)))
                                .or_default()
                                .push(ThresholdValue {
                                    base_inputs,
                                    new_value,
                                });
                        }
                    }
                }
            }
        }

        ThresholdValues {
            threshold_values: values,
        }
    }
}

#[cfg(test)]
mod tests {
    use liblisa::arch::fake::FakeArch;
    use liblisa::encoding::dataflows::{Dest, Size, Source};
    use liblisa::value::OwnedValue;

    use super::{ThresholdValue, ThresholdValueKey};
    use crate::changes::imm::ThresholdValues;

    #[test]
    pub fn middle_num() {
        assert_eq!(
            ThresholdValues::<FakeArch>::middle(&OwnedValue::Num(0), &OwnedValue::Num(10), false),
            Some(OwnedValue::Num(5))
        );
        assert_eq!(
            ThresholdValues::<FakeArch>::middle(&OwnedValue::Num(100), &OwnedValue::Num(200), false),
            Some(OwnedValue::Num(150))
        );
    }

    #[test]
    pub fn middle_bytes() {
        assert_eq!(
            ThresholdValues::<FakeArch>::middle(
                &OwnedValue::Bytes(vec![0x5A, 0xBC, 0xDA, 0x1A]),
                &OwnedValue::Bytes(vec![0x5B, 0x68, 0x28, 0x1A]),
                false
            ),
            Some(OwnedValue::Bytes(vec![0x5B, 0x12, 0x81, 0x1A]))
        );

        assert_eq!(
            ThresholdValues::<FakeArch>::middle(
                &OwnedValue::Bytes(vec![0x1A, 0xDA, 0xBC, 0x5A]),
                &OwnedValue::Bytes(vec![0x1A, 0x28, 0x68, 0x5B]),
                true
            ),
            Some(OwnedValue::Bytes(vec![0x1A, 0x81, 0x12, 0x5B]))
        );
    }

    #[test]
    pub fn serialize_deserialize_json() {
        let values = ThresholdValues::<FakeArch> {
            threshold_values: [(
                ThresholdValueKey(Dest::Mem(0, Size::qword()), Source::Imm(0)),
                vec![
                    ThresholdValue {
                        base_inputs: vec![OwnedValue::Num(5), OwnedValue::Num(10), OwnedValue::Bytes(vec![1, 2, 3])],
                        new_value: OwnedValue::Bytes(vec![7]),
                    },
                    ThresholdValue {
                        base_inputs: vec![OwnedValue::Num(10), OwnedValue::Num(2), OwnedValue::Bytes(vec![7, 6, 5])],
                        new_value: OwnedValue::Bytes(vec![12]),
                    },
                    ThresholdValue {
                        base_inputs: vec![
                            OwnedValue::Num(0x1234321),
                            OwnedValue::Num(0),
                            OwnedValue::Bytes(vec![0, 0, 0]),
                        ],
                        new_value: OwnedValue::Bytes(vec![3]),
                    },
                ],
            )]
            .into_iter()
            .collect(),
        };

        let s = serde_json::to_string(&values).unwrap();
        let de_values = serde_json::from_str(&s).unwrap();

        assert_eq!(values, de_values);
    }

    #[test]
    pub fn serialize_deserialize_rmp() {
        let values = ThresholdValues::<FakeArch> {
            threshold_values: [(
                ThresholdValueKey(Dest::Mem(0, Size::qword()), Source::Imm(0)),
                vec![
                    // ThresholdValue {
                    //     base_inputs: vec![
                    //         OwnedValue::Num(5),
                    //         OwnedValue::Num(10),
                    //         OwnedValue::Bytes(vec![ 1, 2, 3 ])
                    //     ],
                    //     new_value: OwnedValue::Bytes(vec![ 7 ]),
                    // },
                    // ThresholdValue {
                    //     base_inputs: vec![
                    //         OwnedValue::Num(10),
                    //         OwnedValue::Num(2),
                    //         OwnedValue::Bytes(vec![ 7, 6, 5 ])
                    //     ],
                    //     new_value: OwnedValue::Bytes(vec![ 12 ]),
                    // },
                    // ThresholdValue {
                    //     base_inputs: vec![
                    //         OwnedValue::Num(0x1234321),
                    //         OwnedValue::Num(0),
                    //         OwnedValue::Bytes(vec![ 0, 0, 0 ])
                    //     ],
                    //     new_value: OwnedValue::Bytes(vec![ 3 ]),
                    // },
                ],
            )]
            .into_iter()
            .collect(),
        };

        let s = rmp_serde::to_vec(&values).unwrap();
        let de_values = rmp_serde::from_slice(&s).unwrap();

        assert_eq!(values, de_values);
    }
}
