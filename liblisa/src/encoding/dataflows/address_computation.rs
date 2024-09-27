//! Address computations.

use std::cmp::Ordering;
use std::fmt::{Debug, Display};

use log::warn;
use serde::{Deserialize, Serialize};

use crate::arch::{Arch, CpuState};
use crate::encoding::dataflows::{Inputs, Source};
use crate::semantics::Computation;
use crate::state::SystemState;
use crate::value::{AsValue, OwnedValue, Value};

/// An address computation of a memory access.
///
/// The address computation is a sum of shift-then-multiplied values.
/// For example: `A + (B >> 1) * 4 + offset`
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, Hash)]
pub struct AddressComputation {
    /// The offsets that is added to the computation.
    pub offset: i64,

    /// The terms in the computation.
    /// There are always four terms, but some terms may be effectively 0.
    pub terms: [AddrTerm; 4],
}

/// The values for the shift-then-multiply operation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, Hash)]
pub struct AddrTermShift {
    right: u8,
    mult: u8,
}

impl AddrTermShift {
    /// Applies the shift-then-multiply operation to `val`.
    #[inline]
    pub fn apply(self, val: u64) -> u64 {
        ((val as i64 >> self.right).wrapping_mul(self.mult as i64)) as u64
    }

    /// Returns the number of bits by which this operation shifts right.
    pub fn right(&self) -> u8 {
        self.right
    }

    /// Returns the value
    pub fn mult(&self) -> u8 {
        self.mult
    }
}

/// The size of a term in the address computation.
/// Also specifies whether the term should be interpreted as signed or unsigned after cropping it to the right size.
///
/// The variants are named as follows:
///
/// - The first `I`: signed, `U`: unsigned
/// - The number following the `I`/`U` determines the bit size of the term.
#[allow(missing_docs)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, Hash)]
pub enum AddrTermSize {
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
}

impl Display for AddrTermSize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            AddrTermSize::U8 => "u8",
            AddrTermSize::I8 => "i8",
            AddrTermSize::U16 => "u16",
            AddrTermSize::I16 => "i16",
            AddrTermSize::U32 => "u32",
            AddrTermSize::I32 => "i32",
            AddrTermSize::U64 => "u64",
        })
    }
}

impl AddrTermSize {
    /// Applies the sizing operation to `val`.
    pub fn apply(self, val: u64) -> u64 {
        match self {
            AddrTermSize::U64 => val,
            AddrTermSize::U8 => val as u8 as u64,
            AddrTermSize::U16 => val as u16 as u64,
            AddrTermSize::U32 => val as u32 as u64,
            AddrTermSize::I8 => val as i8 as u64,
            AddrTermSize::I16 => val as i16 as u64,
            AddrTermSize::I32 => val as i32 as u64,
        }
    }

    /// Returns the number of possible values in a term with this size.
    /// Panicks for `AddrTermSize::U64`.
    pub fn num_values(self) -> u64 {
        match self {
            AddrTermSize::U8 | AddrTermSize::I8 => 0x100,
            AddrTermSize::U16 | AddrTermSize::I16 => 0x1_0000,
            AddrTermSize::U32 | AddrTermSize::I32 => 0x1_0000_0000,
            AddrTermSize::U64 => panic!("Cannot fit TermSize::U64::len() in a u64"),
        }
    }

    /// Returns true if the term is signed.
    pub fn is_signed(self) -> bool {
        match self {
            AddrTermSize::U8 | AddrTermSize::U16 | AddrTermSize::U32 | AddrTermSize::U64 => false,
            AddrTermSize::I8 | AddrTermSize::I16 | AddrTermSize::I32 => true,
        }
    }

    /// Returns the highest bit index that can be affected by this term.
    pub fn max_bit_influence(self) -> usize {
        match self {
            AddrTermSize::U8 | AddrTermSize::I8 => 8,
            AddrTermSize::U16 | AddrTermSize::I16 => 16,
            AddrTermSize::U32 | AddrTermSize::I32 => 32,
            AddrTermSize::U64 => 64,
        }
    }
}

/// A shift-then-multiply operation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, Hash)]
pub struct AddrTermCalculation {
    /// The shift-then-multiply applied to the term.
    pub shift: AddrTermShift,

    /// The sizing operation applied to the term.
    pub size: AddrTermSize,
}

impl Display for AddrTermCalculation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(X as {} >> {}) * {}", self.size, self.shift.right, self.shift.mult)
    }
}

impl AddrTermCalculation {
    /// Applies the shift-then-multiply operation to `val`.
    #[inline]
    pub fn apply(self, val: u64) -> u64 {
        self.shift.apply(self.size.apply(val))
    }

    /// Returns the highest bit index that this term can influence.
    #[inline]
    pub fn max_bit_influence(self) -> usize {
        let base = self.size.max_bit_influence();
        let mut mult_bits = 0;
        let mut k = 1;

        while k < self.shift.mult {
            k <<= 1;
            mult_bits += 1;
        }

        base + mult_bits - self.shift.right as usize
    }
}

/// An address term, consisting of a primary sized shift-then-multipy operation, and an optional second sized shift-then-multiply operation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, Hash)]
pub struct AddrTerm {
    /// The primary operation on the input.
    pub primary: AddrTermCalculation,

    /// The optional second use of the input.
    pub second_use: Option<AddrTermCalculation>,
}

impl Display for AddrTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.second_use {
            Some(second_use) => write!(f, "{} + {second_use}", self.primary),
            None => Display::fmt(&self.primary, f),
        }
    }
}

impl Default for AddrTerm {
    fn default() -> Self {
        AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 0,
                    right: 0,
                },
                size: AddrTermSize::U64,
            },
            second_use: None,
        }
    }
}

impl AddrTerm {
    /// Creates a new address term that always returns 0.
    #[inline]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Creates an address term that always returns the value it receives.
    #[inline]
    pub fn identity() -> Self {
        AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    right: 0,
                    mult: 1,
                },
                size: AddrTermSize::U64,
            },
            second_use: None,
        }
    }

    /// Creates an address term that sizes, shifts and multiplies once.
    pub fn single(size: AddrTermSize, right: u8, mult: u8) -> Self {
        AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    right,
                    mult,
                },
                size,
            },
            second_use: None,
        }
    }

    /// Applies the term to `val`.
    #[inline]
    pub fn apply(self, val: u64) -> u64 {
        self.primary
            .apply(val)
            .wrapping_add(self.second_use.map(|t| t.apply(val)).unwrap_or(0))
    }

    #[inline]
    fn is_empty(self) -> bool {
        self.primary.shift.mult == 0 && self.second_use.is_none()
    }

    fn compute_step_offset(self, x: u64, target: u64) -> Option<u64> {
        let remaining = target - self.apply(x);
        let second_use = self.second_use.unwrap();
        // Every time that we increment x with `primary_step / self.primary.shift.mult`, the output will increment by `full_step`.
        let primary_step = (self.primary.shift.mult as u64) << second_use.shift.right;
        let full_step = primary_step + second_use.shift.mult as u64;

        // Add as many full steps as possible to x.
        let correction = remaining / full_step * (1 << second_use.shift.right);
        let x = x + correction;

        let remaining = target - self.apply(x);

        // Remaining now must be smaller than a full step, because of the correction above.
        debug_assert!(remaining < full_step);

        // For the final corrections, the contribution from the second use is fixed.
        // We increment by less than a primary_step, which is the threshold below which the shifted second use stays unchanged.
        // This is not always possible depending on the multiplications and shifts.
        if remaining < primary_step && remaining % self.primary.shift.mult as u64 == 0 {
            Some(x.wrapping_add(remaining / self.primary.shift.mult as u64))
        } else {
            None
        }
    }

    /// Computes a new value for this term that would move the memory access from `current_output` to `target_output`, given that the input for the term is currently `current_value`.
    pub fn compute_relocation(self, current_value: u64, current_output: u64, target_output: u64) -> Option<u64> {
        let val = self.apply(current_value);
        let base_offset = current_output.wrapping_sub(val);
        let target = target_output.wrapping_sub(base_offset);
        if let Some(second_use) = self.second_use {
            if self.primary.size == AddrTermSize::U64 && second_use.size == AddrTermSize::U64 && self.primary.shift.right == 0 {
                if second_use.shift.right == 0 {
                    let factor = self.primary.shift.mult as u64 + second_use.shift.mult as u64;
                    if target % factor == 0 {
                        Some(target / factor)
                    } else {
                        None
                    }
                } else {
                    self.compute_step_offset(0, target)
                }
            } else {
                assert!(self.primary.shift.right == 0);
                assert!(self.primary.shift.mult << second_use.shift.right >= second_use.shift.mult);
                if self.primary.size == AddrTermSize::U64 && self.primary.shift.right == 0 {
                    // The second use might not be 64 bits.
                    // If this is the case, the resulting address will "cycle" every N bits because the second use wrapped around.
                    // Start by determining the right "cycle" to use.
                    let cycle_len = second_use.size.num_values() * self.primary.shift.mult as u64;
                    let len = second_use.shift.apply(second_use.size.num_values());

                    // Because we can have computations like x as u64 + x as u8, there might be multiple cycles that we can use.
                    let min_base = target.checked_sub(len).map(|v| v / cycle_len).unwrap_or(0);
                    let max_base = target / cycle_len;

                    let k = second_use.size.num_values() / 2 - 1;
                    let max_positive_remainder = self.primary.shift.apply(k) + second_use.shift.apply(k);

                    let k = second_use.size.num_values() / 2;
                    let first_negative_offset = self.primary.shift.apply(k).wrapping_add(second_use.apply(k));

                    for base in min_base..=max_base {
                        // The base offset that will get us into the right cycle.
                        let x = (base * cycle_len) / self.primary.shift.mult as u64;

                        // The remainder that we need to add to get the target value
                        let remaining = target - self.apply(x);
                        if remaining < max_positive_remainder || !second_use.size.is_signed() {
                            if let Some(new_value) = self.compute_step_offset(x, target) {
                                return Some(new_value);
                            }
                        }

                        if second_use.size.is_signed() && remaining >= first_negative_offset {
                            let x = x + second_use.size.num_values() / 2;
                            if let Some(new_value) = self.compute_step_offset(x, target) {
                                return Some(new_value);
                            }
                        }
                    }

                    None
                } else if self.primary.shift.right == 0 {
                    warn!("Handle primary size not an U64");
                    None
                } else {
                    unreachable!("Terms with two uses must set shift.right = 0 for the first term.")
                }
            }
        } else {
            let result = match self.primary.shift {
                AddrTermShift {
                    mult: 0,
                    right,
                } => Some(target << right),
                AddrTermShift {
                    mult,
                    right,
                } => {
                    if target % mult as u64 == 0 {
                        Some((target / mult as u64) << right)
                    } else {
                        None
                    }
                },
            };

            result.and_then(|result| {
                if self.primary.size.apply(result) == result {
                    Some(result)
                } else {
                    None
                }
            })
        }
    }

    /// Returns true if the delta between two accesses where only this term differs can be `offset`.
    #[inline]
    pub fn offset_is_valid(self, offset: i64) -> bool {
        offset % self.minimum_step_size() as i64 == 0
    }

    /// Returns the minimum step size of this term.
    #[inline]
    pub fn minimum_step_size(self) -> u64 {
        if let Some(second_use) = self.second_use {
            if self.primary.shift.right == second_use.shift.right {
                self.primary.shift.mult as u64 + second_use.shift.mult as u64
            } else {
                1
            }
        } else {
            self.primary.shift.mult as u64
        }
    }

    /// Determines whether the change from `original_address` to `new_address` could have occurred given that the original value for this term was `original_value`, and for `new_address` it was `new_value`.
    #[inline]
    pub fn is_valid_delta(self, original_value: u64, new_value: u64, original_address: u64, new_address: u64) -> bool {
        let original_contribution = self.apply(original_value);
        let new_contribution = self.apply(new_value);

        let contribution_delta = new_contribution.wrapping_sub(original_contribution);
        let address_delta = new_address.wrapping_sub(original_address);

        contribution_delta == address_delta
    }

    /// Determines whether this term could be part of an address calculation, if modifying only this term changes the address of a memory access from `original_address` to `new_address`.
    #[inline]
    pub fn is_possible_with_delta(&self, original_address: u64, new_address: u64) -> bool {
        let max_delta = self
            .primary
            .max_bit_influence()
            .max(self.second_use.map(|u| u.max_bit_influence() + 1).unwrap_or(0))
            .min(64);
        let min = original_address.min(new_address);
        let max = original_address.max(new_address);
        let address_delta = max - min;

        // Correct for the wrap-around between negative and positive numbers
        let address_delta = if address_delta >> 63 != 0 {
            // Since the highest bit was set in one of the numbers, max is negative when converted to i64
            let dist = (-(max as i64)) as u64;

            // println!("min={:X?}, max={:X?}, dist={:X?}", min, max, dist);

            min + dist
        } else {
            address_delta
        };

        // println!("Delta: {:X?}", address_delta);
        // println!("Max bit: {}", max_delta);

        let highest_bit_in_delta = 64 - address_delta.leading_zeros();

        // println!("Highest bit: {}", highest_bit_in_delta);

        highest_bit_in_delta as usize <= max_delta
    }

    /// Returns all supported [`AddrTerm`]s.
    pub fn all() -> Vec<AddrTerm> {
        const ALL_SIZES: [AddrTermSize; 7] = [
            AddrTermSize::U64,
            AddrTermSize::U32,
            AddrTermSize::U16,
            AddrTermSize::U8,
            AddrTermSize::I32,
            AddrTermSize::I16,
            AddrTermSize::I8,
        ];
        const ALL_SHIFTS: [AddrTermShift; 31] = [
            AddrTermShift {
                mult: 1,
                right: 0,
            },
            AddrTermShift {
                mult: 2,
                right: 0,
            },
            AddrTermShift {
                mult: 3,
                right: 0,
            },
            AddrTermShift {
                mult: 4,
                right: 0,
            },
            AddrTermShift {
                mult: 5,
                right: 0,
            },
            AddrTermShift {
                mult: 8,
                right: 0,
            },
            AddrTermShift {
                mult: 9,
                right: 0,
            },
            AddrTermShift {
                mult: 1,
                right: 1,
            },
            AddrTermShift {
                mult: 1,
                right: 2,
            },
            AddrTermShift {
                mult: 1,
                right: 3,
            },
            AddrTermShift {
                mult: 1,
                right: 4,
            },
            AddrTermShift {
                mult: 1,
                right: 5,
            },
            AddrTermShift {
                mult: 1,
                right: 6,
            },
            AddrTermShift {
                mult: 2,
                right: 1,
            },
            AddrTermShift {
                mult: 2,
                right: 2,
            },
            AddrTermShift {
                mult: 2,
                right: 3,
            },
            AddrTermShift {
                mult: 2,
                right: 4,
            },
            AddrTermShift {
                mult: 2,
                right: 5,
            },
            AddrTermShift {
                mult: 2,
                right: 6,
            },
            AddrTermShift {
                mult: 4,
                right: 1,
            },
            AddrTermShift {
                mult: 4,
                right: 2,
            },
            AddrTermShift {
                mult: 4,
                right: 3,
            },
            AddrTermShift {
                mult: 4,
                right: 4,
            },
            AddrTermShift {
                mult: 4,
                right: 5,
            },
            AddrTermShift {
                mult: 4,
                right: 6,
            },
            AddrTermShift {
                mult: 8,
                right: 1,
            },
            AddrTermShift {
                mult: 8,
                right: 2,
            },
            AddrTermShift {
                mult: 8,
                right: 3,
            },
            AddrTermShift {
                mult: 8,
                right: 4,
            },
            AddrTermShift {
                mult: 8,
                right: 5,
            },
            AddrTermShift {
                mult: 8,
                right: 6,
            },
        ];
        let mut result = Vec::new();

        // Two separate loops so that the simpler terms always occur first
        for size in ALL_SIZES {
            for shift in ALL_SHIFTS {
                result.push(AddrTerm {
                    primary: AddrTermCalculation {
                        shift,
                        size,
                    },
                    second_use: None,
                });
            }
        }

        for size in ALL_SIZES {
            for shift in ALL_SHIFTS {
                for second_size in ALL_SIZES {
                    for second_shift in ALL_SHIFTS {
                        // These can only add offsets of 2 or 3 (1 or 2 if signed) bits,
                        // and are false-positives most of the time...
                        if [AddrTermSize::I8, AddrTermSize::U8].contains(&second_size) && second_shift.right >= 5 {
                            continue;
                        }

                        if second_size <= size
                            && (second_size != size || second_shift.right != shift.right)
                            && shift.right == 0
                            && shift.mult << second_shift.right >= second_shift.mult
                        {
                            result.push(AddrTerm {
                                primary: AddrTermCalculation {
                                    shift,
                                    size,
                                },
                                second_use: Some(AddrTermCalculation {
                                    shift: second_shift,
                                    size: second_size,
                                }),
                            });
                        }
                    }
                }
            }
        }

        result
    }
}

impl Computation for AddressComputation {
    #[inline]
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue {
        let inputs = inputs.iter().map(|x| x.unwrap_num()).collect::<Vec<_>>();
        OwnedValue::Num(AddressComputation::evaluate(self, &inputs))
    }

    fn display<'a, S: AsRef<str>>(&'a self, input_names: &'a [S]) -> impl Display + Debug + 'a {
        DisplayAddressComputation {
            calculation: *self,
            inputs: input_names.iter().map(|n| n.as_ref().to_string()).collect::<Vec<_>>(),
        }
    }

    fn used_input_indices(&self) -> Vec<usize> {
        self.terms
            .iter()
            .enumerate()
            .filter(|(_, term)| !term.is_empty())
            .map(|(index, _)| index)
            .collect()
    }

    fn remap_inputs(&mut self, map: &[Option<usize>]) {
        let old_terms = self.terms;
        self.terms = [0, 1, 2, 3].map(|index| map[index].map(|n| old_terms[n]).unwrap_or(AddrTerm::empty()));
    }

    fn is_identity(&self) -> bool {
        unimplemented!()
    }
}

impl AddressComputation {
    /// Computes the address accessed by the instruction when executed on `state`, given that the computation uses `inputs`.
    #[inline]
    pub fn compute<A: Arch>(&self, inputs: &Inputs<A>, state: &SystemState<A>) -> u64 {
        let mut sum = 0u64;
        for (input, shift) in inputs.iter().zip(self.terms.iter()) {
            let v = match input {
                Source::Dest(d) => match state.get_dest(d) {
                    Value::Num(n) => n,
                    other => panic!("Cannot handle: {other:?}"),
                },
                Source::Const {
                    value, ..
                } => *value,
                Source::Imm {
                    ..
                } => panic!("Cannot evaluate an expression that contains immediate value references"),
            };

            sum = sum.wrapping_add(shift.apply(v));
        }

        sum.wrapping_add(self.offset as u64)
    }

    /// Computes the address accessed by the instruction when executed on `state`, given that the computation uses `inputs`.
    #[inline]
    pub fn compute_from_gpregs<A: Arch>(&self, inputs: &[A::GpReg], state: &SystemState<A>) -> u64 {
        let mut sum = 0u64;
        for (input, shift) in inputs.iter().zip(self.terms.iter()) {
            let v = state.cpu().gpreg(*input);
            sum = sum.wrapping_add(shift.apply(v));
        }

        sum.wrapping_add(self.offset as u64)
    }

    /// Computes the address, using `inputs`.
    #[inline]
    pub fn evaluate(&self, inputs: &[u64]) -> u64 {
        self.evaluate_from_iter(inputs.iter().copied())
    }

    /// Computes the address, using `inputs`.
    #[inline]
    pub fn evaluate_from_iter(&self, inputs: impl Iterator<Item = u64>) -> u64 {
        let mut sum = 0u64;
        for (v, shift) in inputs.zip(self.terms.iter()) {
            sum = sum.wrapping_add(shift.apply(v));
        }

        sum.wrapping_add(self.offset as u64)
    }
}

#[derive(Deserialize, Serialize)]
struct DisplayAddressComputation {
    calculation: AddressComputation,
    inputs: Vec<String>,
}

impl Debug for DisplayAddressComputation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for DisplayAddressComputation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, (input, term)) in self
            .inputs
            .iter()
            .zip(self.calculation.terms.iter().filter(|term| !term.is_empty()))
            .enumerate()
        {
            if index != 0 {
                write!(f, " + ")?;
            }

            write!(f, "{}{}", input, term.primary.size)?;
            if term.primary.shift.right > 0 {
                write!(f, " >> {}", term.primary.shift.right)?;
            }

            if term.primary.shift.mult != 1 {
                write!(f, " * {}", term.primary.shift.mult)?;
            }

            if let Some(second_use) = term.second_use {
                write!(f, " + {}{}", input, second_use.size)?;
                if second_use.shift.right > 0 {
                    write!(f, " >> {}", second_use.shift.right)?;
                }

                if second_use.shift.mult != 1 {
                    write!(f, " * {}", second_use.shift.mult)?;
                }
            }
        }

        match self.calculation.offset.cmp(&0) {
            Ordering::Less => write!(f, " - 0x{:X}", -self.calculation.offset)?,
            Ordering::Greater => write!(f, " + 0x{:X}", self.calculation.offset)?,
            Ordering::Equal => (),
        }

        Ok(())
    }
}

impl AddressComputation {
    /// An address computation of the form `A + B + C`.
    /// `num` determines the number of inputs.
    /// `num` cannot be more than 4.
    #[inline]
    pub fn unscaled_sum(num: usize) -> AddressComputation {
        AddressComputation {
            offset: 0,
            terms: [0, 1, 2, 3].map(|n| if n < num { AddrTerm::identity() } else { AddrTerm::default() }),
        }
    }

    /// Returns a new computation with the offset replaced with the specified `offset`.
    #[inline]
    pub fn with_offset(self, offset: i64) -> AddressComputation {
        AddressComputation {
            offset,
            ..self
        }
    }

    /// Returns a new computation with the offset incremented with the specified `offset`.
    #[inline]
    pub fn with_added_offset(self, offset: i64) -> AddressComputation {
        AddressComputation {
            offset: self.offset.wrapping_add(offset),
            ..self
        }
    }

    /// Returns a new computation with an offset inferred from the expected address `expected`.
    #[inline]
    pub fn new_with_inferred_offset<A: Arch>(
        terms: [AddrTerm; 4], inputs: &Inputs<A>, state: &SystemState<A>, expected: u64,
    ) -> AddressComputation {
        let mut result = AddressComputation {
            offset: 0,
            terms,
        };

        let actual = result.compute(inputs, state);
        result.offset = expected.wrapping_sub(actual) as i64;

        result
    }

    /// Returns a new computation with the terms (max 4) from `terms` and the `offset` specified.
    #[inline]
    pub fn from_iter(terms: impl Iterator<Item = AddrTerm>, offset: i64) -> AddressComputation {
        let mut terms = terms.fuse();
        let result = AddressComputation {
            terms: [
                terms.next().unwrap_or_default(),
                terms.next().unwrap_or_default(),
                terms.next().unwrap_or_default(),
                terms.next().unwrap_or_default(),
            ],
            offset,
        };

        if terms.next().is_some() {
            panic!("Too many items in iterator");
        }

        result
    }

    /// Returns the fixed difference (other - self) between two address calculations, if they are given the same inputs
    /// When adding this offset to the address for `self`, you will obtain the adress for `other`.
    #[inline]
    pub fn constant_offset_with(&self, other: &AddressComputation) -> Option<i64> {
        if self.terms == other.terms {
            Some(other.offset.wrapping_sub(self.offset))
        } else {
            None
        }
    }

    /// Returns the fixed difference (other - self) between two address calculations, if they are given the same inputs
    /// When adding this offset to the address for `self`, you will obtain the adress for `other`.
    pub fn constant_offset_considering_inputs<A: Arch>(
        &self, inputs: &Inputs<A>, other: &AddressComputation, other_inputs: &Inputs<A>,
    ) -> Option<i64> {
        let mut result = other.offset.wrapping_sub(self.offset);
        let mut b_terms_used = [false; 4];
        for (term_a, input_a) in self.terms.iter().zip(inputs.iter()) {
            if let Source::Const {
                value, ..
            } = input_a
            {
                result -= *value as i64;
            } else if let Some(other_index) = other_inputs.iter().position(|input_b| input_b == input_a) {
                let term_b = other.terms[other_index];
                b_terms_used[other_index] = true;

                if term_a != &term_b {
                    return None;
                }
            } else {
                return None;
            }
        }

        for (index, input_b) in other_inputs.iter().enumerate() {
            if !b_terms_used[index] {
                if let Source::Const {
                    value, ..
                } = input_b
                {
                    result += *value as i64;
                } else {
                    return None;
                }
            }
        }

        Some(result)
    }

    /// Adds a new [`AddrTerm::identity`] term if there are less than 4 terms.
    /// Otherwise, does nothing.
    #[inline]
    pub fn add_constant_term(&mut self) {
        *self.terms.iter_mut().find(|term| term.is_empty()).unwrap() = AddrTerm::identity();
    }

    /// Removes the term at position `index` from the computation.
    /// If there are less than `index + 1` terms, the same computation is returned.
    #[inline]
    pub fn remove_term(self, index: usize) -> AddressComputation {
        let mut terms = [AddrTerm::default(); 4];
        let len = terms.len();
        terms[..index].copy_from_slice(&self.terms[..index]);
        terms[index..][..len - index - 1].copy_from_slice(&self.terms[index + 1..]);
        AddressComputation {
            offset: self.offset,
            terms,
        }
    }

    /// Combines the two terms, assuming they have the same index.
    /// For example, `A + A * 2` would be unified to `A * 3`.
    pub fn unify_terms(self, first_index: usize, second_index: usize) -> Option<AddressComputation> {
        let first_term = self.terms[first_index];
        let second_term = self.terms[second_index];
        let mut result = self.remove_term(second_index);

        // Correct for removed term
        let first_index = if first_index > second_index {
            first_index - 1
        } else {
            first_index
        };

        if first_term.primary.shift.right == second_term.primary.shift.right
            && first_term.primary.size == second_term.primary.size
            && first_term.second_use.is_none()
            && second_term.second_use.is_none()
        {
            result.terms[first_index].primary.shift.mult += second_term.primary.shift.mult;
        } else {
            // TODO: Implement unification for more cases
            return None;
        }

        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::{AddrTerm, AddrTermCalculation, AddrTermShift};
    use crate::arch::fake::{FakeArch, FakeReg};
    use crate::encoding::dataflows::{AddrTermSize, AddressComputation, Dest, Inputs, Size, Source};

    #[test]
    pub fn size_ordering() {
        assert!(AddrTermSize::U64 > AddrTermSize::U8);
        assert!(AddrTermSize::U8 < AddrTermSize::U16);
        assert!(AddrTermSize::U16 < AddrTermSize::U32);
        assert!(AddrTermSize::U32 < AddrTermSize::U64);
    }

    #[test]
    pub fn compute_relocation_unsigned_x1() {
        let term = AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 1,
                    right: 0,
                },
                size: AddrTermSize::U64,
            },
            second_use: Some(AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 4,
                    right: 2,
                },
                size: AddrTermSize::U16,
            }),
        };

        let x = 0x8000;
        let addr = term.apply(x);
        let target = addr + 0x300_1580;

        println!("Current = 0x{addr:X}");
        println!("Target = 0x{target:X}");

        let new_x = term.compute_relocation(x, addr, target).unwrap();
        assert_eq!(term.apply(new_x), target);

        let x = 0xe7b;
        let addr = term.apply(x);
        let target = 0x4f0;

        println!("Current = 0x{addr:X}");
        println!("Target = 0x{target:X}");

        let new_x = term.compute_relocation(x, addr, target).unwrap();
        assert_eq!(term.apply(new_x), target);
    }

    #[test]
    pub fn compute_relocation_signed_x1() {
        let term = AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 1,
                    right: 0,
                },
                size: AddrTermSize::U64,
            },
            second_use: Some(AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 4,
                    right: 3,
                },
                size: AddrTermSize::I16,
            }),
        };

        let x = 0x7000;
        let addr = term.apply(x);
        let target = 0x1800;

        println!("Current = 0x{addr:X}");
        println!("Target = 0x{target:X}");

        let new_x = term.compute_relocation(x, addr, target).unwrap();
        assert_eq!(term.apply(new_x), target);

        let x = 0x1000;
        let addr = term.apply(x);
        let target = 0x9000; // 0xC000 - (0x6000 >> 3) * 4

        println!("Current = 0x{addr:X}");
        println!("Target = 0x{target:X}");

        let new_x = term.compute_relocation(x, addr, target).unwrap();
        assert_eq!(term.apply(new_x), target);
    }

    #[test]
    pub fn compute_relocation_unsigned_x2() {
        let term = AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 2,
                    right: 0,
                },
                size: AddrTermSize::U64,
            },
            second_use: Some(AddrTermCalculation {
                shift: AddrTermShift {
                    mult: 2,
                    right: 1,
                },
                size: AddrTermSize::U16,
            }),
        };

        let x = 0x1440C;
        let addr = term.apply(x);
        let target = 0x1E8B2;

        println!("Current = 0x{addr:X}");
        println!("Target = 0x{target:X}");

        let new_x = term.compute_relocation(x, addr, target).unwrap();
        assert_eq!(term.apply(new_x), target);
    }

    #[test]
    pub fn compute_relocation_fuzz() {
        let terms = [
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 4,
                        right: 2,
                    },
                    size: AddrTermSize::U16,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 1,
                    },
                    size: AddrTermSize::U16,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 5,
                    },
                    size: AddrTermSize::U16,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 5,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 4,
                        right: 3,
                    },
                    size: AddrTermSize::U32,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U32,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 4,
                        right: 5,
                    },
                    size: AddrTermSize::I16,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 1,
                    },
                    size: AddrTermSize::I32,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 4,
                        right: 5,
                    },
                    size: AddrTermSize::I32,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 1,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                }),
            },
            AddrTerm {
                primary: AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 0,
                    },
                    size: AddrTermSize::U64,
                },
                second_use: Some(AddrTermCalculation {
                    shift: AddrTermShift {
                        mult: 2,
                        right: 1,
                    },
                    size: AddrTermSize::U64,
                }),
            },
        ];

        let mut rng = rand::thread_rng();
        for term in terms {
            for _ in 0..500_000 {
                let x = rng.gen();
                let addr = term.apply(x);
                let target = rng.gen();

                if let Some(new_x) = term.compute_relocation(x, addr, target) {
                    assert_eq!(
                        term.apply(new_x),
                        target,
                        "Relocation from {:X?} resulted in {:X?} rather than the target {:X?} on term {:X?}",
                        addr,
                        term.apply(new_x),
                        target,
                        term
                    );
                }
            }
        }
    }

    #[test]
    pub fn unify_terms() {
        let c1 = AddressComputation {
            offset: 4,
            terms: [
                AddrTerm {
                    primary: AddrTermCalculation {
                        shift: AddrTermShift {
                            right: 0,
                            mult: 1,
                        },
                        size: AddrTermSize::U64,
                    },
                    second_use: None,
                },
                AddrTerm {
                    primary: AddrTermCalculation {
                        shift: AddrTermShift {
                            right: 0,
                            mult: 2,
                        },
                        size: AddrTermSize::U64,
                    },
                    second_use: None,
                },
                AddrTerm::default(),
                AddrTerm::default(),
            ],
        };
        let c2 = AddressComputation {
            offset: 4,
            terms: [
                AddrTerm {
                    primary: AddrTermCalculation {
                        shift: AddrTermShift {
                            right: 0,
                            mult: 3,
                        },
                        size: AddrTermSize::U64,
                    },
                    second_use: None,
                },
                AddrTerm::default(),
                AddrTerm::default(),
                AddrTerm::default(),
            ],
        };

        assert_eq!(c1.unify_terms(0, 1).unwrap(), c2);
        assert_eq!(c1.unify_terms(1, 0).unwrap(), c2);
    }

    #[test]
    pub fn is_possible_with_delta() {
        let term = AddrTerm {
            primary: AddrTermCalculation {
                shift: AddrTermShift {
                    right: 0,
                    mult: 1,
                },
                size: AddrTermSize::U8,
            },
            second_use: None,
        };

        assert!(term.is_possible_with_delta(0, 255));
        assert!(term.is_possible_with_delta(500, 755));
        assert!(term.is_possible_with_delta((-16i64) as u64, 239));

        assert!(!term.is_possible_with_delta(0, 256));
        assert!(!term.is_possible_with_delta(500, 756));
        assert!(!term.is_possible_with_delta((-16i64) as u64, 240));
    }

    #[test]
    pub fn constant_offset_dataflow() {
        let inputs_a = Inputs::<FakeArch>::unsorted(vec![Source::Const {
            value: 12,
            num_bits: 16,
        }]);
        let inputs_b = Inputs::<FakeArch>::unsorted(vec![Source::Const {
            value: 50,
            num_bits: 16,
        }]);
        let c1 = AddressComputation::unscaled_sum(1);
        let c2 = AddressComputation::unscaled_sum(2);

        assert_eq!(c1.constant_offset_considering_inputs(&inputs_a, &c1, &inputs_b), Some(38));

        let inputs_a = Inputs::<FakeArch>::unsorted(vec![Source::Const {
            value: 12,
            num_bits: 16,
        }]);
        let inputs_b = Inputs::<FakeArch>::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]);

        assert_eq!(c1.constant_offset_considering_inputs(&inputs_a, &c1, &inputs_b), None);

        let inputs_a = Inputs::<FakeArch>::unsorted(vec![
            Source::Const {
                value: 12,
                num_bits: 16,
            },
            Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
        ]);
        let inputs_b = Inputs::<FakeArch>::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]);

        assert_eq!(c2.constant_offset_considering_inputs(&inputs_a, &c1, &inputs_b), Some(-12));
        assert_eq!(c1.constant_offset_considering_inputs(&inputs_b, &c2, &inputs_a), Some(12));

        let inputs_a = Inputs::<FakeArch>::unsorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]);
        let inputs_b = Inputs::<FakeArch>::unsorted(vec![
            Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
            Source::Const {
                value: u64::MAX,
                num_bits: 64,
            },
        ]);

        let c1 = AddressComputation::unscaled_sum(1);
        let c2 = AddressComputation::unscaled_sum(2).with_offset(7);

        assert_eq!(c1.constant_offset_considering_inputs(&inputs_a, &c2, &inputs_b), Some(6));
        assert_eq!(c2.constant_offset_considering_inputs(&inputs_b, &c1, &inputs_a), Some(-6));
    }
}
