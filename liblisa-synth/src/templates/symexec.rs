use std::iter::once;
use std::ops::{Add, BitAnd, BitOr, BitXor, Not, Shl, Shr};

use arrayvec::ArrayVec;
use liblisa::semantics::default::ops::{FastOpImpl, Op, ParityOp, Val};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::bitmask_u128;
use log::{debug, trace};

// TODO: For Select[63:+1](0xE | (ube(E) << 0x30)) vs Select[63:+1](0xF | (ube(E) << 0x30)), can we somehow detect that changing the const value does nothing at all for the end result? So we should treat the const value as if it was 0...

pub struct SymbolicExecution<'a> {
    ops: &'a [Op],
    counter: &'a [u16],
    const_values: &'a [i128],
    output_mask: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolicExecutionResult {
    pub leaf_consts: Vec<(usize, i128)>,
    pub const_output: Option<i128>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct SymbolicValue {
    /// if live_bits[N] = 1, then bit N in the value is determined by an input argument.
    /// if live_bits[N] = 0, then bit N is equal to const_value[N].
    live_bits: u128,

    /// if live_bits[N] = 0, then bit N is equal to const_value[N]. Otherwise, const_value[N] = 0.
    const_val: u128,
}

impl std::fmt::Debug for SymbolicValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.live_bits == 0 {
            write!(f, "{}", self.const_val)
        } else if self.live_bits == u128::MAX {
            write!(f, "_")
        } else {
            f.debug_struct("SymbolicValue")
                .field("live_bits", &self.live_bits)
                .field("const_value", &self.const_val)
                .finish()
        }
    }
}

impl From<i128> for SymbolicValue {
    fn from(value: i128) -> Self {
        SymbolicValue {
            live_bits: 0,
            const_val: value as u128,
        }
    }
}

impl SymbolicValue {
    const LIVE: SymbolicValue = SymbolicValue {
        live_bits: u128::MAX,
        const_val: 0,
    };

    pub fn as_i128(&self) -> Option<i128> {
        if self.live_bits == 0 {
            Some(self.const_val as i128)
        } else {
            None
        }
    }

    pub fn mask(&self, mask: u128) -> SymbolicValue {
        SymbolicValue {
            live_bits: self.live_bits & mask,
            const_val: self.const_val & mask,
        }
    }

    pub fn crop(&self, num_bits: u32) -> SymbolicValue {
        self.mask(bitmask_u128(num_bits))
    }

    pub fn sign_extend(&self, num_bits: u32) -> SymbolicValue {
        let is_live = (self.live_bits >> (num_bits - 1)) & 1 != 0;
        if is_live {
            let mask = bitmask_u128(num_bits);
            SymbolicValue {
                live_bits: self.live_bits | !mask,
                const_val: self.const_val & mask,
            }
        } else {
            let mask = bitmask_u128(num_bits);
            let shift = 128 - num_bits;
            SymbolicValue {
                live_bits: self.live_bits & mask,
                const_val: (((self.const_val as i128) << shift) >> shift) as u128,
            }
        }
    }

    fn min_unsigned(&self) -> u128 {
        self.const_val & !self.live_bits
    }

    fn max_unsigned(&self) -> u128 {
        self.live_bits | self.const_val
    }

    pub fn bitmask(n: SymbolicValue) -> SymbolicValue {
        let max = n.max_unsigned();
        let min = n.min_unsigned();

        let fixed = if min < 128 { bitmask_u128(min as u32) } else { u128::MAX };

        let live = if max < 128 { bitmask_u128(max as u32) } else { u128::MAX };

        SymbolicValue {
            live_bits: live & !fixed,
            const_val: fixed,
        }
    }

    pub fn any_const_one_bits(&self) -> bool {
        self.const_val != 0
    }

    pub fn cmp_lt(&self, rhs: SymbolicValue) -> SymbolicValue {
        if get_bit(self.live_bits, 127) || get_bit(rhs.live_bits, 127) {
            return SymbolicValue::LIVE.crop(1)
        }

        let negative = match (get_bit(self.const_val, 127), get_bit(rhs.const_val, 127)) {
            (false, false) => false,
            (true, true) => true,
            (false, true) => return SymbolicValue::from(0),
            (true, false) => return SymbolicValue::from(1),
        };

        for bit in (0..127).rev() {
            if !get_bit(self.live_bits, bit) && !get_bit(rhs.live_bits, bit) {
                if !get_bit(self.const_val, bit) && get_bit(rhs.const_val, bit) {
                    return SymbolicValue::from(if negative { 0 } else { 1 })
                } else if get_bit(self.const_val, bit) && !get_bit(rhs.const_val, bit) {
                    return SymbolicValue::from(if negative { 1 } else { 0 })
                }
            } else {
                return SymbolicValue::LIVE.crop(1)
            }
        }

        // Values are exactly equal
        SymbolicValue::from(0)
    }
}

impl Not for SymbolicValue {
    type Output = SymbolicValue;

    fn not(self) -> Self::Output {
        SymbolicValue {
            live_bits: self.live_bits,
            const_val: !self.const_val & !self.live_bits,
        }
    }
}

impl Shr<u8> for SymbolicValue {
    type Output = SymbolicValue;

    fn shr(self, rhs: u8) -> Self::Output {
        self.shr(rhs as u32)
    }
}

impl Shr<u32> for SymbolicValue {
    type Output = SymbolicValue;

    fn shr(self, rhs: u32) -> Self::Output {
        SymbolicValue {
            live_bits: ((self.live_bits as i128) >> rhs) as u128,
            const_val: ((self.const_val as i128) >> rhs) as u128,
        }
    }
}

impl Shr<SymbolicValue> for SymbolicValue {
    type Output = SymbolicValue;

    fn shr(self, rhs: SymbolicValue) -> Self::Output {
        let min = rhs.min_unsigned() & 0x7f;
        let max = rhs.max_unsigned() & 0x7f;

        let mut live_bits = 0;
        let mut const_val = ((self.const_val as i128) >> min) as u128;

        for x in min..=max {
            live_bits |= ((self.live_bits as i128) >> x) as u128;
            live_bits |= const_val ^ ((self.const_val as i128) >> x) as u128;
            const_val &= !live_bits;
        }

        SymbolicValue {
            live_bits,
            const_val,
        }
    }
}

impl Shl<SymbolicValue> for SymbolicValue {
    type Output = SymbolicValue;

    fn shl(self, rhs: SymbolicValue) -> Self::Output {
        let min = rhs.min_unsigned() & 0x7f;
        let max = rhs.max_unsigned() & 0x7f;

        let mut live_bits = 0;
        let mut const_val = self.const_val << min;

        for x in min..=max {
            live_bits |= self.live_bits << x;
            live_bits |= const_val ^ (self.const_val << x);
            const_val &= !live_bits;
        }

        SymbolicValue {
            live_bits,
            const_val,
        }
    }
}

impl BitAnd for SymbolicValue {
    type Output = SymbolicValue;

    fn bitand(self, rhs: Self) -> Self::Output {
        let live_bits = (self.live_bits | rhs.live_bits) & (self.live_bits | self.const_val) & (rhs.live_bits | rhs.const_val);
        SymbolicValue {
            live_bits,
            const_val: (self.const_val & rhs.const_val) & !live_bits,
        }
    }
}

impl BitOr for SymbolicValue {
    type Output = SymbolicValue;

    fn bitor(self, rhs: Self) -> Self::Output {
        let live_bits = (self.live_bits | rhs.live_bits) & (self.live_bits | !self.const_val) & (rhs.live_bits | !rhs.const_val);
        SymbolicValue {
            live_bits,
            const_val: (self.const_val | rhs.const_val) & !live_bits,
        }
    }
}

impl BitXor for SymbolicValue {
    type Output = SymbolicValue;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let live_bits = self.live_bits | rhs.live_bits;
        SymbolicValue {
            live_bits,
            const_val: (self.const_val ^ rhs.const_val) & !live_bits,
        }
    }
}

fn get_bit(val: u128, bit: u32) -> bool {
    (val >> bit) & 1 != 0
}

impl Add for SymbolicValue {
    type Output = SymbolicValue;

    fn add(self, rhs: Self) -> Self::Output {
        let definite_half_result = self.const_val ^ rhs.const_val;
        let definite_half_carry = self.const_val & rhs.const_val;
        let live_half_result = self.live_bits | rhs.live_bits;
        let live_half_carry =
            (self.const_val & rhs.live_bits) | (rhs.const_val & self.live_bits) | (self.live_bits & rhs.live_bits);

        trace!("Add {self:?} and {rhs:?}");
        trace!("def. HR: {definite_half_result:128b}");
        trace!("def. HC: {definite_half_carry:128b}");
        trace!("live HR: {live_half_result:128b}");
        trace!("live HC: {live_half_carry:128b}");

        let mut live_bits = 0;
        let mut const_value = 0;

        let mut live_carry = false;
        let mut const_carry = false;
        for bit in 0..128 {
            let result_is_live = live_carry || get_bit(live_half_result, bit);
            trace!("bit{bit} live_carry={live_carry}, const_carry={const_carry} is_live={result_is_live}");
            if result_is_live {
                live_bits |= 1 << bit;

                if get_bit(definite_half_carry, bit) {
                    const_carry = true;
                    live_carry = false;
                } else {
                    const_carry = false;
                    live_carry = get_bit(live_half_carry, bit)
                        || (get_bit(live_half_result, bit) && live_carry)
                        || (get_bit(definite_half_result, bit) && live_carry);
                }
            } else {
                let const_half_result = get_bit(definite_half_result, bit);
                let const_result = const_half_result ^ const_carry;

                const_value |= (const_result as u128) << bit;
                const_carry = get_bit(definite_half_carry, bit) || (const_half_result && const_carry);
                live_carry = false;
            }
        }

        SymbolicValue {
            live_bits,
            const_val: const_value,
        }
    }
}

impl std::ops::Sub for SymbolicValue {
    type Output = SymbolicValue;

    fn sub(self, rhs: Self) -> Self::Output {
        trace!("Subtracting {self:?} and {rhs:?}");
        let lhs_potential_zeros = self.live_bits | (!self.const_val & !self.live_bits);
        let rhs_potential_ones = rhs.live_bits | (rhs.const_val & self.live_bits);
        let cases_to_consider = rhs_potential_ones & lhs_potential_zeros;

        trace!("lhs potential zeros: {lhs_potential_zeros:128b}");
        trace!("rhs potential ones : {rhs_potential_ones:128b}");
        trace!("cases to consider  : {cases_to_consider:128b}");

        let live_bits = self.live_bits | rhs.live_bits;
        trace!("live bits          : {live_bits:128b}");

        let live_borrowed = self.const_val.wrapping_sub(cases_to_consider) ^ self.const_val;
        let live_bits = live_bits | live_borrowed;

        trace!("live borrowed      : {live_borrowed:128b}");
        trace!("live bits          : {live_bits:128b}");

        SymbolicValue {
            live_bits,
            const_val: (self.const_val.wrapping_sub(rhs.const_val)) & !live_bits,
        }
    }
}

impl<'a> SymbolicExecution<'a> {
    pub fn new(ops: &'a [Op], counter: &'a [u16], const_values: &'a [i128], output_mask: u128) -> Self {
        SymbolicExecution {
            ops,
            counter,
            const_values,
            output_mask,
        }
    }

    fn compute_data_relations(&self) -> Vec<Vec<usize>> {
        let mut index_stack = ArrayVec::<_, 32>::new();
        let mut relations = Vec::new();
        for (index, op) in self.ops.iter().enumerate() {
            relations.push(index_stack.drain(index_stack.len() - op.num_args()..).collect());
            index_stack
                .try_push(index)
                .unwrap_or_else(|_| panic!("For ops: {:?}, we need more than 32 stack space", self.ops));
        }

        relations
    }

    fn compute_intermediate_masks(&self, const_values: &[SymbolicValue]) -> Vec<u128> {
        let relations = self.compute_data_relations();
        let mut bits_needed = vec![u128::MAX; self.ops.len()];
        *bits_needed.last_mut().unwrap() = self.output_mask;

        for (index, (op, inputs)) in self.ops.iter().zip(relations.iter()).enumerate().rev() {
            let current_bits_needed = bits_needed[index];
            match op {
                Op::And | Op::Or | Op::Xor | Op::Not => {
                    for &index in inputs.iter() {
                        bits_needed[index] = current_bits_needed;
                    }
                },
                Op::Add => {
                    for &index in inputs.iter() {
                        let highest_set = 128 - current_bits_needed.leading_zeros();
                        bits_needed[index] = bitmask_u128(highest_set);
                    }
                },
                Op::Crop {
                    num_bits,
                } => {
                    for &index in inputs.iter() {
                        bits_needed[index] = current_bits_needed & bitmask_u128(*num_bits as u32);
                    }
                },
                Op::Select {
                    num_skip,
                    num_take,
                } => {
                    for &index in inputs.iter() {
                        bits_needed[index] = (current_bits_needed & bitmask_u128(*num_take as u32)) << *num_skip;
                    }
                },
                Op::Shl => {
                    if let Some(const_val) = const_values[inputs[1]].as_i128() {
                        let shift = const_val & 0x7f;
                        bits_needed[inputs[0]] = current_bits_needed >> shift;
                    } else {
                        bits_needed[inputs[0]] = u128::MAX;
                    }

                    bits_needed[inputs[1]] = 0x7f;
                },
                Op::Shr => {
                    if let Some(const_val) = const_values[inputs[1]].as_i128() {
                        let shift = const_val & 0x7f;
                        bits_needed[inputs[0]] = current_bits_needed << shift;
                    } else {
                        bits_needed[inputs[0]] = u128::MAX;
                    }

                    bits_needed[inputs[1]] = 0x7f;
                },
                Op::Parity => {
                    for &index in inputs.iter() {
                        bits_needed[index] = 0xff;
                    }
                },
                Op::SignExtend {
                    num_bits,
                } => {
                    for &index in inputs.iter() {
                        let need_sign_bit = current_bits_needed & !bitmask_u128(*num_bits as u32 - 1) != 0;
                        bits_needed[index] =
                            (bitmask_u128(*num_bits as u32) & current_bits_needed) | ((need_sign_bit as u128) << (*num_bits - 1));
                    }
                },
                Op::Rol {
                    num_bits,
                } => {
                    bits_needed[inputs[0]] = bitmask_u128(*num_bits as u32);
                    bits_needed[inputs[1]] = u128::MAX;
                },
                _ => {
                    for &index in inputs.iter() {
                        bits_needed[index] = u128::MAX;
                    }
                },
            }
        }

        bits_needed
    }

    fn symbolic_exec(&self, intermediate_masks: &[u128]) -> Vec<SymbolicValue> {
        trace!("Symbolic execution with intermediate masks: {intermediate_masks:X?}");
        let mut const_values = Vec::new();
        let mut symbolic_stack = ArrayVec::<_, 32>::new();

        for (op, &intermediate_mask) in self.ops.iter().zip(intermediate_masks.iter()) {
            let input_values: &[SymbolicValue] = &symbolic_stack[symbolic_stack.len() - op.num_args()..];

            trace!("{op:?} with input_values = {input_values:?}");

            let new_value = if input_values.iter().all(|v| v.as_i128().is_some()) {
                let mut stack = symbolic_stack
                    .drain(symbolic_stack.len() - op.num_args()..)
                    .map(|v| v.as_i128().unwrap())
                    .collect::<ArrayVec<_, 8>>();
                let top_of_stack = stack.pop().unwrap_or(0);
                let top_of_stack = op.eval_from_stack(
                    &|hole_index| {
                        let item = self.counter[hole_index];
                        self.const_values.get(item as usize).copied().unwrap_or(0)
                    },
                    top_of_stack,
                    &mut stack,
                );

                let is_const = if let Op::Hole(hole_index) = op {
                    self.counter[*hole_index as usize] != self.const_values.len() as u16
                } else {
                    true
                };

                if is_const {
                    SymbolicValue::from(top_of_stack)
                } else {
                    SymbolicValue::LIVE
                }
            } else {
                let mut stack = symbolic_stack
                    .drain(symbolic_stack.len() - op.num_args()..)
                    .collect::<ArrayVec<_, 8>>();

                let top = stack.pop().unwrap();

                match op {
                    Op::Hole(_) | Op::Const(_) => unreachable!(),
                    Op::Not => !top,
                    Op::Crop {
                        num_bits,
                    } => top.crop(*num_bits as u32),
                    Op::SignExtend {
                        num_bits,
                    } => top.sign_extend(*num_bits as u32),
                    Op::Select {
                        num_skip,
                        num_take,
                    } => (top >> *num_skip).crop(*num_take as u32),
                    Op::And => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a & b
                    },
                    Op::Or => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a | b
                    },
                    Op::Xor => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a ^ b
                    },
                    Op::IsZero => {
                        if top.any_const_one_bits() {
                            SymbolicValue::from(1)
                        } else {
                            SymbolicValue::LIVE.crop(1)
                        }
                    },
                    Op::Parity => {
                        let top = top.crop(8);
                        if let Some(const_value) = top.as_i128() {
                            SymbolicValue::from(ParityOp(Val(const_value)).compute(&|_| unreachable!()))
                        } else {
                            SymbolicValue::LIVE.crop(1)
                        }
                    },
                    Op::BitMask => SymbolicValue::bitmask(top),
                    Op::Sub => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a - b
                    },
                    Op::Add => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a + b
                    },
                    Op::Rol {
                        num_bits,
                    } => SymbolicValue::LIVE.crop(*num_bits as u32),
                    Op::CmpLt => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a.cmp_lt(b)
                    },
                    Op::TrailingZeros | Op::LeadingZeros | Op::PopCount => {
                        // At most 128 trailing/leading zeros or ones because we're using 128-bit numbers.
                        SymbolicValue::LIVE.crop(8)
                    },
                    Op::SwapBytes {
                        num_bits,
                    } => SymbolicValue::LIVE.crop(*num_bits as u32),
                    Op::Shl => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a << b
                    },
                    Op::Shr => {
                        let b = top;
                        let a = stack.pop().unwrap();

                        a >> b
                    },
                    Op::ByteMask
                    | Op::Mul
                    | Op::CarrylessMul
                    | Op::Div
                    | Op::UnsignedDiv
                    | Op::Rem
                    | Op::UnsignedRem
                    | Op::DepositBits
                    | Op::ExtractBits
                    | Op::IfZero => SymbolicValue::LIVE,
                }
            };

            let new_value = new_value.mask(intermediate_mask);

            trace!("Result: {new_value:?}");

            const_values.push(new_value);
            symbolic_stack.push(new_value);
        }

        const_values
    }

    pub fn run(&self) -> SymbolicExecutionResult {
        let mut intermediate_masks = self.compute_intermediate_masks(&vec![SymbolicValue::LIVE; self.ops.len()]);
        let const_values = loop {
            let const_values = self.symbolic_exec(&intermediate_masks);
            let new_intermediate_masks = self.compute_intermediate_masks(&const_values);
            debug_assert_eq!(const_values.len(), self.ops.len());

            if intermediate_masks == new_intermediate_masks {
                break const_values
            } else {
                intermediate_masks = new_intermediate_masks;
            }
        };

        trace!("Const values: {const_values:X?}");

        let const_values = const_values.iter().map(|val| val.as_i128()).collect::<Vec<_>>();

        debug!("Computing leaf constants for: {const_values:X?}");
        let mut eliminated = GrowingBitmap::new_all_zeros(self.ops.len());
        let mut index_stack: Vec<Vec<usize>> = Vec::new();
        for (index, (op, const_value)) in self.ops.iter().zip(const_values.iter()).enumerate() {
            let input_indices = &index_stack[index_stack.len() - op.num_args()..];
            if const_value.is_some() {
                trace!("Eliminating {input_indices:?}, because {index} is const: {const_value:?}");
                for &index in input_indices.iter().flat_map(|v| v.iter()) {
                    eliminated.set(index);
                }
            }

            let new_indexes = index_stack
                .drain(index_stack.len() - op.num_args()..)
                .flatten()
                .chain(once(index))
                .collect::<Vec<_>>();
            index_stack.push(new_indexes);
        }

        trace!("Elimination map: {eliminated:?}");
        let leaf_consts = const_values
            .iter()
            .enumerate()
            .filter(|(index, _)| !eliminated[index])
            .flat_map(|(index, const_value)| const_value.map(|const_value| (index, const_value)))
            .collect::<Vec<_>>();

        let const_output = *const_values.last().unwrap();
        trace!("Output value: {const_output:?}");
        SymbolicExecutionResult {
            leaf_consts,
            const_output,
        }
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::default::ops::Op;
    use test_log::test;

    use crate::templates::symexec::{SymbolicExecution, SymbolicExecutionResult, SymbolicValue};

    #[test]
    pub fn symbolic_and() {
        assert_eq!(
            SymbolicValue::LIVE & SymbolicValue::from(2i128),
            SymbolicValue {
                live_bits: 0b10,
                const_val: 0,
            }
        );
    }

    #[test]
    pub fn symbolic_add() {
        assert_eq!(SymbolicValue::from(123) + SymbolicValue::from(321), SymbolicValue::from(444));

        assert_eq!(
            SymbolicValue {
                live_bits: 0b0111,
                const_val: 0b0000,
            } + SymbolicValue::from(4),
            SymbolicValue {
                live_bits: 0b1111,
                const_val: 0b0000,
            }
        );

        assert_eq!(
            SymbolicValue {
                live_bits: 0b101,
                const_val: 0b000,
            } + SymbolicValue::from(2),
            SymbolicValue {
                live_bits: 0b101,
                const_val: 0b010,
            }
        );

        assert_eq!(
            SymbolicValue {
                live_bits: 0b10011,
                const_val: 0b01000,
            } + SymbolicValue {
                live_bits: 0b00001,
                const_val: 0b00000,
            },
            SymbolicValue {
                live_bits: 0b10111,
                const_val: 0b01000,
            }
        );

        assert_eq!(
            SymbolicValue {
                live_bits: 0b111,
                const_val: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8,
            } + SymbolicValue::from(1),
            SymbolicValue::LIVE
        );
    }

    #[test]
    pub fn symbolic_sub() {
        assert_eq!(
            SymbolicValue::from(0b10_1000) - SymbolicValue::LIVE.crop(2),
            SymbolicValue {
                live_bits: 0b001111,
                const_val: 0b100000,
            }
        );

        assert_eq!(SymbolicValue::from(312) - SymbolicValue::from(12), SymbolicValue::from(300));

        assert_eq!(
            SymbolicValue {
                live_bits: 0b0001,
                const_val: 0b0000,
            } - SymbolicValue::from(1),
            SymbolicValue::LIVE
        );

        assert_eq!(
            SymbolicValue {
                live_bits: 0b0_0001,
                const_val: 0b1_0000,
            } - SymbolicValue::from(1),
            SymbolicValue::LIVE.crop(5)
        );
    }

    #[test]
    pub fn symbolic_shr() {
        assert_eq!(
            SymbolicValue::from(0b10_0000) >> SymbolicValue::LIVE.crop(2),
            SymbolicValue {
                live_bits: 0b0011_1100,
                const_val: 0b0000_0000,
            }
        );

        assert_eq!(
            SymbolicValue::from(0b0000_1111_0000) >> SymbolicValue::LIVE.crop(2),
            SymbolicValue {
                live_bits: 0b1110_1110,
                const_val: 0b0001_0000,
            }
        );

        assert_eq!(SymbolicValue::LIVE >> SymbolicValue::from(120), SymbolicValue::LIVE);

        assert_eq!(
            (SymbolicValue::LIVE << SymbolicValue::from(127)) >> SymbolicValue::from(127),
            SymbolicValue::LIVE
        );
    }

    #[test]
    pub fn symbolic_shl() {
        assert_eq!(
            SymbolicValue::from(0b1_0000) << SymbolicValue::LIVE.crop(2),
            SymbolicValue {
                live_bits: 0b1111_0000,
                const_val: 0b0000_0000,
            }
        );

        assert_eq!(
            SymbolicValue::from(0b0000_1111_0000) << SymbolicValue::LIVE.crop(2),
            SymbolicValue {
                live_bits: 0b0111_0111_0000,
                const_val: 0b0000_1000_0000,
            }
        );
    }

    #[test]
    pub fn symbolic_bitmask() {
        assert_eq!(
            SymbolicValue::bitmask(SymbolicValue::from(2i128)),
            SymbolicValue {
                live_bits: 0b00,
                const_val: 0b11,
            }
        );

        assert_eq!(SymbolicValue::bitmask(SymbolicValue::LIVE), SymbolicValue::LIVE);
    }

    #[test]
    pub fn symbolic_cmp_lt() {
        assert_eq!(
            SymbolicValue::LIVE.crop(127).cmp_lt(SymbolicValue::from(-1)),
            SymbolicValue::from(0)
        );
        assert_eq!(
            (!SymbolicValue::LIVE.crop(127)).cmp_lt(SymbolicValue::from(0)),
            SymbolicValue::from(1)
        );
        assert_eq!(
            SymbolicValue::LIVE.crop(32).cmp_lt(SymbolicValue::from(0x2f << 0x30)),
            SymbolicValue::from(1)
        );
    }

    #[test]
    pub fn symexec_simple() {
        let ops = [
            Op::Hole(0),
            Op::Hole(2),
            Op::Hole(1),
            Op::Crop {
                num_bits: 3,
            },
            Op::Shl,
            Op::Or,
        ];

        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 3, 3], &[1, 2, 0x77], u128::MAX)
                .run()
                .leaf_consts,
            vec![]
        );
        assert_eq!(
            SymbolicExecution::new(&ops, &[0, 3, 3], &[1, 2, 0x77], u128::MAX)
                .run()
                .leaf_consts,
            vec![(0, 1)]
        );
        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 0, 3], &[1, 2, 0x77], u128::MAX)
                .run()
                .leaf_consts,
            vec![(3, 1)]
        );
        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 2, 3], &[1, 2, 0x77], u128::MAX)
                .run()
                .leaf_consts,
            vec![(3, 7)]
        );
        assert_eq!(
            SymbolicExecution::new(&ops, &[0, 0, 0], &[1, 2, 0x77], u128::MAX)
                .run()
                .leaf_consts,
            vec![(5, 3)]
        );
    }

    #[test]
    pub fn symexec_and_with_0() {
        let ops = [Op::Hole(0), Op::Hole(1), Op::And];

        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 0], &[0, 2, 0x77], u128::MAX).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(2, 0)],
                const_output: Some(0),
            }
        );
    }

    #[test]
    pub fn symexec_is_zero() {
        let ops = [Op::Hole(0), Op::Hole(1), Op::And, Op::IsZero];
        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 1], &[0, 2, 0x77], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(1, 2)],
                const_output: None,
            }
        );

        let ops = [Op::Hole(0), Op::IsZero];
        assert_eq!(
            SymbolicExecution::new(&ops, &[3], &[0, 2, 0x77], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![],
                const_output: None,
            }
        );

        let ops = [
            Op::Hole(0),
            Op::Hole(1),
            Op::Mul,
            Op::Hole(2),
            Op::Crop {
                num_bits: 5,
            },
            Op::Shr,
            Op::IsZero,
        ];
        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 3, 0], &[13, 2, 0x77], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(4, 13)],
                const_output: None,
            }
        );
    }

    #[test]
    pub fn symexec_crop_shift() {
        let ops = [
            Op::Hole(0),
            Op::Hole(1),
            Op::Mul,
            Op::Crop {
                num_bits: 8,
            },
            Op::Hole(2),
            Op::Shr,
            Op::IsZero,
        ];
        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 3, 2], &[0, 2, 0x77], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(6, 1)],
                const_output: Some(1),
            }
        );
    }

    #[test]
    pub fn symexec_crop_const() {
        let ops = [
            Op::Hole(0),
            Op::Crop {
                num_bits: 3,
            },
            Op::Hole(1),
            Op::Add,
            Op::IsZero,
        ];
        assert_eq!(
            SymbolicExecution::new(&ops, &[2, 3], &[0, 2, 0x77], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(1, 0x7)],
                const_output: None,
            }
        );
    }

    #[test]
    pub fn symexec_shl_crop() {
        let ops = [
            Op::Hole(0),
            Op::Hole(1),
            Op::Shl,
            Op::Hole(2),
            Op::Or,
            Op::Crop {
                num_bits: 32,
            },
            Op::IsZero,
        ];
        assert_eq!(
            SymbolicExecution::new(&ops, &[3, 2, 3], &[0, 2, 0x77], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(2, 0)],
                const_output: None,
            }
        );
    }

    #[test]
    pub fn symexec_select_crop_add() {
        let ops = [
            Op::Hole(0),
            Op::Hole(1),
            Op::Hole(2),
            Op::Sub,
            Op::Crop {
                num_bits: 64,
            },
            Op::Add,
            Op::Select {
                num_skip: 7,
                num_take: 1,
            },
        ];
        assert_eq!(
            SymbolicExecution::new(&ops, &[1, 0, 1], &[0, 1], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(6, 0)],
                const_output: Some(0),
            }
        );
    }

    #[test]
    pub fn symexec_iszero_mult() {
        let ops = [
            Op::Hole(0),
            Op::Hole(1),
            Op::Mul,
            Op::Hole(2),
            Op::Shr,
            Op::IsZero,
            Op::Hole(0),
            Op::Hole(1),
            Op::Mul,
            Op::Hole(2),
            Op::Shr,
            Op::Not,
            Op::IsZero,
            Op::Or,
            Op::Crop {
                num_bits: 64,
            },
            Op::IsZero,
        ];

        assert_eq!(
            SymbolicExecution::new(&ops, &[1, 1, 0], &[0x1F], 1).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(3, 31), (9, 31)],
                const_output: None,
            }
        );
    }

    #[test]
    pub fn symexec_shld() {
        // (B << 20) | ((A << 20) >> 32)
        let ops = [
            Op::Hole(1),
            Op::Hole(2),
            Op::Shl,
            Op::Hole(0),
            Op::Hole(2),
            Op::Shl,
            Op::Hole(3),
            Op::Shr,
            Op::Or,
        ];

        assert_eq!(
            SymbolicExecution::new(&ops, &[2, 2, 0, 1], &[20, 32], u128::MAX).run(),
            SymbolicExecutionResult {
                leaf_consts: vec![(1, 20), (4, 20), (6, 32)],
                const_output: None,
            }
        );
    }
}
