use liblisa::semantics::IoType;
use liblisa::value::OwnedValue;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct InputHash(u64);

#[derive(Copy, Clone, Debug)]
pub struct InputsEqualQuery(u64);

impl InputsEqualQuery {
    /// Returns false if lhs and rhs are not equal in the input indices specified when creating the query.
    /// Returns true if it is *possible* that lhs and rhs are equal.
    /// You should always perform a comparison of the real inputs to determine whether the inputs are actually equal.
    pub fn check(&self, lhs: InputHash, rhs: InputHash) -> bool {
        let differing_bits = lhs.0 ^ rhs.0;

        // If none of the bits we care about differ, the input indices specified when creating the query *might* be equal.
        differing_bits & self.0 == 0
    }
}

#[derive(Clone, Debug)]
struct Input {
    ty: IoType,
    num_bits: usize,
    mask: u64,
    values: Vec<OwnedValue>,
}

/// Comparing `[OwnedValue]`s can be expensive.
/// The `InputHasher` can compute hashes for a `[OwnedValue]`.
/// These hashes can then be used to more quickly filter `[OwnedValue]`s that don't match.
///
/// The hashes support checking for partial equality via [`InputsEqualQuery`],
/// which can be created by calling `create_inputs_equal_query[_inv]`.
///
/// The number of bits in the hash per input is scaled based on the input types.
/// 1-bit inputs always use a perfect hash.
/// Larger inputs use a perfect hash when possible within the number of bits used for the input.
#[derive(Clone, Debug)]
pub(crate) struct InputHasher {
    inputs: Vec<Input>,
}

impl InputHasher {
    pub fn new(input_types: &[IoType]) -> InputHasher {
        if input_types.is_empty() {
            return InputHasher {
                inputs: Vec::new(),
            };
        }

        let bits_per_input = 64 / input_types.len();

        let mut inputs = input_types
            .iter()
            .map(|&ty| Input {
                ty,
                num_bits: ty.num_bits().min(bits_per_input),
                mask: 0,
                values: Vec::new(),
            })
            .collect::<Vec<_>>();

        let mut bits_in_use = inputs.iter().map(|i| i.num_bits).sum::<usize>();

        loop {
            let mut done = true;
            for input in inputs.iter_mut() {
                if input.num_bits < input.ty.num_bits() {
                    done = false;
                    input.num_bits += 1;
                    input.mask = (input.mask << 1) | 1;
                    bits_in_use += 1;

                    if bits_in_use >= 64 {
                        break
                    }
                }
            }

            if done {
                break
            }
        }

        InputHasher {
            inputs,
        }
    }

    pub fn hash(&mut self, inputs: &[OwnedValue]) -> InputHash {
        let mut result: u64 = 0;
        for (val, input) in inputs.iter().zip(self.inputs.iter_mut()).rev() {
            let index = if let Some(pos) = input.values.iter().position(|v| v == val) {
                pos
            } else {
                let pos = input.values.len();
                input.values.push(val.clone());
                pos
            };

            result = (result.wrapping_shl(input.num_bits as u32)) | (index as u64 & input.mask);
        }

        InputHash(result)
    }

    fn create_mask(&self, indices: &[usize]) -> u64 {
        let mut result: u64 = 0;
        for (index, input) in self.inputs.iter().enumerate().rev() {
            let val = if indices.contains(&index) { input.mask } else { 0 };

            result = result.wrapping_shl(input.num_bits as u32) | val;
        }

        result
    }

    /// Creates a query that checks whether all inputs except the inputs in `indices_that_may_be_unequal` are equal.
    pub fn create_inputs_equal_query_inv(&self, indices_that_may_be_unequal: &[usize]) -> InputsEqualQuery {
        InputsEqualQuery(!self.create_mask(indices_that_may_be_unequal))
    }
}
