use std::collections::HashMap;
use std::iter::repeat;

use log::trace;

use crate::arch::Arch;
use crate::encoding::bitpattern::{Bit, Part};
use crate::encoding::Encoding;
use crate::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};

#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct Mapping {
    a_indices: FixedBitmapU64<1>,
    b_indices: FixedBitmapU64<1>,
    a_to_b: Vec<Option<usize>>,
    b_to_a: Vec<Option<usize>>,
}

impl Mapping {
    pub fn of(a: impl Iterator<Item = (Bit, bool)>, b: impl Iterator<Item = (Bit, bool)>) -> Option<Mapping> {
        use Bit::*;

        let mut a_indices = FixedBitmapU64::new_all_zeros(64);
        let mut b_indices = FixedBitmapU64::new_all_zeros(64);

        let mut a_len = 0;
        let mut b_len = 0;

        let mut mapping = HashMap::new();
        let mut reverse_mapping = HashMap::new();
        for ((bit_a, use_a), (bit_b, use_b)) in a.zip(b) {
            if let Part(x) = bit_a {
                if use_a {
                    a_len = a_len.max(x + 1);
                    a_indices.set(x);
                }
            }

            if let Part(y) = bit_b {
                if use_b {
                    b_len = b_len.max(y + 1);
                    b_indices.set(y);
                }
            }

            if use_a && use_b {
                match (bit_a, bit_b) {
                    (Part(x), Part(y)) => {
                        if let Some(&prev_y) = mapping.get(&x) {
                            if prev_y != y {
                                return None
                            }
                        } else {
                            mapping.insert(x, y);
                        }

                        if let Some(&prev_x) = reverse_mapping.get(&y) {
                            if prev_x != x {
                                return None
                            }
                        } else {
                            reverse_mapping.insert(y, x);
                        }
                    },
                    (Part(_) | DontCare, Fixed(_) | DontCare) | (Fixed(_) | DontCare, Part(_) | DontCare) => (),
                    (Fixed(x), Fixed(y)) => {
                        if x != y {
                            return None
                        }
                    },
                }
            }
        }

        trace!("Mapping: {mapping:?}, reverse mapping: {reverse_mapping:?}");
        let mut b_to_a = repeat(None).take(b_len).collect::<Vec<_>>();
        let mut a_to_b = repeat(None).take(a_len).collect::<Vec<_>>();

        for (&x, &y) in mapping.iter() {
            b_to_a[y] = Some(x);
            a_to_b[x] = Some(y);
        }

        Some(Mapping {
            a_indices,
            b_indices,
            a_to_b,
            b_to_a,
        })
    }

    pub fn b_to_a(&self, part_index: usize) -> usize {
        self.b_to_a[part_index].unwrap()
    }

    pub fn a_to_b(&self, part_index: usize) -> usize {
        self.a_to_b[part_index].unwrap()
    }

    pub fn try_b_to_a(&self, part_index: usize) -> Option<usize> {
        self.b_to_a.get(part_index).copied().flatten()
    }

    pub fn try_a_to_b(&self, part_index: usize) -> Option<usize> {
        self.a_to_b.get(part_index).copied().flatten()
    }

    pub fn all_indices_mapped(&self) -> bool {
        self.b_indices
            .iter_one_indices()
            .all(|b_index| self.try_b_to_a(b_index).is_some())
            && self
                .a_indices
                .iter_one_indices()
                .all(|a_index| self.try_a_to_b(a_index).is_some())
    }
}

/// A mapping between part indices of two encodings.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct PartIndexMapping {
    pub(crate) imms: Mapping,
    pub(crate) dataflow_regs: Mapping,
}

impl PartIndexMapping {
    /// Determines the mapping of part indices between the two encodings.
    /// If such a mapping does not exist, `None` is returned.
    pub fn of<A: Arch, C>(a: &Encoding<A, C>, b: &Encoding<A, C>) -> Option<PartIndexMapping> {
        for (&bit_a, &bit_b) in a.bits.iter().zip(b.bits.iter()) {
            if let (Bit::Fixed(x), Bit::Fixed(y)) = (bit_a, bit_b) {
                if x != y {
                    trace!("Fixed bits don't match");
                    return None
                }
            }
        }

        let imms = Mapping::of(
            a.bits.iter().map(|&bit| {
                (
                    bit,
                    a.is_bit_imm(bit) && a.is_bit_involved_with_address_reg_or_computation(bit),
                )
            }),
            b.bits.iter().map(|&bit| {
                (
                    bit,
                    b.is_bit_imm(bit) && b.is_bit_involved_with_address_reg_or_computation(bit),
                )
            }),
        )?;

        let dataflow_regs = Mapping::of(
            a.bits
                .iter()
                .map(|&bit| (bit, a.is_bit_involved_with_dataflow_reg(bit) && !a.is_bit_dataflow_imm(bit))),
            b.bits
                .iter()
                .map(|&bit| (bit, b.is_bit_involved_with_dataflow_reg(bit) && !b.is_bit_dataflow_imm(bit))),
        )?;

        if !imms.all_indices_mapped() {
            trace!("Not all immediate value indices are mapped");
            return None
        }

        Some(PartIndexMapping {
            imms,
            dataflow_regs,
        })
    }

    pub(crate) fn iter_dataflow_involved_parts<'a, A: Arch, C>(
        &'a self, a: &'a Encoding<A, C>, b: &'a Encoding<A, C>,
    ) -> impl Iterator<Item = ((usize, &'a Part<A>), (usize, &'a Part<A>))> + 'a {
        self.dataflow_regs.a_indices.iter_one_indices().flat_map(move |a_part_index| {
            self.dataflow_regs
                .try_a_to_b(a_part_index)
                .map(|b_part_index| ((a_part_index, &a.parts[a_part_index]), (b_part_index, &b.parts[b_part_index])))
        })
    }

    pub(crate) fn b_imm_to_a(&self, part_index: usize) -> usize {
        self.imms.b_to_a(part_index)
    }

    pub(crate) fn try_a_dataflow_part_to_b(&self, part_index: usize) -> Option<usize> {
        self.dataflow_regs.try_a_to_b(part_index)
    }

    pub(crate) fn try_b_dataflow_part_to_a(&self, part_index: usize) -> Option<usize> {
        self.dataflow_regs.try_b_to_a(part_index)
    }
}
