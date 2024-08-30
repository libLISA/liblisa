use super::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};
use super::MinimumCoveringSet;

pub struct MinCoverWithExclusions<'a> {
    num_bits: usize,
    exclude: &'a [u64],
    fixed: FixedBitmapU64<1>,
    value: FixedBitmapU64<1>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitFilter {
    pub bit_is_fixed: FixedBitmapU64<1>,
    pub value: u64,
}

impl BitFilter {
    pub fn matches(&self, value: u64) -> bool {
        value & self.bit_is_fixed.as_u64() == self.value
    }
}

impl<'a> MinCoverWithExclusions<'a> {
    pub fn new(exclude: &'a [u64], num_bits: usize) -> Self {
        assert!(num_bits <= 64);
        Self {
            num_bits,
            exclude,
            fixed: FixedBitmapU64::new_all_zeros(num_bits),
            value: FixedBitmapU64::new_all_zeros(num_bits),
        }
    }

    pub fn into_bit_filters(mut self) -> Vec<BitFilter> {
        let mut results = Vec::new();

        if self.exclude.len() < 64 {
            let applicable = FixedBitmapU64::<1>::new_all_ones(self.exclude.len());
            self.run_internal(&applicable, &mut results);
        } else if self.exclude.len() < 128 {
            let applicable = FixedBitmapU64::<2>::new_all_ones(self.exclude.len());
            self.run_internal(&applicable, &mut results);
        } else if self.exclude.len() < 1024 {
            let applicable = FixedBitmapU64::<16>::new_all_ones(self.exclude.len());
            self.run_internal(&applicable, &mut results);
        } else {
            panic!("Too many excludes: {}", self.exclude.len());
        }

        results.sort_by_key(|filter| filter.bit_is_fixed.count_ones());

        let decisions = (0..1 << self.num_bits)
            .filter(|value| !self.exclude.contains(value))
            .map(|value| {
                results
                    .iter()
                    .enumerate()
                    .filter(|(_, filter)| filter.matches(value))
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        if decisions.iter().any(|d| d.is_empty()) {
            panic!(
                "Cannot find minimal cover with exclusions {:?} and num_bits = {}",
                self.exclude, self.num_bits
            )
        }

        let mcs = MinimumCoveringSet::of(decisions, results.len());

        mcs.into_vec().into_iter().map(|index| results[index].clone()).collect()
    }

    fn run_internal<const N: usize>(&mut self, applicable: &FixedBitmapU64<N>, result: &mut Vec<BitFilter>) {
        match applicable.count_ones() {
            0 => result.push(BitFilter {
                bit_is_fixed: self.fixed.clone(),
                value: self.value.iter_data().next().unwrap(),
            }),
            _ => {
                for split_index in 0..self.num_bits {
                    if self.fixed.set(split_index) {
                        // Consider cases where split_index = 1
                        self.value.set(split_index);
                        let mut new_applicable = applicable.clone();
                        for (index, exclude) in self.exclude.iter().enumerate() {
                            if (exclude >> split_index) & 1 == 0 {
                                new_applicable.clear(index);
                            }
                        }

                        self.run_internal(&new_applicable, result);

                        // Consider cases where split_index = 0
                        self.value.clear(split_index);
                        let mut new_applicable = applicable.clone();
                        for (index, exclude) in self.exclude.iter().enumerate() {
                            if (exclude >> split_index) & 1 != 0 {
                                new_applicable.clear(index);
                            }
                        }

                        self.run_internal(&new_applicable, result);

                        self.fixed.clear(split_index);
                    }
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::bitmap::FixedBitmapU64;
    use crate::utils::min_cover_with_exclusions::{BitFilter, MinCoverWithExclusions};

    #[test]
    pub fn single_exclusion() {
        assert_eq!(
            MinCoverWithExclusions::new(&[0b1010], 4).into_bit_filters(),
            vec![
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b0001),
                    value: 0b0001,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b0010),
                    value: 0b0000,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b0100),
                    value: 0b0100,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b1000),
                    value: 0b0000,
                },
            ]
        );

        assert_eq!(
            MinCoverWithExclusions::new(&[0b101], 3).into_bit_filters(),
            vec![
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b001),
                    value: 0b000,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b010),
                    value: 0b010,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b100),
                    value: 0b000,
                },
            ]
        );

        assert_eq!(
            MinCoverWithExclusions::new(&[0b100], 3).into_bit_filters(),
            vec![
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b001),
                    value: 0b001,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b010),
                    value: 0b010,
                },
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b100),
                    value: 0b000,
                },
            ]
        );
    }

    #[test]
    pub fn double_exclusion() {
        assert_eq!(
            MinCoverWithExclusions::new(&[0b1010, 0b0101], 4).into_bit_filters(),
            vec![
                // __11
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b0011),
                    value: 0b0011,
                },
                // _1_0
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b0101),
                    value: 0b0100,
                },
                // 1_0_
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b1010),
                    value: 0b1000,
                },
                // 00__
                BitFilter {
                    bit_is_fixed: FixedBitmapU64::from_u64(0b1100),
                    value: 0b0000,
                },
            ]
        );
    }
}
