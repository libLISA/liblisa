use std::fmt::{Debug, Write};
use std::iter::repeat;

use arrayvec::ArrayVec;
use serde::{Deserialize, Serialize};

use super::{Bitmap, BitmapSlice, GrowingBitmap};

/// A bitmap of a fixed multiple of 64-bit blocks.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, arbitrary::Arbitrary)]
pub struct FixedBitmapU64<const N: usize = 1> {
    data: [u64; N],
}

impl<const N: usize> Default for FixedBitmapU64<N> {
    fn default() -> Self {
        Self {
            data: [0; N],
        }
    }
}

impl<const N: usize> Serialize for FixedBitmapU64<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        (&self.data as &[_]).serialize(serializer)
    }
}

impl<'de, const N: usize> Deserialize<'de> for FixedBitmapU64<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let items = ArrayVec::<u64, N>::deserialize(deserializer)?;
        Ok(Self {
            data: items.as_slice().try_into().unwrap(),
        })
    }
}

impl<const N: usize> FixedBitmapU64<N> {
    #[inline]
    fn index(x: usize) -> (usize, usize) {
        (x / 64, x % 64)
    }
}

impl FixedBitmapU64<1> {
    /// Creates a new bitmap, using `value` as the bitmap data.
    /// The bit N in the bitmap is set if the Nth bit in `value` is set.
    pub fn from_u64(value: u64) -> Self {
        Self {
            data: [value],
        }
    }

    /// Converts the bitmap to a `u64`.
    pub fn as_u64(&self) -> u64 {
        self.data[0]
    }
}

impl<const N: usize> FromIterator<bool> for FixedBitmapU64<N> {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut new = Self::default();
        for (index, b) in iter.into_iter().enumerate() {
            if index >= new.len() {
                panic!("Iterator returns more than {} items", new.len());
            }

            if b {
                new.set(index);
            }
        }

        new
    }
}

impl<const N: usize> FromIterator<usize> for FixedBitmapU64<N> {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        let mut v = Self::default();
        for item in iter {
            v.set(item);
        }

        v
    }
}

impl<const N: usize> From<&[usize]> for FixedBitmapU64<N> {
    fn from(items: &[usize]) -> Self {
        items.iter().copied().collect()
    }
}

impl<const N: usize, const K: usize> From<[usize; K]> for FixedBitmapU64<N> {
    fn from(items: [usize; K]) -> Self {
        items.into_iter().collect()
    }
}

impl<const N: usize> Bitmap for FixedBitmapU64<N> {
    fn set(&mut self, index: usize) -> bool {
        let (index, offset) = Self::index(index);

        let mask = 1 << offset;
        let changed = self.data[index] & mask == 0;
        self.data[index] |= mask;

        changed
    }

    fn clear(&mut self, index: usize) -> bool {
        let (index, offset) = Self::index(index);

        let mask = 1 << offset;
        let changed = self.data[index] & mask != 0;
        self.data[index] &= !mask;

        changed
    }

    fn and_with(&mut self, other: &impl BitmapSlice) -> bool {
        let mut changed = false;
        for (a, b) in self.data.iter_mut().zip(other.iter_data().chain(repeat(0))) {
            let new = *a & b;
            changed |= *a != new;
            *a = new;
        }

        changed
    }

    fn clear_from(&mut self, other: &impl BitmapSlice) -> bool {
        let mut changed = false;
        for (a, b) in self.data.iter_mut().zip(other.iter_data().chain(repeat(0))) {
            let new = *a & !b;
            changed |= *a != new;
            *a = new;
        }

        changed
    }

    fn or_with(&mut self, other: &impl BitmapSlice) -> bool {
        let mut changed = false;
        for (a, b) in self.data.iter_mut().zip(other.iter_data().chain(repeat(0))) {
            let new = *a | b;
            changed |= *a != new;
            *a = new;
        }

        changed
    }

    fn xor_with(&mut self, other: &impl BitmapSlice) -> bool {
        let mut changed = false;
        for (a, b) in self.data.iter_mut().zip(other.iter_data().chain(repeat(0))) {
            let new = *a ^ b;
            changed |= *a != new;
            *a = new;
        }

        changed
    }

    fn is_all_ones(&self) -> bool {
        self.data.iter().all(|&x| x == u64::MAX)
    }

    fn is_superset_of(&self, other: &Self) -> bool {
        self.data.iter().zip(other.data.iter()).all(|(&a, &b)| a | b == a)
    }

    #[inline]
    fn new_all_zeros(len: usize) -> Self {
        assert!(len <= N * 64, "Size {len} is too big for FixedBitmapU64<{}>", N);
        Self {
            data: [0; N],
        }
    }

    fn new_all_ones(mut len: usize) -> Self {
        let mut result = Self::new_all_zeros(len);
        let mut index = 0;
        while len >= 64 {
            result.data[index] = u64::MAX;
            index += 1;
            len -= 64;
        }

        if len > 0 {
            assert!(len < 64);
            result.data[index] = u64::MAX >> (64 - len);
        }

        result
    }
}

impl<const N: usize> TryFrom<&GrowingBitmap> for FixedBitmapU64<N> {
    type Error = ();

    fn try_from(value: &GrowingBitmap) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Ok(Self::default())
        } else if value.len() <= 64 * N {
            let mut index = 0;
            Ok(FixedBitmapU64 {
                data: [(); N].map(|_| {
                    let result = *value.data().get(index).unwrap_or(&0);
                    index += 1;
                    result
                }),
            })
        } else {
            Err(())
        }
    }
}

impl<const N: usize> Debug for FixedBitmapU64<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for index in 0..N * 64 {
            f.write_char(if self.get(index) { '1' } else { '0' })?;
        }

        Ok(())
    }
}

impl<const N: usize> BitmapSlice for FixedBitmapU64<N> {
    fn get(&self, index: usize) -> bool {
        let (index, offset) = Self::index(index);
        (*self.data.get(index).unwrap_or(&0) >> offset) & 1 != 0
    }

    fn len(&self) -> usize {
        N * 64
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.data.iter().copied()
    }
}

impl<const N: usize> FixedBitmapU64<N> {
    /// Iterates over the indices of the bits that are one, starting at the highest index.
    pub fn iter_one_indices_rev(&self) -> impl Iterator<Item = usize> + '_ {
        self.data.iter().copied().enumerate().rev().flat_map(|(offset, item)| {
            (0..64)
                .rev()
                .filter(move |index| (item >> index) & 1 != 0)
                .map(move |index| index + offset * 64)
        })
    }
}
