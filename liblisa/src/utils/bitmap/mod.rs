//! Memory-efficient implementations of 1D bitmaps.

mod fixed;
mod growing;
mod tiny;

use std::iter::repeat;

// pub use tiny::TinyBitmap56;
pub use fixed::FixedBitmapU64;
pub use growing::{DenseSet, GrowingBitmap};
use itertools::{EitherOrBoth, Itertools};

/// A writable bitmap.
pub trait Bitmap: BitmapSlice {
    /// Creates a new bitmap with all bits set to zero.
    fn new_all_zeros(len: usize) -> Self;

    /// Creates a new bitmap with all bits set to one.
    fn new_all_ones(len: usize) -> Self;

    /// Sets the bit at position `index` to one.
    fn set(&mut self, index: usize) -> bool;

    /// Sets all bits in `indices` to one.
    fn set_many(&mut self, indices: impl Iterator<Item = usize>) {
        for item in indices {
            self.set(item);
        }
    }

    /// Sets the bit at position `index` to zero.
    fn clear(&mut self, index: usize) -> bool;

    /// Sets all bits in `indices` to zero.
    fn clear_many(&mut self, indices: impl Iterator<Item = usize>) {
        for item in indices {
            self.clear(item);
        }
    }

    /// ANDs the slice with `other`. Returns true if anything changed.
    fn and_with(&mut self, other: &impl BitmapSlice) -> bool;

    /// Computes `self & !other`. Returns true if anything changed.
    fn clear_from(&mut self, other: &impl BitmapSlice) -> bool;

    /// ORs the slice with `other`. Returns true if anything changed.
    fn or_with(&mut self, other: &impl BitmapSlice) -> bool;

    /// XORs the slice with `other`. Returns true if anything changed.
    fn xor_with(&mut self, other: &impl BitmapSlice) -> bool;

    /// Returns true if the bitmap contains only ones.
    fn is_all_ones(&self) -> bool;

    /// Returns true if the bitmap is a superset of `other`.
    /// In other words: for every bit that is set in `other`, it should also be set in `self`.
    fn is_superset_of(&self, other: &Self) -> bool;
}

/// A bitmap that can be resized.
pub trait ResizableBitmap {
    /// Resizes the bitmap to be `new_size` bits long.
    /// Inserts zeros if the bitmap grows.
    fn resize(&mut self, new_size: usize);
}

/// A read-only bitmap slice.
pub trait BitmapSlice {
    /// Returns the value of the bit at position `index`.
    fn get(&self, index: usize) -> bool;

    /// Returns the number of bits in the bitmap.
    fn len(&self) -> usize;

    /// Return true if the bitmap is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Counts the number of bits that are one in both this bitmap and `other`.
    fn count_overlapping_with(&self, other: &impl BitmapSlice) -> usize
    where
        Self: Sized,
    {
        self.anded_with(other)
            .iter_data()
            .map(|x| x.count_ones() as usize)
            .sum::<usize>()
    }

    /// Returns true if the bitmap overlaps with `other`.
    /// In other words, if there is any bit which is set in both bitmaps.
    fn overlaps_with(&self, other: &impl BitmapSlice) -> bool
    where
        Self: Sized,
    {
        self.anded_with(other).iter_data().any(|x| x != 0)
    }

    /// Returns true if all bits in the bitmap are set to one.
    fn is_all_zeros(&self) -> bool {
        self.iter_data().all(|x| x == 0)
    }

    /// Returns true if, for all bits set in the bitmap, it is also set in `other`.
    fn is_subset_of(&self, other: &impl BitmapSlice) -> bool {
        self.iter_data()
            .chain(repeat(0))
            .zip(other.iter_data())
            .all(|(subset, whole)| subset | whole == whole)
    }

    /// Returns a slice to a bitmap where each bit is negated.
    fn flipped(&self) -> Flipped<Self>
    where
        Self: Sized,
    {
        Flipped(self)
    }

    /// Returns a slice to a bitmap where each bit is ANDed with `other`.
    fn anded_with<'r, B: BitmapSlice>(&'r self, other: &'r B) -> AndWith<'r, Self, B>
    where
        Self: Sized,
    {
        AndWith {
            a: self,
            b: other,
        }
    }

    /// Returns a slice to a bitmap where each bit is XORed with `other`.
    fn xored_with<'r, B: BitmapSlice>(&'r self, other: &'r B) -> XorWith<'r, Self, B>
    where
        Self: Sized,
    {
        XorWith {
            a: self,
            b: other,
        }
    }

    /// Returns a slice to a bitmap where each bit is ORed with `other`.
    fn ored_with<'r, B: BitmapSlice>(&'r self, other: &'r B) -> OrWith<'r, Self, B>
    where
        Self: Sized,
    {
        OrWith {
            a: self,
            b: other,
        }
    }

    /// Returns a slice to a bitmap where each bit is set to `self & !other`.
    fn cleared_from<'r, B: BitmapSlice>(&'r self, other: &'r B) -> ClearFrom<'r, Self, B>
    where
        Self: Sized,
    {
        ClearFrom {
            a: self,
            b: other,
        }
    }

    /// Iterates over all indices in the bitmap that are set to one.
    fn iter_one_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.iter_data().enumerate().flat_map(|(offset, item)| {
            (0..64)
                .filter(move |index| (item >> index) & 1 != 0)
                .map(move |index| index + offset * 64)
        })
    }

    /// Iterates over all bits in the bitmap.
    fn iter(&self) -> impl Iterator<Item = bool> + '_ {
        self.iter_data()
            .flat_map(|val| (0..64).map(move |index| (val >> index) & 1 != 0))
    }

    /// Counts the number of bits that are one.
    fn count_ones(&self) -> usize {
        self.iter_data().map(|x| x.count_ones() as usize).sum::<usize>()
    }

    /// Counts the number of bits that are zero.
    fn count_zeros(&self) -> usize {
        self.iter_data().map(|x| x.count_zeros() as usize).sum::<usize>() - (64 - self.len() % 64)
    }

    /// Iterates over the internal backing data of the bitmap.
    fn iter_data(&self) -> impl Iterator<Item = u64> + '_;
}

/// A mutable bitmap slice.
pub trait BitmapSliceMut: BitmapSlice {
    /// Sets all bits in the bitmap to 0.
    fn clear(&mut self) {
        self.modify(|_| 0);
    }

    /// Overwrites all bits in the bitmap with bits from `other`.
    ///
    /// Panics if `other` is smaller than `self`.
    fn copy_from(&mut self, other: &impl BitmapSlice) {
        assert_eq!(self.len(), other.len());

        let mut iter = other.iter_data();
        self.modify(|_| iter.next().expect("Should succeed because self.len() == other.len()"));
    }

    /// ANDs each bit in the bitmap with `!other`.
    ///
    /// Panics if `other` is smaller than `self`.
    fn clear_from(&mut self, other: &impl BitmapSlice) {
        let mut iter = other.iter_data();
        self.modify(|d| d & !iter.next().unwrap_or(0));
    }

    /// ORs each bit in the bitmap with `other`.
    ///
    /// Panics if `other` is smaller than `self`
    fn or_with(&mut self, other: &impl BitmapSlice) {
        let mut iter = other.iter_data();
        self.modify(|d| d | iter.next().unwrap_or(0));
    }

    /// Modifies the backing data according to `f`.
    fn modify(&mut self, f: impl FnMut(u64) -> u64);
}

/// A bitmap slice that is the result of ANDing two slices.
#[derive(Copy, Clone)]
pub struct AndWith<'r, A, B> {
    a: &'r A,
    b: &'r B,
}

impl<A: BitmapSlice, B: BitmapSlice> BitmapSlice for AndWith<'_, A, B> {
    fn get(&self, index: usize) -> bool {
        self.a.get(index) && self.b.get(index)
    }

    fn len(&self) -> usize {
        self.a.len().min(self.b.len())
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.a.iter_data().zip(self.b.iter_data()).map(|(a, b)| a & b)
    }
}

/// A bitmap slice that is the result of ORing two slices.
#[derive(Copy, Clone)]
pub struct OrWith<'r, A, B> {
    a: &'r A,
    b: &'r B,
}

impl<A: BitmapSlice, B: BitmapSlice> BitmapSlice for OrWith<'_, A, B> {
    fn get(&self, index: usize) -> bool {
        self.a.get(index) || self.b.get(index)
    }

    fn len(&self) -> usize {
        self.a.len().max(self.b.len())
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.a.iter_data().zip_longest(self.b.iter_data()).map(|v| match v {
            EitherOrBoth::Both(a, b) => a | b,
            EitherOrBoth::Left(x) | EitherOrBoth::Right(x) => x,
        })
    }
}

/// A bitmap slice that is the result of XORing two slices.
#[derive(Copy, Clone)]
pub struct XorWith<'r, A, B> {
    a: &'r A,
    b: &'r B,
}

impl<A: BitmapSlice, B: BitmapSlice> BitmapSlice for XorWith<'_, A, B> {
    fn get(&self, index: usize) -> bool {
        self.a.get(index) ^ self.b.get(index)
    }

    fn len(&self) -> usize {
        self.a.len().max(self.b.len())
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.a.iter_data().zip_longest(self.b.iter_data()).map(|v| match v {
            EitherOrBoth::Both(a, b) => a ^ b,
            EitherOrBoth::Left(x) | EitherOrBoth::Right(x) => x,
        })
    }
}

/// A bitmap slice that is the result of `(a & !b)`
#[derive(Copy, Clone)]
pub struct ClearFrom<'r, A, B> {
    a: &'r A,
    b: &'r B,
}

impl<A: BitmapSlice, B: BitmapSlice> BitmapSlice for ClearFrom<'_, A, B> {
    fn get(&self, index: usize) -> bool {
        self.a.get(index) && !self.b.get(index)
    }

    fn len(&self) -> usize {
        self.a.len()
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.a
            .iter_data()
            .zip(self.b.iter_data().chain(repeat(0)))
            .map(|(a, b)| a & !b)
    }
}

/// A bitmap slice where all bits are flipped compared to the original slice.
#[derive(Copy, Clone)]
pub struct Flipped<'r, A>(&'r A);

impl<A: BitmapSlice> BitmapSlice for Flipped<'_, A> {
    fn get(&self, index: usize) -> bool {
        !self.0.get(index)
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        let mut remaining = self.len();
        self.0.iter_data().map(move |x| {
            if remaining >= 64 {
                remaining -= 64;
                !x
            } else {
                !x & ((1 << remaining) - 1)
            }
        })
    }
}

/// A read-only bitmap filled with only ones
pub struct AllOnes;

/// A read-only bitmap filled with only zeros
pub struct AllZeros;

impl BitmapSlice for AllOnes {
    fn get(&self, _index: usize) -> bool {
        true
    }

    fn len(&self) -> usize {
        usize::MAX
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        repeat(u64::MAX)
    }
}

impl BitmapSlice for AllZeros {
    fn get(&self, _index: usize) -> bool {
        false
    }

    fn len(&self) -> usize {
        usize::MAX
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        repeat(0)
    }
}
