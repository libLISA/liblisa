use std::fmt::{Debug, Write};
use std::hash::Hash;
use std::iter::repeat;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Index, Range};

use super::{BitmapSlice, BitmapSliceMut};

/// A bitmap that is automatically resized whenever an element higher than the maximum capacity of the bitmap is set.
/// Newly added bits are initialized to `0` (unset).
#[derive(Default, Eq)]
pub struct GrowingBitmap {
    data: Vec<u64>,
    len: usize,
}

impl GrowingBitmap {
    /// An empty bitmap
    pub const EMPTY: &'static GrowingBitmap = &GrowingBitmap::new();

    /// Creates a new, empty, bitmap
    pub const fn new() -> Self {
        GrowingBitmap {
            data: Vec::new(),
            len: 0,
        }
    }

    /// Creates a bitmap and fills it with the data from `slice`.
    pub fn from_slice(slice: &impl BitmapSlice) -> Self {
        let data = slice.iter_data().collect::<Vec<_>>();

        debug_assert_eq!(data.len(), (slice.len() + 63) / 64);

        GrowingBitmap {
            data,
            len: slice.len(),
        }
    }

    /// Clears the current bitmap, then fills it with data from `slice`.
    pub fn clone_from_slice(&mut self, slice: &impl BitmapSlice) {
        self.len = slice.len();
        self.data.clear();
        self.data.extend(slice.iter_data());

        debug_assert_eq!(self.data.len(), (slice.len() + 63) / 64);
    }

    /// Creates a new bitmap with `num` ones.
    pub fn new_all_ones(num: usize) -> Self {
        let mut r = GrowingBitmap {
            data: vec![u64::MAX; (num + 63) / 64],
            len: num,
        };
        r.zeroize_past_end();
        r
    }

    /// Creates a new bitmap with `num` zeros.
    pub fn new_all_zeros(num: usize) -> Self {
        GrowingBitmap {
            data: vec![0; num / 64 + 1],
            len: num,
        }
    }

    #[inline]
    fn index(x: usize) -> (usize, usize) {
        (x / 64, x % 64)
    }

    /// Returns the value of the `n`th bit.
    #[inline]
    pub fn get(&self, n: usize) -> bool {
        let (index, offset) = Self::index(n);
        (*self.data.get(index).unwrap_or(&0) >> offset) & 1 != 0
    }

    /// Returns the value of the `n`th bit, then resets it to `0`.
    #[inline]
    pub fn get_then_reset(&mut self, n: usize) -> bool {
        let (index, offset) = Self::index(n);
        if let Some(x) = self.data.get_mut(index) {
            let mask = 1 << offset;
            let result = *x & mask != 0;
            *x &= !mask;
            result
        } else {
            false
        }
    }

    /// ANDs the bitmap with `rhs`.
    pub fn and_with(&mut self, rhs: &impl BitmapSlice) -> bool {
        let mut changed = false;
        for (a, b) in self.data.iter_mut().zip(rhs.iter_data().chain(repeat(0))) {
            let new = *a & b;
            changed |= *a != new;
            *a = new;
        }

        changed
    }

    /// ORs the bitmap with `rhs`.
    pub fn or_with(&mut self, rhs: &impl BitmapSlice) -> bool {
        let mut changed = false;
        for (a, b) in self.data.iter_mut().zip(rhs.iter_data().chain(repeat(0))) {
            let new = *a | b;
            changed |= *a != new;
            *a = new;
        }

        changed
    }

    /// Sets `self[n]` to true.
    /// Returns true if `self[n]` changed; False if `self[n]` was already true.
    #[inline]
    pub fn set(&mut self, n: usize) -> bool {
        let (index, offset) = Self::index(n);
        if n >= self.len {
            self.internal_resize(n, index);
        }

        let mask = 1 << offset;
        let changed = self.data[index] & mask == 0;
        self.data[index] |= mask;

        changed
    }

    fn internal_resize(&mut self, n: usize, index: usize) {
        self.len = n + 1;
        if self.data.len() <= index {
            self.data.resize(index + 1, 0);
        }
    }

    /// Sets `self[n]` to false.
    /// Returns true if `self[n]` changed; False if `self[n]` was already false.
    #[inline]
    pub fn reset(&mut self, n: usize) -> bool {
        let (index, offset) = Self::index(n);
        if n >= self.len {
            self.internal_resize(n, index);
        }

        let mask = 1 << offset;
        let changed = self.data[index] & mask != 0;
        self.data[index] &= !mask;

        changed
    }

    /// Extends the bitmap with `items`.
    /// New values are inserted at the end of the bitmap.
    pub fn extend(&mut self, items: impl IntoIterator<Item = bool>) {
        let (mut next_index, mut next_offset) = Self::index(self.len);
        if next_index >= self.data.len() {
            self.data.resize(next_index + 1, 0);
        }

        for item in items.into_iter() {
            self.data[next_index] |= u64::from(item) << next_offset;

            self.len += 1;
            next_offset += 1;
            if next_offset == 64 {
                next_index += 1;
                next_offset = 0;

                if next_index >= self.data.len() {
                    self.data.resize(next_index + 1, 0);
                }
            }
        }
    }

    fn zeroize_past_end(&mut self) {
        if self.len % 64 != 0 && !self.data.is_empty() {
            let last_index = self.data.len() - 1;
            self.data[last_index] &= (1 << (self.len % 64)) - 1;
        }
    }

    /// Fills the bitmap with ones.
    pub fn fill_with_ones(&mut self) {
        self.data.fill(u64::MAX);
        self.zeroize_past_end();
    }

    /// Returns the number of ones in the bitmap.
    #[inline]
    pub fn count_ones(&self) -> usize {
        self.data.iter().map(|v| v.count_ones() as usize).sum()
    }

    /// Returns the number of zeros in the bitmap.
    #[inline]
    pub fn count_zeros(&self) -> usize {
        self.data.iter().map(|v| v.count_zeros() as usize).sum::<usize>() - (64 - self.len % 64)
    }

    /// Returns true if the bitmap only contains zeros.
    #[inline]
    pub fn is_all_zeros(&self) -> bool {
        self.data.iter().all(|&n| n == 0)
    }

    /// Returns true if the bitmap only contains ones.
    pub fn is_all_ones(&self) -> bool {
        let (full_u64s, ok) = if self.len % 64 == 0 {
            (&self.data[..self.len / 64], true)
        } else if !self.data.is_empty() {
            let v = self.data[self.data.len() - 1];
            let last_ok = v == (1 << (self.len % 64)) - 1;
            (&self.data[..self.data.len() - 1], last_ok)
        } else {
            (&[][..], true)
        };

        ok && full_u64s.iter().all(|&n| n == u64::MAX)
    }

    /// Removes bit `n` and shifts all bits above `n` down by one bit.
    pub fn remove(&mut self, n: usize) -> bool {
        let b = self.get(n);

        for i in n..self.len {
            if self.get(i + 1) {
                self.set(i);
            } else {
                self.reset(i);
            }
        }

        self.len -= 1;

        b
    }

    /// Removes the first `num` bits, and shifts the other bits `down` by `num` bits.
    pub fn remove_front(&mut self, num: usize) {
        let num = num.min(self.len);

        let u64s = num / 64;
        self.data.drain(..u64s);

        let shift = num % 64;
        if shift != 0 {
            for n in 0..self.data.len() {
                self.data[n] = (self.data[n] >> shift) | (self.data.get(n + 1).copied().unwrap_or(0) << (64 - shift))
            }
        }

        self.len -= num;

        let data_len_needed = (self.len + 63) / 64;
        if self.data.len() > data_len_needed {
            self.data.drain(data_len_needed..);
        }

        self.zeroize_past_end()
    }

    /// Removes the last `num` bits from the bitmap.
    pub fn remove_back(&mut self, num: usize) {
        assert!(num >= self.len);
        self.len -= num;

        self.data.resize((self.len + 63) / 64, 0);
        self.zeroize_past_end();
    }

    /// Returns the index of the first one bit in the bitmap.
    pub fn first_bit_set(&self) -> Option<usize> {
        self.data
            .iter()
            .enumerate()
            .find(|&(_, &v)| v != 0)
            .map(|(index, val)| index * 64 + val.trailing_zeros() as usize)
    }

    /// Returns the lowest index >= start_index for which self\[index\] = true
    #[inline]
    pub fn first_bit_set_from(&self, start_index: usize) -> Option<usize> {
        let base_index = (start_index / 64) * 64;
        self.data
            .iter()
            .skip(start_index / 64)
            .enumerate()
            .map(|(index, &v)| {
                if index == 0 {
                    (index, v & !((1 << (start_index % 64)) - 1))
                } else {
                    (index, v)
                }
            })
            .find(|&(_, v)| v != 0)
            .map(|(index, val)| base_index + index * 64 + val.trailing_zeros() as usize)
    }

    /// Returns the lowest index >= start_index for which self\[index\] = false
    #[inline]
    pub fn first_bit_unset_from(&self, start_index: usize) -> Option<usize> {
        let base_index = (start_index / 64) * 64;
        self.data
            .iter()
            .skip(start_index / 64)
            .enumerate()
            .map(|(index, &v)| (index, !v))
            .map(|(index, v)| {
                if index == 0 {
                    (index, v & !((1 << (start_index % 64)) - 1))
                } else {
                    (index, v)
                }
            })
            .find(|&(_, v)| v != 0)
            .map(|(index, val)| base_index + index * 64 + val.trailing_zeros() as usize)
            .and_then(|n| if n >= self.len { None } else { Some(n) })
    }

    /// Returns the index of the first bit set in all bitmaps in `items`.
    pub fn first_bit_set_after_many(items: &[&GrowingBitmap], start_index: usize, end_index: usize) -> Option<usize> {
        let start = start_index / 64;
        let end = (end_index + 63) / 64;
        (start..end)
            .map(|index| {
                let v = items.iter().map(|map| map.data[index]).reduce(|a, b| a & b).unwrap();
                if index == start {
                    (index, v & !((1 << (start_index % 64)) - 1))
                } else {
                    (index, v)
                }
            })
            .find(|&(_, v)| v != 0)
            .map(|(index, val)| index * 64 + val.trailing_zeros() as usize)
    }

    /// Returns true if for all bits: other\[n\] implies self\[n\].
    pub fn is_superset_of(&self, other: &GrowingBitmap) -> bool {
        if other.len() > self.len() && other.first_bit_set_from(self.len).is_some() {
            false
        } else {
            self.data.iter().zip(other.data.iter()).all(|(&a, &b)| a | b == a)
        }
    }

    /// Returns true if there are any bits set both in this bitmap and in `other`.
    #[inline]
    pub fn overlaps_with(&self, other: &impl BitmapSlice) -> bool {
        self.data.iter().zip(other.iter_data()).any(|(&a, b)| a & b != 0)
    }

    /// Clears the bits in self if they are set in other
    pub fn clear_from(&mut self, other: &impl BitmapSlice) {
        for (a, b) in self.data.iter_mut().zip(other.iter_data()) {
            *a &= !b;
        }
    }

    /// Returns the length of the bitmap.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the bitmap is empty.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterates over all bits in the bitmap.
    #[inline]
    pub fn iter(&self) -> GrowingBitmapIterator {
        GrowingBitmapIterator {
            data: &self.data,
            len: self.len,
            index: 0,
        }
    }

    /// Iterates over all indices of the bits that are one.
    #[inline]
    pub fn iter_one_indices(&self) -> impl Iterator<Item = usize> + '_ {
        if self.data.is_empty() {
            GrowingBitmapOnesIterator {
                data: &[],
                base_index: 0,
                current_element: 0,
            }
        } else {
            GrowingBitmapOnesIterator {
                data: &self.data[1..],
                base_index: 0,
                current_element: self.data[0],
            }
        }
    }

    /// Returns the backing data of the bitmap.
    #[inline]
    pub fn data(&self) -> &[u64] {
        self.data.as_ref()
    }

    /// Resizes the bitmap to contain exactly `len` bits.
    /// If the bitmap grows, zero bits are inserted at the end.
    pub fn resize(&mut self, len: usize) {
        self.len = len;

        let required_len = (len + 63) / 64;
        if required_len != self.data.len() {
            self.data.resize(required_len, 0);
        }

        self.zeroize_past_end();
    }

    /// Sets all bits in `range` to one.
    pub fn set_range(&mut self, range: Range<usize>) {
        for n in range {
            self.set(n);
        }
    }

    /// Sets all bits in `range` to zero.
    pub fn clear_range(&mut self, index: Range<usize>) {
        for n in index {
            self.reset(n);
        }
    }

    /// Appends `bitmap` to the bitmap.
    pub fn append(&mut self, bitmap: &GrowingBitmap) {
        self.extend(bitmap.iter())
    }

    /// Returns a slice that references the bits in `range`.
    pub fn slice(&self, range: Range<usize>) -> impl BitmapSlice + '_ {
        if range.start == range.end {
            BitmapSliceU64 {
                data: &[],
                offset: 0,
                crop: 0,
            }
        } else {
            let (start_index, start_offset) = Self::index(range.start);
            let (end_index, end_offset) = Self::index(range.end);
            let (end_index, crop) = if end_offset != 0 {
                (end_index + 1, 64 - end_offset)
            } else {
                (end_index, 0)
            };

            BitmapSliceU64 {
                data: &self.data[start_index..end_index],
                offset: start_offset as u8,
                crop: crop as u8,
            }
        }
    }

    /// Returns a mutable slice that references the bits in `range`.
    pub fn slice_mut(&mut self, range: Range<usize>) -> impl BitmapSliceMut + '_ {
        if range.start == range.end {
            BitmapSliceMutU64 {
                data: &mut [],
                offset: 0,
                crop: 0,
            }
        } else {
            let (start_index, start_offset) = Self::index(range.start);
            let (end_index, end_offset) = Self::index(range.end);
            let (end_index, crop) = if end_offset != 0 {
                (end_index + 1, 64 - end_offset)
            } else {
                (end_index, 0)
            };

            BitmapSliceMutU64 {
                data: &mut self.data[start_index..end_index],
                offset: start_offset as u8,
                crop: crop as u8,
            }
        }
    }

    /// Sets all bits in the bitmap to zero.
    pub fn set_all_zero(&mut self) {
        for x in self.data.iter_mut() {
            *x = 0;
        }
    }
}

impl BitmapSlice for GrowingBitmap {
    fn get(&self, index: usize) -> bool {
        GrowingBitmap::get(self, index)
    }

    fn len(&self) -> usize {
        GrowingBitmap::len(self)
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.data.iter().copied()
    }
}

impl BitmapSlice for &'_ mut GrowingBitmap {
    fn get(&self, index: usize) -> bool {
        GrowingBitmap::get(self, index)
    }

    fn len(&self) -> usize {
        GrowingBitmap::len(self)
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.data.iter().copied()
    }
}

impl BitmapSlice for &'_ GrowingBitmap {
    fn get(&self, index: usize) -> bool {
        GrowingBitmap::get(self, index)
    }

    fn len(&self) -> usize {
        GrowingBitmap::len(self)
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        self.data.iter().copied()
    }
}

impl BitmapSliceMut for GrowingBitmap {
    fn modify(&mut self, mut f: impl FnMut(u64) -> u64) {
        for item in self.data.iter_mut() {
            *item = f(*item);
        }

        self.zeroize_past_end()
    }
}

impl BitmapSliceMut for &'_ mut GrowingBitmap {
    fn modify(&mut self, mut f: impl FnMut(u64) -> u64) {
        for item in self.data.iter_mut() {
            *item = f(*item);
        }

        self.zeroize_past_end()
    }
}

#[derive(Copy, Clone)]
pub struct BitmapSliceU64<'a> {
    data: &'a [u64],
    offset: u8,
    crop: u8,
}

fn create_iter(data: &[u64], offset: u8, crop: u8) -> impl Iterator<Item = u64> + '_ {
    let shift = 64 - offset;
    data.iter()
        .enumerate()
        .take(if data.len() > 1 && crop + offset >= 64 {
            data.len() - 1
        } else {
            data.len()
        })
        .map(move |(index, &first)| {
            if index + 1 == data.len() {
                let crop_mask = u64::MAX >> crop;
                (first & crop_mask) >> offset
            } else if offset == 0 {
                first
            } else {
                let next = data.get(index + 1).unwrap_or(&0);
                let next_crop_mask = if index + 2 == data.len() { u64::MAX >> crop } else { u64::MAX };

                (first >> offset) | ((next & next_crop_mask).checked_shl(shift as u32).unwrap_or(0))
            }
        })
}

impl BitmapSlice for BitmapSliceU64<'_> {
    fn get(&self, n: usize) -> bool {
        let (index, offset) = GrowingBitmap::index(n + self.offset as usize);
        (self.data.get(index).unwrap_or(&0) >> offset) & 1 != 0
    }

    fn len(&self) -> usize {
        self.data.len() * 64 - self.offset as usize - self.crop as usize
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        create_iter(self.data, self.offset, self.crop)
    }
}

pub struct BitmapSliceMutU64<'a> {
    data: &'a mut [u64],
    offset: u8,
    crop: u8,
}

impl BitmapSlice for BitmapSliceMutU64<'_> {
    fn get(&self, n: usize) -> bool {
        let (index, offset) = GrowingBitmap::index(n + self.offset as usize);
        (self.data.get(index).unwrap_or(&0) >> offset) & 1 != 0
    }

    fn len(&self) -> usize {
        self.data.len() * 64 - self.offset as usize - self.crop as usize
    }

    fn iter_data(&self) -> impl Iterator<Item = u64> + '_ {
        create_iter(self.data, self.offset, self.crop)
    }
}

impl BitmapSliceMut for BitmapSliceMutU64<'_> {
    fn modify(&mut self, mut f: impl FnMut(u64) -> u64) {
        if self.data.is_empty() {
            return
        }

        if self.offset == 0 {
            let last_index = self.data.len() - 1;
            for (index, item) in self.data.iter_mut().enumerate() {
                if index == last_index {
                    let old = *item;
                    let val = f(old);
                    let mask = u64::MAX >> self.crop;

                    *item = (old & !mask) | (val & mask);
                } else {
                    *item = f(*item);
                }
            }
        } else {
            let shift = 64 - self.offset;

            let mut buffer_in = self.data[0] >> self.offset;
            let mut buffer_out = self.data[0] & !(u64::MAX << self.offset);

            for index in 1..self.data.len() {
                let item = self.data[index];
                let old_val = buffer_in | (item << shift);
                buffer_in = item >> self.offset;

                let new_val = f(old_val);
                let write = buffer_out | (new_val << self.offset);
                self.data[index - 1] = write;
                buffer_out = new_val >> shift;
            }

            let len = self.data.len();
            let last = &mut self.data[len - 1];
            let crop_mask = u64::MAX >> self.crop;
            let item = *last & crop_mask;
            let old_val = buffer_in | (item << shift);

            let new_val = if len <= 1 || self.crop + self.offset < 64 {
                f(old_val)
            } else {
                0
            };
            let write = buffer_out | (new_val << self.offset);

            *last = (*last & !crop_mask) | (write & crop_mask);
        }
    }
}

impl Clone for GrowingBitmap {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            len: self.len,
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.len = source.len;
        self.data.clone_from(&source.data);
    }
}

pub struct GrowingBitmapIterator<'a> {
    data: &'a [u64],
    index: usize,
    len: usize,
}

impl Iterator for GrowingBitmapIterator<'_> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(new_len) = self.len.checked_sub(1) {
            let index = self.index;
            let b = self.data[0] & (1 << index) != 0;

            let new_index = self.index + 1;
            if new_index >= 64 {
                self.index = 0;
                self.data = &self.data[1..];
            } else {
                self.index = new_index;
            }

            self.len = new_len;

            Some(b)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }
}

impl ExactSizeIterator for GrowingBitmapIterator<'_> {
    fn len(&self) -> usize {
        self.len
    }
}

pub struct GrowingBitmapOnesIterator<'a> {
    data: &'a [u64],
    base_index: usize,
    current_element: u64,
}

impl Iterator for GrowingBitmapOnesIterator<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_element == 0 {
                self.base_index += 64;
                if let Some(&next) = self.data.first() {
                    self.data = &self.data[1..];
                    self.current_element = next;
                } else {
                    return None
                }
            } else {
                let offset = self.current_element.trailing_zeros();
                self.current_element &= (u64::MAX << offset) << 1;

                return Some(self.base_index + offset as usize)
            }
        }
    }
}

impl Debug for GrowingBitmap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for item in self.iter() {
            if item {
                f.write_char('1')?;
            } else {
                f.write_char('0')?;
            }
        }

        Ok(())
    }
}

impl BitAnd for GrowingBitmap {
    type Output = GrowingBitmap;

    fn bitand(self, rhs: Self) -> Self::Output {
        GrowingBitmap {
            data: self.data.into_iter().zip(rhs.data).map(|(a, b)| a & b).collect(),
            len: self.len.min(rhs.len),
        }
    }
}

impl BitAnd for &GrowingBitmap {
    type Output = GrowingBitmap;

    fn bitand(self, rhs: Self) -> Self::Output {
        GrowingBitmap {
            data: self.data.iter().zip(rhs.data.iter()).map(|(a, b)| a & b).collect(),
            len: self.len.min(rhs.len),
        }
    }
}

impl BitAndAssign for GrowingBitmap {
    fn bitand_assign(&mut self, rhs: Self) {
        for (a, b) in self.data.iter_mut().zip(rhs.data.iter().chain(repeat(&0))) {
            *a &= b;
        }
    }
}

impl<'a> BitAndAssign<&'a GrowingBitmap> for GrowingBitmap {
    fn bitand_assign(&mut self, rhs: &'a GrowingBitmap) {
        for (a, b) in self.data.iter_mut().zip(rhs.data.iter().chain(repeat(&0))) {
            *a &= b;
        }
    }
}

impl BitOr for GrowingBitmap {
    type Output = GrowingBitmap;

    fn bitor(self, rhs: Self) -> Self::Output {
        let n = self.data.len().max(rhs.data.len());
        GrowingBitmap {
            data: (0..n)
                .map(|index| self.data.get(index).unwrap_or(&0) | rhs.data.get(index).unwrap_or(&0))
                .collect(),
            len: self.len.max(rhs.len),
        }
    }
}

impl BitOr for &GrowingBitmap {
    type Output = GrowingBitmap;

    fn bitor(self, rhs: Self) -> Self::Output {
        let n = self.data.len().max(rhs.data.len());
        GrowingBitmap {
            data: (0..n)
                .map(|index| self.data.get(index).unwrap_or(&0) | rhs.data.get(index).unwrap_or(&0))
                .collect(),
            len: self.len.max(rhs.len),
        }
    }
}

impl BitOrAssign for GrowingBitmap {
    fn bitor_assign(&mut self, rhs: Self) {
        if self.len() < rhs.len() {
            self.resize(rhs.len());
        }

        for (a, b) in self.data.iter_mut().zip(rhs.data.iter().chain(repeat(&0))) {
            *a |= b;
        }
    }
}

impl<'a> BitOrAssign<&'a GrowingBitmap> for GrowingBitmap {
    fn bitor_assign(&mut self, rhs: &'a GrowingBitmap) {
        if self.len() < rhs.len() {
            self.resize(rhs.len());
        }

        for (a, b) in self.data.iter_mut().zip(rhs.data.iter().chain(repeat(&0))) {
            *a |= b;
        }
    }
}

impl Index<usize> for GrowingBitmap {
    type Output = bool;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        if self.get(index) {
            &true
        } else {
            &false
        }
    }
}

impl<'a> Index<&'a usize> for GrowingBitmap {
    type Output = bool;

    #[inline]
    fn index(&self, index: &'a usize) -> &Self::Output {
        &self[*index]
    }
}

impl FromIterator<bool> for GrowingBitmap {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut b = GrowingBitmap::new();
        b.extend(iter);
        b
    }
}

impl PartialEq for GrowingBitmap {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.data == other.data
    }
}

impl Hash for GrowingBitmap {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.len.hash(state);

        for item in self.data.iter() {
            item.hash(state);
        }
    }
}

/// A set which has most values near 0.
#[derive(Clone, Default)]
pub struct DenseSet {
    bitmap: GrowingBitmap,
    num_items: usize,
}

impl DenseSet {
    /// Create a new dense set.
    #[inline]
    pub const fn new() -> Self {
        DenseSet {
            bitmap: GrowingBitmap::new(),
            num_items: 0,
        }
    }

    /// Returns true if the set contains `x`.
    #[inline]
    pub fn contains(&self, x: usize) -> bool {
        self.bitmap.get(x)
    }

    /// Inserts `index` into the set.
    #[inline]
    pub fn set(&mut self, index: usize) -> bool {
        if self.bitmap.set(index) {
            self.num_items += 1;
            true
        } else {
            false
        }
    }

    /// Iterates over all items in the set.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.bitmap.iter_one_indices()
    }

    /// Returns the number of items in the set.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.num_items
    }

    /// Returns true if the set is empty.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Debug for DenseSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut set = f.debug_set();
        for item in self.iter() {
            set.entry(&item);
        }

        set.finish()
    }
}

#[cfg(test)]
mod tests {
    use std::iter::{once, repeat};

    use itertools::Itertools;

    use crate::utils::bitmap::{BitmapSlice, BitmapSliceMut, GrowingBitmap};

    #[test]
    pub fn or() {
        let a = [true, false, false, false, false, true]
            .into_iter()
            .collect::<GrowingBitmap>();
        let b = [true, true, false].into_iter().collect::<GrowingBitmap>();

        assert_eq!(
            a | b,
            [true, true, false, false, false, true].into_iter().collect::<GrowingBitmap>()
        );
    }

    #[test]
    pub fn iter_one_indices() {
        let a = [true, false, false, false, false, true]
            .into_iter()
            .collect::<GrowingBitmap>();
        let b = [true, true, false].into_iter().collect::<GrowingBitmap>();
        let c = [true, true, false, true].into_iter().collect::<GrowingBitmap>();
        let mut d = GrowingBitmap::new_all_zeros(512);
        d.set(500);
        d.set(48);
        d.set(321);

        let mut e = GrowingBitmap::new_all_zeros(65);
        e.set(63);
        e.set(64);

        assert_eq!(a.iter_one_indices().collect::<Vec<_>>(), vec![0, 5]);
        assert_eq!(b.iter_one_indices().collect::<Vec<_>>(), vec![0, 1]);
        assert_eq!(c.iter_one_indices().collect::<Vec<_>>(), vec![0, 1, 3]);
        assert_eq!(d.iter_one_indices().collect::<Vec<_>>(), vec![48, 321, 500]);
        assert_eq!(e.iter_one_indices().collect::<Vec<_>>(), vec![63, 64]);
    }

    #[test]
    pub fn is_all_zeros_ones() {
        let b = (0..10).map(|_| true).collect::<GrowingBitmap>();
        assert!(b.is_all_ones());
        assert!(!b.is_all_zeros());

        let b = (0..64).map(|_| true).collect::<GrowingBitmap>();
        assert!(b.is_all_ones());
        assert!(!b.is_all_zeros());

        let b = (0..10).map(|_| false).collect::<GrowingBitmap>();
        assert!(!b.is_all_ones());
        assert!(b.is_all_zeros());

        let b = (0..64).map(|_| false).collect::<GrowingBitmap>();
        assert!(!b.is_all_ones());
        assert!(b.is_all_zeros());

        let b = (0..80).map(|n| n < 64).collect::<GrowingBitmap>();
        assert!(!b.is_all_ones());
        assert!(!b.is_all_zeros());
    }

    #[test]
    pub fn remove() {
        let mut b = (0..10).map(|k| k < 5).collect::<GrowingBitmap>();
        b.remove(3);
        assert_eq!(b, (0..9).map(|k| k < 4).collect());

        let mut b = (0..10).map(|k| k < 5).collect::<GrowingBitmap>();
        b.remove(7);
        assert_eq!(b, (0..9).map(|k| k < 5).collect());
        assert!(b != (0..10).map(|k| k < 5).collect());
    }

    #[test]
    pub fn first_bit_set_after() {
        let b = [false, false, true, false, false, true, false]
            .into_iter()
            .collect::<GrowingBitmap>();
        assert_eq!(b.first_bit_set_from(2), Some(2));
        assert_eq!(b.first_bit_set_from(3), Some(5));
        assert_eq!(b.first_bit_set_from(5), Some(5));
        assert_eq!(b.first_bit_set_from(6), None);
    }

    #[test]
    pub fn first_bit_unset_from() {
        let b = [true, true, false, true, true, false, true]
            .into_iter()
            .collect::<GrowingBitmap>();
        assert_eq!(b.first_bit_unset_from(2), Some(2));
        assert_eq!(b.first_bit_unset_from(3), Some(5));
        assert_eq!(b.first_bit_unset_from(5), Some(5));
        assert_eq!(b.first_bit_unset_from(6), None);
    }

    #[test]
    pub fn is_superset_of() {
        let b1 = [false, false, true, false].into_iter().collect::<GrowingBitmap>();
        let b2 = [false, false, true, true].into_iter().collect::<GrowingBitmap>();
        let b3 = [false, false, true, true]
            .into_iter()
            .chain(repeat(false).take(500))
            .collect::<GrowingBitmap>();
        let b4 = [false, false, true, true]
            .into_iter()
            .chain(repeat(false).take(350))
            .chain(once(true))
            .collect::<GrowingBitmap>();
        assert!(b2.is_superset_of(&b1));
        assert!(!b1.is_superset_of(&b2));
        assert!(b3.is_superset_of(&b1));
        assert!(b4.is_superset_of(&b1));
        assert!(!b2.is_superset_of(&b4));
        assert!(!b3.is_superset_of(&b4));
    }

    #[test]
    pub fn remove_front() {
        let mut b1 = [false, false, true, false].into_iter().collect::<GrowingBitmap>();

        b1.remove_front(2);
        assert_eq!(b1, [true, false].into_iter().collect::<GrowingBitmap>());

        let mut b2 = (0..300u32).map(|n| n.is_power_of_two()).collect::<GrowingBitmap>();

        println!("{:X?}", b2.data());
        b2.remove_front(50);
        println!("{:X?}", b2.data());

        let expected = (50..300u32).map(|n| n.is_power_of_two()).collect::<GrowingBitmap>();
        println!("{:X?}", expected.data());

        assert_eq!(b2, expected);
    }

    #[test]
    pub fn slice_equivalences() {
        let b1 = {
            let mut b = GrowingBitmap::new();
            for x in [47, 138, 140, 150, 160, 169, 178, 197, 222, 223, 224, 225] {
                b.set(x);
            }
            b
        };

        for start_index in 0..b1.len() {
            for end_index in start_index..=b1.len() {
                println!("Slicing {start_index}..{end_index}");
                let expected = {
                    let mut b = b1.clone();
                    b.resize(end_index);
                    b.remove_front(start_index);
                    b
                };

                let slice = b1.slice(start_index..end_index);

                println!("Data: {:X?}", slice.iter_data().format(", "));

                // Make sure the data is properly cropped at the end
                let len = end_index - start_index;
                if len > 0 && len % 64 != 0 {
                    let last = slice.iter_data().nth(len / 64).unwrap();
                    let num_set = len % 64;
                    assert_eq!(
                        last & (u64::MAX << num_set),
                        0,
                        "Last u64 entry in slice {last:064b} should only have the lower {num_set} bits set"
                    );
                }

                // Make sure the slice matches a similar slice constructed via resize & remove_front.
                let new = GrowingBitmap::from_slice(&slice);
                assert_eq!(
                    new,
                    expected,
                    "range: {start_index}..{end_index}, new data: {:X?}, expected data: {:X?}",
                    new.data(),
                    expected.data()
                );
            }
        }
    }

    #[test]
    pub fn slice_mut_equivalences() {
        let mut b1 = {
            let mut b = GrowingBitmap::new();
            for x in [47, 138, 140, 150, 160, 169, 178, 197, 222, 223, 224, 225] {
                b.set(x);
            }
            b
        };

        for start_index in 0..b1.len() {
            for end_index in start_index..=b1.len() {
                println!("Slicing {start_index}..{end_index}");
                let expected = {
                    let mut b = b1.clone();
                    b.resize(end_index);
                    b.remove_front(start_index);
                    b
                };

                let slice = b1.slice_mut(start_index..end_index);

                println!("Data: {:X?}", slice.iter_data().format(", "));

                // Make sure the data is properly cropped at the end
                let len = end_index - start_index;
                if len > 0 && len % 64 != 0 {
                    let last = slice.iter_data().nth(len / 64).unwrap();
                    let num_set = len % 64;
                    assert_eq!(
                        last & (u64::MAX << num_set),
                        0,
                        "Last u64 entry in slice {last:064b} should only have the lower {num_set} bits set"
                    );
                }

                // Make sure the slice matches a similar slice constructed via resize & remove_front.
                let new = GrowingBitmap::from_slice(&slice);
                assert_eq!(
                    new,
                    expected,
                    "range: {start_index}..{end_index}, new data: {:X?}, expected data: {:X?}",
                    new.data(),
                    expected.data()
                );
            }
        }
    }

    #[test]
    pub fn slice_mut_copy_from() {
        let b1 = {
            let mut b = GrowingBitmap::new();
            for x in [47, 138, 140, 150, 160, 169, 178, 197, 222, 223, 224, 225] {
                b.set(x);
            }
            b
        };

        let b2 = {
            let mut b = GrowingBitmap::new_all_ones(512);
            for x in [37, 130, 137, 149, 171, 173, 179, 201, 203, 207, 222, 225, 227] {
                b.reset(x);
            }
            b
        };

        for start_index in 0..b1.len() {
            for end_index in start_index..=b1.len() {
                println!("Slicing {start_index}..{end_index}");
                let expected = {
                    let mut b = b1.clone();

                    for index in start_index..end_index {
                        if b2.get(index - start_index) {
                            b.set(index);
                        } else {
                            b.reset(index);
                        }
                    }

                    b
                };

                let mut new = b1.clone();
                let mut slice = new.slice_mut(start_index..end_index);
                slice.copy_from(&b2.slice(0..slice.len()));
                drop(slice);

                assert_eq!(
                    new,
                    expected,
                    "range: {start_index}..{end_index}, new data: {:X?}, expected data: {:X?}",
                    new.data(),
                    expected.data()
                );
            }
        }
    }
}
