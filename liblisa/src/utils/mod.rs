//! Contains various utility functions needed by other parts of libLISA.

use std::time::Instant;

pub mod bitmap;
pub(crate) mod cmov;
mod iter;
mod matrix;
mod mcs;
pub(crate) mod min_cover_with_exclusions;
pub(crate) mod minisat;

pub use iter::MapRotated;
pub use matrix::Symmetric2DMatrix;
pub use mcs::MinimumCoveringSet;

#[inline]
const fn be_to_le_num_to_shift(num_bits: usize) -> usize {
    ((64 - num_bits) / 8) * 8
}

/// Reverses the ordering of the lowest `ceil(num_bits / 8)` in `val`.
#[inline]
pub const fn switch_endianness_u64(val: u64, num_bits: usize) -> u64 {
    val.swap_bytes() >> be_to_le_num_to_shift(num_bits)
}

/// Reverses the ordering of the lowest `ceil(num_bits / 8)` in `val`.
#[inline]
pub const fn switch_endianness_u128(val: u128, num_bits: usize) -> u128 {
    val.swap_bytes() >> (((128 - num_bits) / 8) * 8)
}

/// Extends an `n`-bit number in `v` to an `i128`.
#[inline]
pub const fn sign_extend(v: i128, n: usize) -> i128 {
    let k = 128 - n;
    (v << k) >> k
}

/// Extends an `n`-bit number in `v` to an `i64`.
#[inline]
pub const fn sign_extend_u64(v: u64, n: usize) -> i64 {
    let k = 64 - n;
    ((v << k) as i64) >> k
}

/// Returns a bitmask where the lowest `n` bits are set.
#[inline]
pub const fn bitmask_u64(n: u32) -> u64 {
    match u64::MAX.checked_shr(64 - n) {
        Some(val) => val,
        None => 0,
    }
}

/// Returns a bitmask where the lowest `n` bits are set.
#[inline]
pub const fn bitmask_u128(n: u32) -> u128 {
    match u128::MAX.checked_shr(128 - n) {
        Some(val) => val,
        None => 0,
    }
}

/// Performs the x86 PDEP operation.
#[inline]
pub const fn deposit_bits_u128(mut source: u128, mut selector: u128) -> u128 {
    let mut dest = 0u128;

    let mut dest_bit = 0;
    while selector != 0 {
        let bit_index = selector.trailing_zeros();
        let bit = source & 1;
        dest |= bit << (dest_bit + bit_index);
        dest_bit += bit_index + 1;

        source >>= 1;
        selector >>= bit_index + 1;
    }

    dest
}

#[doc(hidden)] // Only public for benchmark
#[inline]
pub fn create_from_le_bytes<T>(bytes: &[u8], process_u64: impl FnOnce(u64) -> T, process_u128: impl FnOnce(u128) -> T) -> T {
    #[inline(always)]
    fn x64(bytes: &[u8]) -> u64 {
        u64::from_le_bytes(bytes.try_into().unwrap())
    }

    #[inline(always)]
    fn x32(bytes: &[u8]) -> u32 {
        u32::from_le_bytes(bytes.try_into().unwrap())
    }

    #[inline(always)]
    fn x16(bytes: &[u8]) -> u16 {
        u16::from_le_bytes(bytes.try_into().unwrap())
    }

    match bytes.len() {
        1 => process_u64(bytes[0] as u64),
        2 => process_u64(x16(&bytes[0..2]) as u64),
        3 => process_u64((x16(&bytes[0..2]) as u32 | ((bytes[2] as u32) << 16)) as u64),
        4 => process_u64(x32(&bytes[0..4]) as u64),
        5 => process_u64(x32(&bytes[0..4]) as u64 | ((bytes[4] as u64) << 32)),
        6 => process_u64(x32(&bytes[0..4]) as u64 | ((x16(&bytes[4..6]) as u64) << 32)),
        7 => process_u64(x32(&bytes[0..4]) as u64 | ((x16(&bytes[4..6]) as u64) << 32) | ((bytes[6] as u64) << 48)),
        8 => process_u64(x64(&bytes[0..8])),
        9 => process_u128((x64(&bytes[0..8]) as u128) | ((bytes[8] as u128) << 64)),
        10 => process_u128((x64(&bytes[0..8]) as u128) | ((x16(&bytes[8..10]) as u128) << 64)),
        11 => process_u128((x64(&bytes[0..8]) as u128) | ((x16(&bytes[8..10]) as u128) << 64) | ((bytes[10] as u128) << 80)),
        12 => process_u128((x64(&bytes[0..8]) as u128) | ((x32(&bytes[8..12]) as u128) << 64)),
        13 => process_u128((x64(&bytes[0..8]) as u128) | ((x32(&bytes[8..12]) as u128) << 64) | ((bytes[12] as u128) << 96)),
        14 => process_u128(
            (x64(&bytes[0..8]) as u128) | ((x32(&bytes[8..12]) as u128) << 64) | ((x16(&bytes[12..14]) as u128) << 96),
        ),
        15 => process_u128(
            (x64(&bytes[0..8]) as u128)
                | ((x32(&bytes[8..12]) as u128) << 64)
                | ((x16(&bytes[12..14]) as u128) << 96)
                | ((bytes[14] as u128) << 112),
        ),
        _ => process_u128((x64(&bytes[0..8]) as u128) | ((x64(&bytes[8..16]) as u128) << 64)),
    }
}

/// An iterator that can be one of two types.
pub enum EitherIter<A: Iterator, B: Iterator> {
    /// Iterator type A.
    Left(A),

    /// Iterator type B.
    Right(B),
}

impl<A: Iterator, B: Iterator> Iterator for EitherIter<A, B>
where
    A: Iterator<Item = B::Item>,
{
    type Item = A::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            EitherIter::Left(iter) => iter.next(),
            EitherIter::Right(iter) => iter.next(),
        }
    }
}

/// A timeout-checker.
#[derive(Copy, Clone, Debug, Default)]
pub struct Timeout(Option<Instant>);

impl Timeout {
    /// Sets the timeout to occur at `timeout_at`.
    pub fn set_timeout_at(&mut self, timeout_at: Instant) {
        self.0 = Some(timeout_at);
    }

    /// Returns true if the timeout has elapsed.
    pub fn is_timed_out(&self) -> bool {
        self.0.map(|timeout| Instant::now() >= timeout).unwrap_or(false)
    }

    /// Returns the current timeout.
    pub fn get(&self) -> Option<Instant> {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::{be_to_le_num_to_shift, create_from_le_bytes, sign_extend};

    #[test]
    pub fn test_sign_extend() {
        assert_eq!(sign_extend(0x1234321, 32), 0x1234321);
        assert_eq!(sign_extend(2, 2), -2);
        assert_eq!(sign_extend(0x7f, 7), -1);
    }

    #[test]
    pub fn test_sign_extend_u64() {
        assert_eq!(sign_extend(0x1234321, 32), 0x1234321);
        assert_eq!(sign_extend(2, 2), -2);
        assert_eq!(sign_extend(0x7f, 7), -1);
    }

    #[test]
    pub fn be_to_le_shift_correct() {
        fn reference(num_bits: usize) -> usize {
            ((64 - num_bits) / 8) * 8
        }

        for n in 1..64 {
            let reference_result = reference(n);
            let result = be_to_le_num_to_shift(n);
            println!("{n} (0x{n:X}) -> {reference_result} (0x{reference_result:X}) <=> {result} (0x{result:X})");
            assert_eq!(reference_result, result, "failing for n={n}");
        }
    }

    #[test]
    pub fn create_from_bytes_correct() {
        assert_eq!(create_from_le_bytes(&[1, 0, 0, 0, 0, 0, 0, 0], |n| n as u128, |n| n), 1);
        assert_eq!(
            create_from_le_bytes(&[0, 0, 0, 0, 0, 0, 0, 0x80], |n| n as u128, |n| n),
            0x8000_0000_0000_0000
        );
    }
}
