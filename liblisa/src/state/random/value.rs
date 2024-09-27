use std::iter::{once, repeat_with};

use arrayvec::ArrayVec;
use rand::Rng;

use super::StateGen;
use crate::arch::{Arch, CpuState, Register};
use crate::encoding::dataflows::{AccessKind, AddressComputation, Dest, Inputs, MemoryAccess, MemoryAccesses, Size, Source};
use crate::instr::Instruction;
use crate::oracle::MappableArea;
use crate::state::{Addr, MemoryState, Permissions, SystemState};
use crate::value::MutValue;
struct TinyBuffer(u64);

impl TinyBuffer {
    fn get<const NUM: usize>(&mut self) -> u64 {
        let result = self.0 & ((1 << NUM) - 1);
        self.0 >>= NUM;
        result
    }

    fn get_u32(&mut self) -> u32 {
        let result = self.0 as u32;
        self.0 >>= 32;
        result
    }

    fn get_u16(&mut self) -> u16 {
        let result = self.0 as u16;
        self.0 >>= 16;
        result
    }

    fn get_u8(&mut self) -> u8 {
        let result = self.0 as u8;
        self.0 >>= 8;
        result
    }

    fn rest(self) -> u64 {
        self.0
    }
}

/// Returns a randomized `u64` value.
pub fn randomized_value<R: Rng>(rng: &mut R) -> u64 {
    const TOPMOST_BIT: u64 = 0x8000_0000_0000_0000;
    let v = rng.gen::<u64>();
    // Accept a bit of bias to avoid the overhead of gen_range(..)
    let k = rng.gen::<u16>() as u32 % (65 * 64);

    // The topmost bit in v is never used, so we can re-use it later on to avoid a call to rng.gen().
    let leftover_rng_bit = (v & TOPMOST_BIT) != 0;
    // The next bit is likely shifted out as well,
    let mostly_leftover_rng_bit = (v & (TOPMOST_BIT >> 1)) != 0;
    let zeros = k % 64;
    let shift = k / 64;

    let v = v << zeros;

    // Always set the top bit, because we decide the number of prefixed zeroes separately
    // This makes the number of prefix zeroes nicely uniform
    let v = v | TOPMOST_BIT;

    let v = v.checked_shr(shift).unwrap_or(0);

    if leftover_rng_bit {
        if shift > 18 && mostly_leftover_rng_bit {
            // up to "48-bit" memory address that can actually be mapped
            // we're cropping to just 46 bits, because:
            // - bit 48 is equal to bits 49..64, so it has to be 0 to make the address mappable (a 1 in bit 48..64 is an address reserved for kernel use)
            // - bit 47 is 0, because the highest mappable address is 0x7fff_ffff_e000, not 0x7fff_ffff_f000. So it would be impossible to generate something mappable ending in .._ffff_ffff if bit 47 was set (and it would be set, because we're negating the number here).
            (!v) & 0x0000_3fff_ffff_ffff
        } else {
            // 64-bit negative number
            !v
        }
    } else {
        // (up to) 64-bit positive number
        v
    }
}

fn randomized_u32<R: Rng>(rng: &mut R) -> u32 {
    let mut r = TinyBuffer(rng.gen());

    const TOPMOST_BIT: u32 = 0x80000000;
    let v = r.get_u32();

    // The topmost bit in v is never used, so we can re-use it later on to avoid a call to rng.gen().
    let leftover_rng_bit = (v & TOPMOST_BIT) != 0;
    let zeros = r.get::<5>();
    let shift = (r.get::<5>() + r.get::<1>()) as u32;

    let v = v << zeros;

    // Always set the top bit, because we decide the number of prefixed zeroes separately
    // This makes the number of prefix zeroes nicely uniform
    let v = v | TOPMOST_BIT;

    let v = v.checked_shr(shift).unwrap_or(0);

    if leftover_rng_bit {
        // 32-bit negative number
        !v
    } else {
        // (up to) 32-bit positive number
        v
    }
}

fn randomized_u22<R: Rng>(rng: &mut R) -> u32 {
    let mut r = TinyBuffer(rng.gen());

    const TOPMOST_BIT: u32 = 0x80000000;
    let v = r.get_u32();
    // Accept a bit of bias to avoid the overhead of gen_range(..)

    // The topmost bit in v is never used, so we can re-use it later on to avoid a call to rng.gen().
    let leftover_rng_bit = (v & TOPMOST_BIT) != 0;
    let zeros = r.get::<5>();
    let shift = ((r.get_u8()) % 23) as u32 + 10;

    let v = v << zeros;

    // Always set the top bit, because we decide the number of prefixed zeroes separately
    // This makes the number of prefix zeroes nicely uniform
    let v = v | TOPMOST_BIT;

    let v = v.checked_shr(shift).unwrap_or(0);

    if leftover_rng_bit {
        // 32-bit negative number
        !v
    } else {
        // (up to) 32-bit positive number
        v
    }
}

fn randomized_u64<R: Rng>(rng: &mut R) -> u64 {
    const TOPMOST_BIT: u64 = 0x8000_0000_0000_0000;
    let v = rng.gen::<u64>();
    // Accept a bit of bias to avoid the overhead of gen_range(..)
    let k = rng.gen::<u16>() as u32 % (65 * 64);

    // The topmost bit in v is never used, so we can re-use it later on to avoid a call to rng.gen().
    let leftover_rng_bit = (v & TOPMOST_BIT) != 0;
    let zeros = k % 64;
    let shift = k / 64;

    let v = v << zeros;

    // Always set the top bit, because we decide the number of prefixed zeroes separately
    // This makes the number of prefix zeroes nicely uniform
    let v = v | TOPMOST_BIT;

    let v = v.checked_shr(shift).unwrap_or(0);

    if leftover_rng_bit {
        // 64-bit negative number
        !v
    } else {
        // (up to) 64-bit positive number
        v
    }
}

fn randomized_u50<R: Rng>(rng: &mut R) -> u64 {
    const TOPMOST_BIT: u64 = 0x8000_0000_0000_0000;
    let v = rng.gen::<u64>();
    // Accept a bit of bias to avoid the overhead of gen_range(..)
    let k = rng.gen::<u16>() as u32 % (51 * 64);

    // The topmost bit in v is never used, so we can re-use it later on to avoid a call to rng.gen().
    let leftover_rng_bit = (v & TOPMOST_BIT) != 0;
    let zeros = k % 64;
    let shift = k / 64 + 14;

    let v = v << zeros;

    // Always set the top bit, because we decide the number of prefixed zeroes separately
    // This makes the number of prefix zeroes nicely uniform
    let v = v | TOPMOST_BIT;

    let v = v.checked_shr(shift).unwrap_or(0);

    if leftover_rng_bit {
        // 64-bit negative number
        !v
    } else {
        // (up to) 64-bit positive number
        v
    }
}

fn randomized_f32<R: Rng>(rng: &mut R) -> f32 {
    let mut r = TinyBuffer(rng.gen());

    match r.get::<5>() {
        // Special values
        // NaN - but changing the least significant byte to a 0 makes it non-NaN
        0 => f32::from_bits(0x7F800001 | (r.get_u32() & 0xFFC0_0000)),
        1 => f32::NEG_INFINITY,
        2 => f32::INFINITY,

        // Useful for float -> int conversions (for example: vcvttpd2dq)
        3 | 4 => i32::MAX as f32,
        5 => 0x4000_0000i32 as f32,
        6 | 7 => i32::MIN as f32,
        8..=11 => (0xC000_0000u32 as i32) as f32,
        // denormal / subnormal number
        12..=15 => f32::from_bits(r.get_u32() & !0x7f80_0000),
        // There is a 1 in 256 chance we generate a NaN here.
        // It's not worth the performance cost trying to filter them out.
        _ => f32::from_bits(r.get_u32()),
    }
}

fn randomized_f64<R: Rng>(rng: &mut R) -> u64 {
    let mut r = TinyBuffer(rng.gen());
    match r.get::<5>() {
        // Special values
        0 => f64::NAN.to_bits(),
        1 => f64::NEG_INFINITY.to_bits(),
        2 => f64::INFINITY.to_bits(),

        // f64 such that changing the highest byte will cause a difference during conversion to u/i32
        3 | 4 => 0x000000010000aec1u64 | (r.rest() & 0x000000ffffffaec1u64),

        // Useful for f64 -> i32 conversions (for example: vcvttpd2dq)
        5 | 18 => (i32::MAX as f64).to_bits(),
        6 => (0x4000_0000i32 as f64).to_bits(),
        7 => (i32::MIN as f64).to_bits(),
        8 => ((0xC000_0000u32 as i32) as f64).to_bits(),
        // denormal / subnormal number
        // Technically we should be checking (v << 12) != 0 to make sure we're not returning zero,
        // but the chance of that occurring is so small we won't bother.
        9 | 10 => r.get::<52>() | (r.rest() << 63),
        // denormal / subnormal number with only one byte set
        // Technically we should be checking (v << 12) != 0 to make sure we're not returning zero,
        // but the chance of that occurring is so small we won't bother.
        11 => {
            let data = r.get_u16();
            let value = data as u8;
            let byte_index = (data >> 8) as u8 & 0x7;
            ((value as u64) << (byte_index * 8)) & !0x7ff0_0000_0000_0000
        },
        // exponent such that to_bits(f) + 1 == f + 1
        12..=14 => 0x4330000000000000 | (r.get::<52>() | (r.rest() << 63)),
        // whole number with exponent such that to_bits(f) + 1 == f + 1/(2**8)
        15..=17 => 0x42c0000000000000 | (r.get::<52>() | (r.rest() << 63)) & !0xff,
        // There's a 1 in 2048 chance that we generate a NaN here.
        // It's not worth the performance cost trying to filter them out.
        _ => rng.gen(),
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ExtendedFloatingPoint(u16, u64);

impl ExtendedFloatingPoint {
    const NAN: ExtendedFloatingPoint = ExtendedFloatingPoint(0x7fff, 0x8000_0000_0000_0001);
    const NEG_INFINITY: ExtendedFloatingPoint = ExtendedFloatingPoint(0xffff, 0x8000_0000_0000_0000);
    const INFINITY: ExtendedFloatingPoint = ExtendedFloatingPoint(0x7fff, 0x8000_0000_0000_0000);

    fn to_le_bytes(self) -> [u8; 10] {
        let mut result = [0u8; 10];
        result[..8].copy_from_slice(&self.1.to_le_bytes());
        result[8..].copy_from_slice(&self.0.to_le_bytes());

        result
    }

    fn to_be_bytes(self) -> [u8; 10] {
        let mut result = [0u8; 10];
        result[..2].copy_from_slice(&self.0.to_be_bytes());
        result[2..].copy_from_slice(&self.1.to_be_bytes());

        result
    }
}

fn randomized_f80<R: Rng>(rng: &mut R) -> ExtendedFloatingPoint {
    let mut r = TinyBuffer(rng.gen());
    match r.get::<4>() {
        // Special values
        0 | 1 => ExtendedFloatingPoint::NAN,
        2 => ExtendedFloatingPoint::NEG_INFINITY,
        3 => ExtendedFloatingPoint::INFINITY,

        // f80 such that changing the highest byte will cause a difference during conversion to u/i64
        4 | 5 => ExtendedFloatingPoint(0x403d, r.rest() | 0xf000_0000_0000_0000),

        // f80 such that changing the highest byte will cause a difference during conversion to u/i32
        6 | 7 => ExtendedFloatingPoint(0x401d, ((r.get_u32() as u64) << 32) | 0xf000_0000_0000_0000),
        // Special value that changes the i32 value when changing the least significant byte
        8 => ExtendedFloatingPoint(0x401d, 0xfcf2_a2b1_0000_0000),

        // f80 such that changing the highest byte will cause a difference during conversion to u/i16
        9 | 10 => ExtendedFloatingPoint(0x400d, (r.rest() << 3) | 0x8000_0000_0000_0000),
        // Special value that changes the i16 value when changing the least significant byte
        11 => ExtendedFloatingPoint(0x400d, 0x90b9000000000000),

        // denormal / subnormal number
        // There's a 1 in "many" chance that we generate a NaN here.
        // It's not worth the performance cost trying to filter them out.
        _ => ExtendedFloatingPoint(rng.gen(), rng.gen()),
    }
}

/// Returns a vector of `len` random bytes.
pub fn randomized_bytes<R: Rng>(rng: &mut R, len: usize) -> Vec<u8> {
    let mut result = vec![0u8; len];
    randomized_bytes_into_buffer(rng, &mut result);
    result
}

/// Returns a randomized byte for position `index` into a byte vector.
/// This avoids the allocation of a vector for the result.
pub fn randomized_bytes_select_nth<R: Rng>(rng: &mut R, index: usize) -> u8 {
    // We repeat the same items in *at most* 8 bytes, so there's no point in skipping more than 7 bytes.
    let index = index % 8;
    let mut buf = [0u8; 8];
    randomized_bytes_into_buffer(rng, &mut buf);

    buf[index]
}

/// Generates randomized bytes and puts them in `buf`.
pub fn randomized_bytes_into_buffer<R: Rng>(rng: &mut R, buf: &mut [u8]) {
    fn gen10<R: Rng>(buf: &mut [u8], swap_bytes: bool, rng: &mut R, mut f: impl FnMut(&mut R) -> ExtendedFloatingPoint) {
        fn swap(swap_bytes: bool, v: ExtendedFloatingPoint) -> [u8; 10] {
            if swap_bytes {
                v.to_le_bytes()
            } else {
                v.to_be_bytes()
            }
        }

        let size = (buf.len() + 9) / 10;
        let mut data = ArrayVec::<_, 16>::new();

        if size <= data.capacity() {
            for _ in 0..size {
                data.push(swap(swap_bytes, f(rng)));
            }

            // Because alignment cannot be guaranteed, the compiler will normally generate calls to memcpy
            // for a naive implementation that copies each generated value to the right byte range.
            // We can reduce this to a single memcpy call by first collecting the results into a buffer,
            // then copying all of them at once when we are done.
            let data_bytes: &[u8] = unsafe {
                let ptr = data.as_ptr();
                std::slice::from_raw_parts(ptr as *const u8, data.len() * 10)
            };

            buf.copy_from_slice(&data_bytes[..buf.len()]);
        } else {
            for i in 0..size - 1 {
                buf[i * 10..(i + 1) * 10].copy_from_slice(&swap(swap_bytes, f(rng)));
            }

            let last = (size - 1) * 10;
            let remaining = buf.len() - last;
            buf[last..].copy_from_slice(&swap(swap_bytes, f(rng))[..remaining]);
        }
    }

    fn gen8<R: Rng>(buf: &mut [u8], swap_bytes: bool, rng: &mut R, mut f: impl FnMut(&mut R) -> u64) {
        fn swap(swap_bytes: bool, v: u64) -> u64 {
            if swap_bytes {
                v.swap_bytes()
            } else {
                v
            }
        }

        if let (&mut [], buf, &mut []) = unsafe { buf.align_to_mut::<u64>() } {
            for b in buf.iter_mut() {
                *b = swap(swap_bytes, f(rng));
            }
        } else {
            let size = (buf.len() + 7) / 8;
            let mut data = ArrayVec::<_, 20>::new();

            if size <= data.capacity() {
                for _ in 0..size {
                    data.push(swap(swap_bytes, f(rng)));
                }

                // Because alignment cannot be guaranteed, the compiler will normally generate calls to memcpy
                // for a naive implementation that copies each generated value to the right byte range.
                // We can reduce this to a single memcpy call by first collecting the results into a buffer,
                // then copying all of them at once when we are done.
                let data_bytes: &[u8] = unsafe {
                    let ptr = data.as_ptr();
                    std::slice::from_raw_parts(ptr as *const u8, data.len() * 8)
                };

                buf.copy_from_slice(&data_bytes[..buf.len()]);
            } else {
                for i in 0..size - 1 {
                    buf[i * 8..(i + 1) * 8].copy_from_slice(&swap(swap_bytes, f(rng)).to_ne_bytes());
                }

                let last = (size - 1) * 8;
                let remaining = buf.len() - last;
                buf[last..].copy_from_slice(&swap(swap_bytes, f(rng)).to_ne_bytes()[..remaining]);
            }
        }
    }

    fn gen4<R: Rng>(buf: &mut [u8], swap_bytes: bool, rng: &mut R, mut f: impl FnMut(&mut R) -> u32) {
        fn swap(swap_bytes: bool, v: u32) -> u32 {
            if swap_bytes {
                v.swap_bytes()
            } else {
                v
            }
        }

        if let (&mut [], buf, &mut []) = unsafe { buf.align_to_mut::<u32>() } {
            for b in buf.iter_mut() {
                *b = swap(swap_bytes, f(rng));
            }
        } else {
            let size = (buf.len() + 3) / 4;
            let mut data = ArrayVec::<_, 40>::new();

            if size <= data.capacity() {
                for _ in 0..size {
                    data.push(swap(swap_bytes, f(rng)));
                }

                // Because alignment cannot be guaranteed, the compiler will normally generate calls to memcpy
                // for a naive implementation that copies each generated value to the right byte range.
                // We can reduce this to a single memcpy call by first collecting the results into a buffer,
                // then copying all of them at once when we are done.
                let data_bytes: &[u8] = unsafe {
                    let ptr = data.as_ptr();
                    std::slice::from_raw_parts(ptr as *const u8, data.len() * 4)
                };

                buf.copy_from_slice(&data_bytes[..buf.len()]);
            } else {
                for i in 0..size - 1 {
                    buf[i * 4..(i + 1) * 4].copy_from_slice(&swap(swap_bytes, f(rng)).to_ne_bytes());
                }

                let last = (size - 1) * 4;
                let remaining = buf.len() - last;
                buf[last..].copy_from_slice(&swap(swap_bytes, f(rng)).to_ne_bytes()[..remaining]);
            }
        }
    }

    let r = rng.gen::<u8>() % 14;
    let swap_bytes = r & 1 != 0;
    match r >> 1 {
        0 => gen4(buf, swap_bytes, rng, |rng| randomized_f32(rng).to_bits()),
        1 => gen8(buf, swap_bytes, rng, |rng| randomized_f64(rng)),
        2 => gen4(buf, swap_bytes, rng, |rng| randomized_u32(rng)),
        3 => gen8(buf, swap_bytes, rng, |rng| randomized_u64(rng)),
        4 => gen4(buf, swap_bytes, rng, |rng| randomized_u22(rng)),
        5 => gen8(buf, swap_bytes, rng, |rng| randomized_u50(rng)),
        6 => gen10(buf, swap_bytes, rng, |rng| randomized_f80(rng)),
        _ => unreachable!(),
    }
}

/// Generates randomized bytes and puts them in an [`ArrayVec`].
pub fn randomized_bytes_into_arrayvec<const N: usize, R: Rng>(rng: &mut R, buf: &mut arrayvec::ArrayVec<u8, N>, len: usize) {
    fn gen<const N: usize, I: IntoIterator<Item = u8>, R: Rng>(
        buf: &mut arrayvec::ArrayVec<u8, N>, len: usize, rng: &mut R, mut f: impl FnMut(&mut R) -> I,
    ) {
        for src in repeat_with(|| f(rng)).flat_map(|v| IntoIterator::into_iter(v)).take(len) {
            buf.push(src);
        }
    }

    match rng.gen::<u8>() % 14 {
        0 => gen(buf, len, rng, |rng| randomized_f32(rng).to_be_bytes()),
        1 => gen(buf, len, rng, |rng| randomized_f64(rng).to_be_bytes()),
        2 => gen(buf, len, rng, |rng| randomized_f32(rng).to_le_bytes()),
        3 => gen(buf, len, rng, |rng| randomized_f64(rng).to_le_bytes()),
        4 => gen(buf, len, rng, |rng| randomized_u32(rng).to_be_bytes()),
        5 => gen(buf, len, rng, |rng| randomized_u64(rng).to_be_bytes()),
        6 => gen(buf, len, rng, |rng| randomized_u32(rng).to_le_bytes()),
        7 => gen(buf, len, rng, |rng| randomized_u64(rng).to_le_bytes()),
        8 => gen(buf, len, rng, |rng| randomized_u22(rng).to_be_bytes()),
        9 => gen(buf, len, rng, |rng| randomized_u22(rng).to_le_bytes()),
        10 => gen(buf, len, rng, |rng| randomized_u50(rng).to_be_bytes()),
        11 => gen(buf, len, rng, |rng| randomized_u50(rng).to_le_bytes()),
        12 => gen(buf, len, rng, |rng| randomized_f80(rng).to_be_bytes()),
        13 => gen(buf, len, rng, |rng| randomized_f80(rng).to_le_bytes()),
        _ => unreachable!(),
    }
}

/// Generates a randomized [`SystemState`], with only one memory mapping for the provided instruction `instr`.
pub fn random_state<A: Arch, M: MappableArea, R: Rng>(rng: &mut R, instr: &Instruction, mappable: &M, pc: u64) -> SystemState<A> {
    // TODO: Replace this with something better
    let accesses = MemoryAccesses::<A> {
        instr: *instr,
        memory: vec![MemoryAccess {
            kind: AccessKind::Executable,
            inputs: Inputs::unsorted(vec![Source::Dest(Dest::Reg(A::reg(A::PC), Size::qword()))]),
            size: instr.byte_len() as u64..instr.byte_len() as u64,
            calculation: AddressComputation::unscaled_sum(1),
            alignment: 1,
        }],
        use_trap_flag: true,
    };

    let gen = StateGen::new(&accesses, mappable).unwrap();

    SystemState::new(
        A::CpuState::create(|reg, value| {
            if reg.is_pc() {
                match value {
                    MutValue::Num(value) => *value = pc,
                    MutValue::Bytes(_) => unreachable!(),
                }
            } else {
                match value {
                    MutValue::Num(value) => *value = gen.randomize_register(rng, reg),
                    MutValue::Bytes(buf) => randomized_bytes_into_buffer(rng, buf),
                }
            }
        }),
        MemoryState::new(once((Addr::new(pc), Permissions::Execute, instr.bytes().to_vec()))),
    )
}
