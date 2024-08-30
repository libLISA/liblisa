// use std::{ops::Index, fmt::{Debug, Write}};

// use super::{GrowingBitmap, Bitmap, ResizableBitmap};

// #[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
// pub struct TinyBitmap56 {
//     data: [u8; 7],
//     len: u8,
// }

// impl TryFrom<&GrowingBitmap> for TinyBitmap56 {
//     type Error = ();

//     fn try_from(value: &GrowingBitmap) -> Result<Self, Self::Error> {
//         if value.is_empty() {
//             Ok(Self::default())
//         } else if value.len() <= 56 {
//             Ok(TinyBitmap56 {
//                 data: value.data()[0].to_le_bytes()[..7].try_into().unwrap(),
//                 len: value.len() as u8,
//             })
//         } else {
//             Err(())
//         }
//     }
// }

// impl TinyBitmap56 {
//     #[inline]
//     fn index(x: usize) -> (usize, usize) {
//         (x / 8, x % 8)
//     }

//     fn zeroize_past_end(&mut self) {
//         let last_index = self.len as usize / 8;

//         let rest = if self.len % 8 != 0 {
//             self.data[last_index] &= (1 << (self.len % 8)) - 1;
//             &mut self.data[last_index + 1..]
//         } else {
//             &mut self.data[last_index..]
//         };

//         for b in rest.iter_mut() {
//             *b = 0;
//         }
//     }
// }

// impl Bitmap for TinyBitmap56 {
//     fn get(&self, index: usize) -> bool {
//         let (index, shift) = Self::index(index);

//         (self.data.get(index).unwrap_or(&0) >> shift) & 1 != 0
//     }

//     fn set(&mut self, index: usize) -> bool {
//         if index >= 56 {
//             panic!("Index {index} is out of bounds [0, 56) for TinyBitmap56");
//         }

//         if index as u8 > self.len {
//             self.len = index as u8 + 1;
//         }

//         let (index, offset) = Self::index(index);

//         let mask = 1 << offset;
//         let changed = self.data[index] & mask == 0;
//         self.data[index] |= mask;

//         changed
//     }

//     fn clear(&mut self, index: usize) -> bool {
//         if index >= 56 {
//             panic!("Index {index} is out of bounds [0, 56) for TinyBitmap56");
//         }

//         if index as u8 > self.len {
//             self.len = index as u8 + 1;
//         }

//         let (index, offset) = Self::index(index);

//         let mask = 1 << offset;
//         let changed = self.data[index] & mask != 0;
//         self.data[index] &= !mask;

//         changed
//     }

//     fn is_all_zeros(&self) -> bool {
//         self.data == [0; 7]
//     }

//     fn is_all_ones(&self) -> bool {
//         let (full_u8s, ok) = if self.len % 8 == 0 {
//             (&self.data[..self.len as usize / 8], true)
//         } else if !self.data.is_empty() {
//             let v = self.data[self.data.len() - 1];
//             let last_ok = v == (1 << (self.len % 8)) - 1;
//             (&self.data[..self.data.len() - 1], last_ok)
//         } else {
//             (&[][..], true)
//         };

//         ok && full_u8s.iter().all(|&n| n == u8::MAX)
//     }

//     fn and_with(&mut self, other: &GrowingBitmap) -> bool {
//         if other.len() < self.len as usize {
//             self.len = other.len() as u8;
//         }

//         let mut changed = false;
//         for (lhs, rhs) in self.data.iter_mut().zip(other.data().iter().flat_map(|d| d.to_le_bytes())) {
//             let original = *lhs;
//             *lhs &= rhs;
//             changed |= original != *lhs;
//         }

//         changed
//     }
// }

// impl ResizableBitmap for TinyBitmap56 {
//     fn resize(&mut self, new_size: usize) {
//         if new_size > 56 {
//             panic!("Cannot resize a TinyBitmap56 to {new_size} bits")
//         }

//         self.len = new_size as u8;
//         self.zeroize_past_end();
//     }
// }

// impl Index<usize> for TinyBitmap56 {
//     type Output = bool;

//     fn index(&self, index: usize) -> &Self::Output {
//         if self.get(index) {
//             &true
//         } else {
//             &false
//         }
//     }
// }

// impl Debug for TinyBitmap56 {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         for index in 0..self.len {
//             f.write_char(if self.get(index as usize) {
//                 '1'
//             } else {
//                 '0'
//             })?;
//         }

//         Ok(())
//     }
// }
