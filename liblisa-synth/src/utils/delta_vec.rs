use std::marker::PhantomData;

use crate::search::{CompressedIterComputation, CompressedIterComputationWithExtraData, ExtraDataSpec};

pub trait DeltaVecItem {
    fn as_value(&self) -> u64;

    fn reconstitute(value: u64) -> Self;
}

impl DeltaVecItem for CompressedIterComputation {
    fn as_value(&self) -> u64 {
        self.as_u64()
    }

    fn reconstitute(value: u64) -> Self {
        Self::from_u64(value)
    }
}

impl<E: ExtraDataSpec> DeltaVecItem for CompressedIterComputationWithExtraData<E> {
    fn as_value(&self) -> u64 {
        self.as_u64()
    }

    fn reconstitute(value: u64) -> Self {
        Self::from_u64(value)
    }
}

impl DeltaVecItem for u64 {
    fn as_value(&self) -> u64 {
        *self
    }

    fn reconstitute(value: u64) -> Self {
        value
    }
}

#[derive(Clone)]
pub struct DeltaVec<T> {
    data: Vec<u16>,
    first: u64,
    last: u64,
    len: usize,
    _phantom: PhantomData<T>,
}

impl<T: DeltaVecItem> Default for DeltaVec<T> {
    fn default() -> Self {
        Self {
            data: Vec::new(),
            first: 0,
            last: 0,
            len: 0,
            _phantom: PhantomData,
        }
    }
}

impl<T: DeltaVecItem> DeltaVec<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, item: T) {
        if self.is_empty() {
            self.first = item.as_value();
            self.last = item.as_value();
            self.len += 1;
        } else {
            let delta = item.as_value() - self.last;
            self.last = item.as_value();
            self.len += 1;

            assert!(delta > 0);

            if let Ok(delta) = delta.try_into() {
                self.data.push(delta);
            } else {
                let size = if delta >> 32 == 0 {
                    2
                } else if delta >> 48 == 0 {
                    3
                } else {
                    4
                };

                for _ in 1..size {
                    self.data.push(0);
                }

                for n in (0..size).rev() {
                    self.data.push((delta >> (n * 16)) as u16);
                }
            }
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn first(&self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(T::reconstitute(self.first))
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn retain(&mut self, f: impl FnMut(&T) -> bool) {
        // TODO: More efficient implementation
        let mut new = Self::new();
        new.extend(self.drain().filter(f));
        *self = new
    }

    pub fn iter(&self) -> impl Iterator<Item = T> + '_ {
        Iter {
            done: self.is_empty(),
            iter: self.data.iter().copied(),
            current: self.first,
        }
        .map(|value| T::reconstitute(value))
    }

    pub fn drain(&mut self) -> impl Iterator<Item = T> + '_ {
        Iter {
            done: self.is_empty(),
            iter: self.data.drain(..),
            current: self.first,
        }
        .map(|value| T::reconstitute(value))
    }
}

pub struct Iter<I> {
    iter: I,
    done: bool,
    current: u64,
}

fn read_single_delta(iter: &mut impl Iterator<Item = u16>) -> Option<u64> {
    iter.next().map(|n| {
        if n != 0 {
            n as u64
        } else {
            let mut len = 1;
            let n = loop {
                let n = iter.next().unwrap();
                if n == 0 {
                    len += 1;
                } else {
                    break n
                }
            };

            let mut delta = n as u64;
            while len > 0 {
                len -= 1;
                let n = iter.next().unwrap();
                delta = (delta << 16) | (n as u64);
            }

            delta
        }
    })
}

impl<I: Iterator<Item = u16>> Iterator for Iter<I> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            None
        } else {
            let result = self.current;

            if let Some(delta) = read_single_delta(&mut self.iter) {
                self.current += delta;
            } else {
                self.done = true;
            }

            Some(result)
        }
    }
}

impl<T: DeltaVecItem> Extend<T> for DeltaVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }
}

impl<T: DeltaVecItem> FromIterator<T> for DeltaVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut result = Self::new();
        result.extend(iter);

        result
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::DeltaVec;

    #[test]
    pub fn push_then_iter() {
        let mut c = DeltaVec::<u64>::new();
        c.push(0x123);
        c.push(0x125);
        c.push(0x777);
        c.push(0x1234_3210_0777);

        assert_eq!(c.iter().collect::<Vec<_>>(), vec![0x123, 0x125, 0x777, 0x1234_3210_0777]);
    }
}
