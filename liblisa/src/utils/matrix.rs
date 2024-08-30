use std::fmt::{Debug, Write};

use super::bitmap::GrowingBitmap;

/// A matrix of boolean values, where matrix[x, y] == matrix[y, x]
#[derive(Default, Clone)]
pub struct Symmetric2DMatrix {
    data: GrowingBitmap,
    size: usize,
}

impl Symmetric2DMatrix {
    /// Creates an empty matrix.
    pub const fn new() -> Self {
        Symmetric2DMatrix {
            data: GrowingBitmap::new(),
            size: 0,
        }
    }

    /// Translates the 2d coordinates to a 1d index.
    #[inline]
    fn index(x: usize, y: usize) -> usize {
        let (x, y) = (x.min(y), x.max(y));

        // (0, 0) -> 0,
        // (0, 1) -> 1, (1, 1) -> 2,
        // (0, 2) -> 3, (1, 2) -> 4, (2, 2) -> 5,
        // (0, 3) -> 6, ..,
        // (0, 4) -> 10, ..,
        // Note how the base index is 1 + 2 + .. + y.
        // That computation can be simplified to (y + 1) * y / 2.

        let base_index = ((y + 1) * y) / 2;
        base_index + x
    }

    /// Returns the value of the matrix at position `(x, y)`.
    #[inline]
    pub fn get(&self, x: usize, y: usize) -> bool {
        self.data[Self::index(x, y)]
    }

    /// Sets the value of the matrix at position `(x, y)` to true.
    /// Returns true if the value at (x, y) was changed, otherwise false.
    pub fn set(&mut self, x: usize, y: usize) -> bool {
        self.size = self.size.max(x + 1).max(y + 1);

        self.data.set(Self::index(x, y))
    }

    /// Yields all indices `x` where `self.get(x, y)` is true.
    pub fn iter_row_indices(&self, y: usize) -> impl Iterator<Item = usize> + '_ {
        (0..self.size).filter(move |&x| self.get(x, y))
    }

    /// Returns the backing bitmap.
    pub fn raw_data(&self) -> &GrowingBitmap {
        &self.data
    }
}

impl Debug for Symmetric2DMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for y in 0..self.size {
            for x in 0..self.size {
                f.write_char(if x >= self.size - y {
                    ' '
                } else if self.get(x, y) {
                    '1'
                } else {
                    '0'
                })?;
            }

            f.write_char('\n')?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use log::debug;
    use rand::Rng;

    use super::Symmetric2DMatrix;

    #[test]
    pub fn is_symmetric() {
        let mut m = Symmetric2DMatrix::new();

        m.set(5, 1);
        assert!(m.get(1, 5));
        assert!(m.get(5, 1));

        m.set(2, 7);
        assert!(m.get(2, 7));
        assert!(m.get(7, 2));

        assert_eq!(m.iter_row_indices(7).collect::<Vec<_>>(), vec![2]);
        assert_eq!(m.iter_row_indices(2).collect::<Vec<_>>(), vec![7]);
    }

    #[test]
    pub fn middle_entries() {
        let mut m = Symmetric2DMatrix::new();
        for n in 0..256 {
            m.set(n, n);
        }

        for n in 0..256 {
            assert_eq!(m.iter_row_indices(n).collect::<Vec<_>>(), vec![n]);
        }
    }

    #[test]
    pub fn distinct_indices() {
        let mut seen = vec![false; 1000 * 1000];
        for x in 0..1000 {
            for y in x..1000 {
                let index = Symmetric2DMatrix::index(x, y);
                assert!(!seen[index]);

                seen[index] = true;
            }
        }
    }

    #[test]
    pub fn fuzz() {
        let mut rng = rand::thread_rng();
        for size in 1..100 {
            println!("Size {size}");

            let mut m = Symmetric2DMatrix::new();
            let mut arr = vec![false; size * size];

            debug!("Size {size}");

            for _ in 0..20_000 {
                let x = rng.gen_range(0..size);
                let y = rng.gen_range(0..size);

                debug!("    - setting ({x}, {y}) = true");

                m.set(x, y);
                arr[x * size + y] = true;
                arr[y * size + x] = true;

                for x in 0..size {
                    for y in 0..size {
                        assert_eq!(m.get(x, y), arr[x * size + y], "({x}, {y}) not equal; matrix: \n{m:?}");
                    }
                }
            }
        }
    }
}
