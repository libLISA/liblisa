/// Convenience trait that rotates elements in a slice, and maps them to a new value.
pub trait MapRotated {
    /// The items in the slice.
    type Item;

    /// The output type of [`MapRotated::Output`].
    type Output<I>;

    /// Returns an iterator that maps every value to another value using `f`, but rotates the results by `start` positions.
    /// This means that the iterator returns `f(self[start])`, `f(self[start + 1])`, .., `f(self[0])`, `f(self[1])`, .., `f(self[start - 1])`.
    fn map_rotated<I>(self, start: usize, f: impl FnMut(Self::Item) -> I) -> Self::Output<I>;
}

impl<const N: usize, T> MapRotated for [T; N]
where
    T: Copy,
{
    type Item = T;
    type Output<I> = [I; N];

    fn map_rotated<I>(self, start: usize, mut f: impl FnMut(Self::Item) -> I) -> Self::Output<I> {
        let mut index = 0;
        [(); N].map(|_| {
            let item = self[(index + start) % self.len()];
            index += 1;
            f(item)
        })
    }
}
