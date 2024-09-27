use std::collections::HashMap;
use crate::{arch::Arch, encoding::dataflows::{Dest, IntoDestWithSize, Size}, state::Location, utils::bitmap::GrowingBitmap};
use log::trace;

/// Splits dests into smaller, non-overlapping chunks.
/// 
/// # Example
/// ```rust
/// use liblisa::arch::x64::{X64Arch, X64Reg, GpReg};
/// use liblisa::encoding::dataflows::{Dest, Size};
/// use liblisa::state::SplitDests;
/// const Rax: X64Reg = X64Reg::GpReg(GpReg::Rax);
/// 
/// let mut split = SplitDests::<X64Arch>::new();
/// split.split(Dest::Reg(Rax, Size::new(0, 3)));
/// split.split(Dest::Reg(Rax, Size::new(2, 5)));
/// 
/// assert_eq!(split.get(Dest::Reg(Rax, Size::new(2, 5))).collect::<Vec<_>>(), vec![
///     Dest::Reg(Rax, Size::new(2, 3)),
///     Dest::Reg(Rax, Size::new(4, 5)),
/// ])
/// ```
/// 
#[derive(Clone, Debug, Default)]
pub struct SplitDests<A: Arch> {
    outputs: HashMap<Location<A>, Vec<Size>>,
}

impl<A: Arch> SplitDests<A> {
    /// Creates an empty [`SplitDests`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Splits the location in `dest` into non-overlapping chunks.
    /// If the location has not been inserted before, the entire size is added as one chunk.
    /// If the location has been inserted before, the sizes are split such that only subsets 
    /// of one or more of the previously inserted [`Dest`]s are included.
    pub fn split(&mut self, dest: Dest<A>) {
        let location = Location::from(dest);
        let size = dest.size();
        let existing_sizes = self.outputs.remove(&location).unwrap_or_default();

        trace!("Splitting {dest:?} with existing sizes {existing_sizes:?}");

        let mut split_sizes = Vec::new();
        let mut covered = GrowingBitmap::new_all_zeros(size.end_byte + 1);
        for existing_size in existing_sizes {
            covered.set_range(existing_size.start_byte..existing_size.end_byte + 1);
            trace!("Checking {existing_size:?} vs {size:?}");
            if let Some((before, overlapping, after)) = size.split_by_overlap(existing_size) {
                trace!("Split into: {before:?} {overlapping:?} {after:?}");
                split_sizes.push(overlapping);

                for item in [before, after].into_iter().flatten() {
                    if existing_size.contains(&item) {
                        split_sizes.push(item);
                    }
                }
            } else {
                split_sizes.push(existing_size);
            }
        }

        trace!("Covered: {covered:?}");
        let mut index = size.start_byte;
        while index <= size.end_byte {
            if !covered[index] {
                let num = covered.iter()
                    .skip(index)
                    .take(size.end_byte + 1 - index)
                    .take_while(|&b| !b)
                    .count();

                let uncovered_size = Size::new(index, index + num - 1);
                trace!("Adding uncovered {uncovered_size:?}");
                split_sizes.push(uncovered_size);
                index += num;
            } else {
                index += 1;
            }
        }

        trace!("Result: {split_sizes:?}");
        self.outputs.insert(location, split_sizes);
    }

    /// Returns the non-overlapping chunks for the specified location `loc`.
    /// You must have called `split(loc)` at least once.
    /// If you have not, this function may panick.
    /// 
    /// Returns only the chunks that `loc` contains.
    pub fn get(&self, loc: Dest<A>) -> impl Iterator<Item = Dest<A>> + '_ {
        let loc_size = loc.size();
        self.outputs
            .get(&Location::from(loc))
            .iter()
            .flat_map(|v| v.iter())
            .flat_map(move |size| {
                if loc_size.contains(size) {
                    Some(loc.with_size(*size))
                } else {
                    // No partial overlaps!
                    assert!(!loc_size.overlaps(size));
                    None
                }
            })
            .collect::<Vec<_>>()
            .into_iter()
    }

    /// Returns all non-overlapping chunks for all locations.
    pub fn iter(&self) -> impl Iterator<Item = Dest<A>> + '_ {
        self.outputs.iter()
            .flat_map(|(loc, sizes)| sizes.iter().map(|&size| loc.into_dest_with_size(size)))
    }
}