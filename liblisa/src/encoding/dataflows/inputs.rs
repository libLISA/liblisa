use std::fmt::{Debug, Display};
use std::ops::{Index, IndexMut};

use serde::{Deserialize, Serialize};

use super::{Dest, Source};
use crate::arch::Arch;

/// A set of inputs to a dataflow or memory address computation.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[serde(bound = "")]
pub struct Inputs<A: Arch> {
    inputs: Vec<Source<A>>,
}

impl<A: Arch> Inputs<A> {
    /// Creates the inputs from the provided `inputs` without sorting.
    ///
    /// You should not sort inputs if you already have references to specific indices in the inputs.
    /// For example, if the inputs are part of a dataflow in an encoding.
    #[inline]
    pub fn unsorted(inputs: Vec<Source<A>>) -> Self {
        Inputs {
            inputs,
        }
    }

    /// Creates the inputs form the provided `inputs` and sorts them.
    ///
    /// You should not sort inputs if you already have references to specific indices in the inputs.
    /// For example, if the inputs are part of a dataflow in an encoding.
    #[inline]
    pub fn sorted(mut inputs: Vec<Source<A>>) -> Self {
        inputs.sort();
        Self::unsorted(inputs)
    }

    /// Iterates over all inputs
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Source<A>> {
        self.inputs.iter()
    }

    /// Iterates over `&mut` references to all inputs.
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Source<A>> {
        self.inputs.iter_mut()
    }

    /// Removes all inputs for which `f` returns false.
    #[inline]
    pub fn retain(&mut self, f: impl FnMut(&Source<A>) -> bool) {
        self.inputs.retain(f);
    }

    /// Returns the number of inputs.
    #[inline]
    pub fn len(&self) -> usize {
        self.inputs.len()
    }

    /// Returns true if the set of inputs is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inputs.is_empty()
    }

    /// Returns true if the set of inputs contains `item`.
    #[inline]
    pub fn contains(&self, item: &Source<A>) -> bool {
        self.inputs.contains(item)
    }

    /// Removes `item` from the inputs.
    /// If `item` does not exist in the inputs, no change occurs.
    #[inline]
    pub fn remove(&mut self, item: &Source<A>) {
        self.inputs.retain(|input| input != item);
    }

    /// Removes an input by index.
    #[inline]
    pub fn remove_index(&mut self, index: usize) {
        self.inputs.remove(index);
    }

    /// Pushes a new input at the end.
    /// Does not re-sort the inputs.
    #[inline]
    pub fn push(&mut self, item: Source<A>) {
        self.inputs.push(item)
    }
}

impl<A: Arch> Index<usize> for Inputs<A> {
    type Output = Source<A>;

    #[inline]
    fn index(&self, index: usize) -> &Source<A> {
        &self.inputs[index]
    }
}

impl<A: Arch> IndexMut<usize> for Inputs<A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Source<A> {
        &mut self.inputs[index]
    }
}

impl<A: Arch> Debug for Inputs<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inputs.fmt(f)
    }
}

// impl<A: Arch> FromIterator<Source<A>> for Inputs<A> {
//     fn from_iter<T: IntoIterator<Item = Source<A>>>(iter: T) -> Self {
//         iter.into_iter().collect::<Vec<Source<A>>>().into()
//     }
// }

impl<A: Arch> Display for Inputs<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (index, input) in self.inputs.iter().enumerate() {
            if index != 0 {
                write!(f, ", ")?;
            }

            write!(f, "{input}")?;
        }

        Ok(())
    }
}

impl<A: Arch> PartialEq<[A::GpReg]> for Inputs<A> {
    #[inline]
    fn eq(&self, other: &[A::GpReg]) -> bool {
        self.inputs.len() == other.len()
            && self.inputs.iter().zip(other.iter()).all(|(a, &b)| match a {
                Source::Dest(Dest::Reg(reg, _)) => reg == &A::reg(b),
                _ => false,
            })
    }
}

impl<A: Arch> PartialEq<&[A::GpReg]> for Inputs<A> {
    #[inline]
    fn eq(&self, other: &&[A::GpReg]) -> bool {
        self == *other
    }
}
