use std::fmt::{self, Debug};

use crate::SynthesizerOutput;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CaseMap(u64);

impl CaseMap {
    pub fn new(matches: impl Iterator<Item = bool>) -> CaseMap {
        CaseMap(
            matches
                .enumerate()
                .fold(0u64, |acc, (index, b)| acc | if b { 1 << index } else { 0 }),
        )
    }

    pub fn new_from_u64(map: u64) -> CaseMap {
        CaseMap(map)
    }

    #[must_use]
    pub fn is_none(&self) -> bool {
        self.0 == 0
    }

    #[must_use]
    pub fn matches(&self, index: usize) -> bool {
        self.0 & (1 << index) != 0
    }

    #[must_use]
    pub fn first_index(&self) -> usize {
        self.0.trailing_zeros() as usize
    }

    #[must_use]
    pub fn as_u64(&self) -> u64 {
        self.0
    }

    #[must_use]
    pub fn overlaps(&self, other: CaseMap) -> bool {
        self.0 & other.0 != 0 || self.0 == other.0
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn restrict_to(&mut self, other: CaseMap) {
        self.0 &= other.0;
    }

    pub fn covers(&self, covered: CaseMap) -> bool {
        self.0 & covered.0 == covered.0
    }
}

impl SynthesizerOutput for CaseMap {
    type Borrowed<'o> = &'o CaseMap
        where Self: 'o;

    fn borrow(&self) -> Self::Borrowed<'_> {
        self
    }
}

impl Debug for CaseMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.count_ones() == 1 {
            write!(f, "{}", self.first_index())
        } else {
            write!(f, "<")?;

            let mut first = true;
            for index in 0..64 {
                if self.matches(index) {
                    if !first {
                        write!(f, ", ")?;
                    }

                    first = false;
                    write!(f, "{index}")?;
                }
            }

            write!(f, ">")
        }
    }
}
