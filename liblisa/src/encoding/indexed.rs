//! Provides a collection type for [`crate::encoding::Encoding`]s that can be used in self-referential structures and can be serialized to disk.
//!
//! When building self-referential datastructures or serializing to disk, it is not possible to use references.
//! The [`IndexedEncodings`] type can be used to obtain [`EncodingId`]s.
//! These IDs reference encodings in the [`IndexedEncodings`] type.
//! The IDs can be safely used in self-referential types and can be serialized to disk.

use std::ops::Index;

use serde::{Deserialize, Serialize};

use crate::arch::Arch;
use crate::encoding::EncodingWithFilters;
use crate::semantics::Computation;

/// A reference to an encoding in an [`IndexedEncodings`] collection.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, bitcode::Encode, bitcode::Decode)]
pub struct EncodingId(usize);

impl EncodingId {
    /// Returns the ID as an `usize`.
    pub fn as_usize(&self) -> usize {
        self.0
    }

    /// Creates an EncodingId from an `usize`.
    pub fn from_usize(n: usize) -> EncodingId {
        Self(n)
    }
}

/// A collection of encodings which can be accessed using [`EncodingId`]s.
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct IndexedEncodings<A: Arch, C: Computation> {
    encodings: Vec<EncodingWithFilters<A, C>>,
}

impl<A: Arch, C: Computation> Default for IndexedEncodings<A, C> {
    fn default() -> Self {
        Self {
            encodings: Vec::new(),
        }
    }
}

impl<A: Arch, C: Computation> IndexedEncodings<A, C> {
    /// Creates an empty collection.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new encoding.
    /// The ID returned can be permanently used to obtain a reference to the encoding from this collection.
    pub fn add(&mut self, encoding: EncodingWithFilters<A, C>) -> EncodingId {
        let id = EncodingId(self.encodings.len());
        self.encodings.push(encoding);
        id
    }

    /// Returns the number of encodings in the collection.
    #[must_use]
    pub fn len(&self) -> usize {
        self.encodings.len()
    }

    /// Returns true if the collection contains no encodings.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterates over all encodings in the collection.
    pub fn all(&self) -> impl Iterator<Item = &EncodingWithFilters<A, C>> {
        self.encodings.iter()
    }
}

impl<A: Arch, C: Computation> Index<EncodingId> for IndexedEncodings<A, C> {
    type Output = EncodingWithFilters<A, C>;

    fn index(&self, index: EncodingId) -> &Self::Output {
        &self.encodings[index.0]
    }
}

impl<'a, A: Arch, C: Computation> Index<&'a EncodingId> for IndexedEncodings<A, C> {
    type Output = EncodingWithFilters<A, C>;

    fn index(&self, index: &'a EncodingId) -> &Self::Output {
        &self[*index]
    }
}
