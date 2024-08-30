//! A condensed summary of the architecture comparison, suitable for export to a file.

use serde::{Deserialize, Serialize};

use crate::arch::Arch;
use crate::encoding::indexed::{EncodingId, IndexedEncodings};
use crate::instr::InstructionFilter;
use crate::semantics::Computation;

/// Information about an architecture.
#[derive(Serialize, Deserialize)]
pub struct ArchInfo {
    /// A human-readable name of the architecture.
    pub name: String,
}

/// An identifier that references an architecture.
#[derive(Serialize, Deserialize)]
pub struct ArchId(pub usize);

/// Set of encodings shared between architectures.
#[derive(Serialize, Deserialize)]
pub struct SharedEncodings {
    /// The architectures that share the semantics of `encodings`.
    pub architectures: Vec<ArchId>,

    /// The encodings that have equivalent semantics on all `architectures`.
    pub encodings: Vec<EncodingId>,
}

/// A grouping of sets of encodings that cover the exact same instruction space (when restricted to `filter`).
#[derive(Serialize, Deserialize)]
pub struct SharedEncodingGroup {
    /// The filter to which all encodings should be restricted.
    pub filter: InstructionFilter,

    /// The sets of encodings.
    pub encodings: Vec<SharedEncodings>,
}

/// A collection of architectures and encoding groups that describes which encodings are semantically equivalent between different architectures.
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "C: Serialize", deserialize = "C: Deserialize<'de>"))]
pub struct ArchComparisonSummary<A: Arch, C: Computation> {
    /// [`ArchInfo`] for each architecture.
    pub architectures: Vec<ArchInfo>,

    /// Groups of encodings and their semantics.
    pub encodings: Vec<SharedEncodingGroup>,

    /// An indexing of [`EncodingId`] to [`Encoding`](crate::encoding::Encoding).
    pub index: IndexedEncodings<A, C>,
}
