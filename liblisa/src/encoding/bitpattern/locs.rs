use serde::{Deserialize, Serialize};

/// The location of a source in an encoding.
/// Either a memory address computation or dataflow.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FlowInputLocation {
    /// An input located in a dataflow.
    InputForOutput {
        /// The index of the dataflow.
        output_index: usize,

        /// The index of the input in the sources of the dataflow.
        input_index: usize,
    },
    /// An imput located in a memory access
    MemoryAddress {
        /// The index of the memory access
        memory_index: usize,

        /// The index of the input in the sources of the memory address computation.
        input_index: usize,
    },
}

/// The location of an output in an encoding.
/// Either a dataflow destination, or memory output.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FlowOutputLocation {
    /// Refers to the destination of the nth dataflow.
    Output(usize),

    /// Refers to the memory area accessed by the nth memory access.
    MemoryAccess(usize),
}

impl FlowOutputLocation {
    /// Converts an output location into an input location.
    /// This converts destinations to sources, and memory area's to memory address calculation inputs.
    pub fn input(&self, input_index: usize) -> FlowInputLocation {
        match *self {
            FlowOutputLocation::Output(output_index) => FlowInputLocation::InputForOutput {
                output_index,
                input_index,
            },
            FlowOutputLocation::MemoryAccess(memory_index) => FlowInputLocation::MemoryAddress {
                memory_index,
                input_index,
            },
        }
    }
}

/// The location of a source or destination in an encoding.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FlowValueLocation {
    /// The destination of the nth dataflow.
    Output(usize),

    /// The source in a dataflow.
    InputForOutput {
        /// The index of the dataflow
        output_index: usize,

        /// The index of the input in the sources of the dataflow.
        input_index: usize,
    },

    /// An input in a memory access
    MemoryAddress {
        /// The index of the memory access
        memory_index: usize,

        /// The index of the input in the sources of the memory address computation.
        input_index: usize,
    },
}
impl FlowValueLocation {
    /// Returns true if the location is a source in the inputs of a memory address computation.
    pub fn is_address(&self) -> bool {
        matches!(self, FlowValueLocation::MemoryAddress { .. })
    }

    /// Returns true if the location is the destination or one of the sources of the dataflow with index `index_to_find`.
    pub fn is_in_output(&self, index_to_find: usize) -> bool {
        match *self {
            FlowValueLocation::Output(output_index) => output_index == index_to_find,
            FlowValueLocation::InputForOutput {
                output_index, ..
            } => output_index == index_to_find,
            FlowValueLocation::MemoryAddress {
                ..
            } => false,
        }
    }
}

impl From<FlowInputLocation> for FlowValueLocation {
    fn from(location: FlowInputLocation) -> Self {
        match location {
            FlowInputLocation::InputForOutput {
                output_index,
                input_index,
            } => FlowValueLocation::InputForOutput {
                output_index,
                input_index,
            },
            FlowInputLocation::MemoryAddress {
                memory_index,
                input_index,
            } => FlowValueLocation::MemoryAddress {
                memory_index,
                input_index,
            },
        }
    }
}

impl TryFrom<FlowValueLocation> for FlowInputLocation {
    type Error = ();

    fn try_from(location: FlowValueLocation) -> Result<Self, ()> {
        Ok(match location {
            FlowValueLocation::Output(_) => return Err(()),
            FlowValueLocation::InputForOutput {
                output_index,
                input_index,
            } => FlowInputLocation::InputForOutput {
                output_index,
                input_index,
            },
            FlowValueLocation::MemoryAddress {
                memory_index,
                input_index,
            } => FlowInputLocation::MemoryAddress {
                memory_index,
                input_index,
            },
        })
    }
}

impl PartialEq<FlowValueLocation> for FlowInputLocation {
    fn eq(&self, other: &FlowValueLocation) -> bool {
        &FlowValueLocation::from(*self) == other
    }
}
