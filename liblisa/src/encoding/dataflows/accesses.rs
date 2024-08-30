use std::fmt::{Debug, Display};
use std::ops::{Index, IndexMut, Range};

use serde::{Deserialize, Serialize};

use crate::arch::{Arch, Register};
use crate::encoding::bitpattern::FlowValueLocation;
use crate::encoding::dataflows::{AddressComputation, Inputs, Source};
use crate::instr::Instruction;
use crate::semantics::Computation;
use crate::state::{Addr, Location, SystemState};

/// A collection of memory accesses.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct MemoryAccesses<A: Arch> {
    /// The instruction for which these memory accesses are relevant.
    pub instr: Instruction,

    /// The set of memory accesses performed by `instr`.
    pub memory: Vec<MemoryAccess<A>>,

    /// Whether the trap flag should be used to observe `instr`.
    /// Memory access analysis will detect when an instruction can jump, and if so, set this field to true.
    pub use_trap_flag: bool,
}

impl<A: Arch> Index<usize> for MemoryAccesses<A> {
    type Output = MemoryAccess<A>;

    #[inline]
    fn index(&self, index: usize) -> &MemoryAccess<A> {
        &self.memory[index]
    }
}

impl<A: Arch> IndexMut<usize> for MemoryAccesses<A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut MemoryAccess<A> {
        &mut self.memory[index]
    }
}

/// The type of access that is performed.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AccessKind {
    /// The memory is only read.
    Input,

    /// The memory is written (and potentially also read).
    InputOutput,

    /// The memory contains the instruction that is executed.
    Executable,
}

/// A memory access.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "schemars",
    schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")
)]
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct MemoryAccess<A: Arch> {
    /// The type of access that is performed.
    pub kind: AccessKind,

    /// The inputs for `calculation`.
    pub inputs: Inputs<A>,

    /// The determined size range of the access.
    /// The lower bound is the largest number of bytes that could be observed as being acesssed.
    /// The upper bound is set to one below the smallest byte index for which we could observe that it was not accessed.
    pub size: Range<u64>,

    /// A simple expression for the calculation of the address of the form i1 + i2 + .. + i_k * c + i_k+1 + i_k+1 .. i_n + c.
    /// That is, all inputs are summed, one input can be multiplied by a certain factor, which is then offset by a constant value c.
    /// This allows for the computation of most common addresses. It speeds up enumeration by ~20% on average up to ~40% in extreme
    /// cases. Obviously the speedup gets bigger if the amount of memory accesses increases or if the number of randomize_new() and
    /// adapt() calls is greater.
    pub calculation: AddressComputation,

    /// An alignment of 1 means that every address is OK. An alignment of 2 means that only addresses of the form 2n are ok.
    /// An alignment of 4 means that addresses of the form 4n are OK. Etc.
    /// NOTE: Only powers of 2 are acceptable values. Any other value will produce unspecified behavior.
    pub alignment: usize,
}

impl<A: Arch> Debug for MemoryAccess<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryAccess")
            .field("kind", &self.kind)
            .field("inputs", &self.inputs)
            .field("size", &self.size)
            .field(
                "calculation",
                &self.calculation.display(&["A", "B", "C", "D"][0..self.inputs.len()]),
            )
            .field("alignment", &self.alignment)
            .finish()
    }
}

impl<A: Arch> MemoryAccess<A> {
    /// The inputs of the address calculation.
    pub fn inputs(&self) -> &Inputs<A> {
        &self.inputs
    }

    /// Computes the address that this memory access will access, given the provided CPU state.
    pub fn compute_address(&self, state: &SystemState<A>) -> Addr {
        Addr::new(self.calculation.compute(&self.inputs, state))
    }

    /// Returns true if the memory address is fixed or only dependent on immediate values in the instruction.
    pub fn has_fixed_addr(&self) -> bool {
        self.inputs
            .iter()
            .all(|source| matches!(source, Source::Imm(_) | Source::Const { .. }))
    }

    /// Computes the fixed address for this access.
    /// Only returns a valid value if [`Self::has_fixed_addr`] returns true.
    pub fn compute_fixed_addr(&self) -> Addr {
        self.compute_address(&SystemState::<A>::default())
    }
}

impl<A: Arch> MemoryAccesses<A> {
    /// Returns the largest number of bytes that can be in the provided storage location.
    pub fn max_size_of(&self, location: &Location<A>) -> usize {
        match location {
            Location::Reg(reg) => reg.byte_size(),
            Location::Memory(index) => self.memory[*index].size.end as usize,
        }
    }

    /// Slices the memory accesses to only include the first `length` accesses.
    pub fn slice(&self, length: usize) -> MemoryAccesses<A> {
        MemoryAccesses {
            instr: self.instr,
            memory: self.memory[..length].to_vec(),
            use_trap_flag: self.use_trap_flag,
        }
    }

    /// Iterates over all accesses.
    pub fn iter(&self) -> impl Iterator<Item = &MemoryAccess<A>> {
        self.memory.iter()
    }

    /// Returns the number of accesses.
    #[must_use]
    pub fn len(&self) -> usize {
        self.memory.len()
    }

    /// Returns true if there are no accesses.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Maps all address computations and inputs to new values.
    pub fn map_computations(
        &self, mut f: impl FnMut(usize, &Inputs<A>, &AddressComputation) -> (Inputs<A>, AddressComputation),
    ) -> MemoryAccesses<A> {
        MemoryAccesses {
            instr: self.instr,
            memory: self
                .memory
                .iter()
                .enumerate()
                .map(|(index, ma)| {
                    let (inputs, calculation) = f(index, &ma.inputs, &ma.calculation);
                    MemoryAccess {
                        kind: ma.kind,
                        size: ma.size.clone(),
                        calculation,
                        inputs,
                        alignment: ma.alignment,
                    }
                })
                .collect(),
            use_trap_flag: self.use_trap_flag,
        }
    }
}

impl<A: Arch> MemoryAccesses<A> {
    /// Individually maps all computations and all inputs of all memory accesses to new values.
    pub fn map(
        &self, instr: Instruction, f: impl Fn(FlowValueLocation, &Source<A>) -> Option<Source<A>>,
        map_address_computations: impl Fn(usize, &AddressComputation) -> Option<AddressComputation>,
    ) -> MemoryAccesses<A> {
        MemoryAccesses {
            instr,
            memory: self
                .memory
                .iter()
                .enumerate()
                .map(|(memory_index, ma)| {
                    let inputs = Inputs::unsorted(
                        ma.inputs
                            .iter()
                            .enumerate()
                            .flat_map(|(input_index, input)| {
                                f(
                                    FlowValueLocation::MemoryAddress {
                                        memory_index,
                                        input_index,
                                    },
                                    input,
                                )
                            })
                            .collect::<Vec<_>>(),
                    );

                    MemoryAccess {
                        kind: ma.kind,
                        size: ma.size.clone(),
                        // We keep the calculation if the number of inputs remains the same
                        calculation: if ma.inputs.len() == inputs.len() {
                            map_address_computations(memory_index, &ma.calculation).unwrap_or(ma.calculation)
                        } else {
                            panic!()
                        },
                        inputs,
                        alignment: ma.alignment,
                    }
                })
                .collect::<Vec<_>>(),
            use_trap_flag: self.use_trap_flag,
        }
    }
}

impl Display for AccessKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccessKind::Input => f.write_str("input"),
            AccessKind::InputOutput => f.write_str("input/output"),
            AccessKind::Executable => f.write_str("executable"),
        }
    }
}

impl<A: Arch> Display for MemoryAccesses<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;

        for (index, access) in self.memory.iter().enumerate() {
            write!(f, "{access}")?;
            if index != self.memory.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, "]")?;

        Ok(())
    }
}

impl<A: Arch> Display for MemoryAccess<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[size {}..{}] = ", self.kind, self.size.start, self.size.end)?;

        let input_names = self.inputs.iter().map(|i| format!("{i}")).collect::<Vec<_>>();
        write!(f, "{}", self.calculation.display(&input_names))?;

        Ok(())
    }
}
