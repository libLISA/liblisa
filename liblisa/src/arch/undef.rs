//! Provides generic definitions for specifying undefined behavior on an architecture.

use std::fmt::{Debug, Display};

use crate::arch::{Arch, Register};
use crate::encoding::dataflows::{AddressComputation, Size};
use crate::semantics::default::computation::{Arg, ArgEncoding, OutputEncoding, SynthesizedComputation};
use crate::semantics::default::ops::Op;
use crate::semantics::default::Expression;
use crate::semantics::{Computation, IoType, ARG_NAMES};
use crate::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};

/// An oracle that can provide information about which outputs are undefined for any given instruction.
pub trait UndefProvider<A: Arch> {
    /// The error type returned by this provider.
    type Error;

    /// Returns a list of outputs that can be undefined, and the conditions under which they are undefined.
    fn undefined_outputs_of(&self, instr: &[u8]) -> Result<UndefinedOutputs<A>, Self::Error>;
}

/// A (part) of a register, or an address calculation and size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegOrMem<A: Arch> {
    /// A register
    Reg {
        /// The register
        reg: A::Reg,

        /// The area of the register
        size: Size,
    },
    /// A memory location
    Memory {
        /// The address calculation
        calculation: AddressComputation,

        /// The inputs for the address calculation
        inputs: Vec<RegOrMem<A>>,

        /// The number of bytes being read
        num_bytes: usize,
    },
}

impl<A: Arch> RegOrMem<A> {
    /// Creates a new [`RegOrMem::Reg`]
    pub fn new_reg(reg: A::Reg, size: Size) -> Self {
        Self::Reg {
            reg,
            size,
        }
    }

    /// The byte size of the storage location.
    pub fn num_bytes(&self) -> usize {
        match self {
            RegOrMem::Reg {
                size, ..
            } => size.num_bytes(),
            RegOrMem::Memory {
                num_bytes, ..
            } => *num_bytes,
        }
    }

    /// Creates a new [`RegOrMem`] from a flag.
    ///
    /// Converts the flag to the correct (register, size) pair.
    pub fn from_flag(target_flag: A::Flag) -> RegOrMem<A> {
        for reg in A::iter_regs() {
            if reg.is_flags() {
                for index in 0..reg.byte_size() {
                    let flag = A::flagreg_to_flags(reg, index, index)[0];
                    if target_flag == flag {
                        return RegOrMem::new_reg(reg, Size::new(index, index));
                    }
                }
            }
        }

        panic!("Flag not found: {target_flag:?}")
    }
}

/// An instruction output that may be undefined.
/// When the condition returns true, or is None, the `target` is undefined.
pub struct UndefinedOutput<A: Arch> {
    target: RegOrMem<A>,
    condition: Option<SynthesizedComputation>,
    inputs: Vec<RegOrMem<A>>,
}

struct DebugAsDisplay<T>(T);

impl<T: Display> std::fmt::Debug for DebugAsDisplay<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<A: Arch> Debug for UndefinedOutput<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UndefinedOutput")
            .field("target", &self.target)
            .field(
                "condition",
                &self
                    .condition
                    .as_ref()
                    .map(|condition| DebugAsDisplay(condition.display(ARG_NAMES))),
            )
            .field("inputs", &self.inputs)
            .finish()
    }
}

impl<A: Arch> UndefinedOutput<A> {
    /// Creates an unconditionally undefined output.
    pub fn from_target(target: RegOrMem<A>) -> Self {
        Self {
            target,
            condition: None,
            inputs: Vec::new(),
        }
    }

    /// Replaces the condition of this undefined output with a new condition.
    pub fn with_condition(mut self, condition: SynthesizedComputation, inputs: Vec<RegOrMem<A>>) -> Self {
        self.condition = Some(condition);
        self.inputs = inputs;
        self
    }

    /// Replaces the condition of this undefined output with a condition that declares the output undefined only if the value of `target` is zero.
    pub fn only_if_zero(mut self, target: RegOrMem<A>) -> Self {
        self.condition = Some(SynthesizedComputation::new(
            Expression::new(vec![Op::Hole(0), Op::IsZero]),
            vec![Arg::Input {
                index: 0,
                num_bits: (target.num_bytes() * 8).try_into().unwrap(),
                encoding: ArgEncoding::UnsignedBigEndian,
            }],
            Vec::new(),
            OutputEncoding::UnsignedBigEndian,
            IoType::Integer {
                num_bits: 1,
            },
        ));
        self.inputs = vec![target];

        self
    }

    /// The output that can be undefined.
    pub fn target(&self) -> &RegOrMem<A> {
        &self.target
    }

    /// The condition under which the output is undefined.
    pub fn condition(&self) -> Option<&SynthesizedComputation> {
        self.condition.as_ref()
    }

    /// The inputs for the condition.
    pub fn inputs(&self) -> &[RegOrMem<A>] {
        self.inputs.as_ref()
    }
}

#[derive(Debug, Default)]
/// A collection of [`UndefinedOutput`]s.
pub struct UndefinedOutputs<A: Arch> {
    items: Vec<UndefinedOutput<A>>,
}

/// A convenience trait that can convert various types into [`UndefinedOutputs`].
pub trait IntoUndefinedOutputs<A: Arch> {
    /// Converts `self` to an undefined output, and adds it to the list of undefined outputs `target`.
    fn add(self, target: &mut UndefinedOutputs<A>);
}

impl<A: Arch> UndefinedOutputs<A> {
    /// Creates an empty list of undefined outputs.
    pub fn new() -> Self {
        Self::default()
    }

    /// Computes the undefined outputs of the instruction `instr` using provider `provider`.
    pub fn of<P: UndefProvider<A>>(instr: &[u8], provider: &P) -> Result<UndefinedOutputs<A>, P::Error> {
        provider.undefined_outputs_of(instr)
    }

    /// The number of undefined outputs.
    #[must_use]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Whether this list of undefined outputs is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterates over all undefined outputs in this list.
    pub fn iter(&self) -> impl Iterator<Item = &UndefinedOutput<A>> {
        self.items.iter()
    }

    /// Merges `self` with `items` and returns a list of undefined outputs containing all undefined outputs from both lists.
    #[must_use]
    pub fn with(mut self, items: impl IntoUndefinedOutputs<A>) -> Self {
        items.add(&mut self);
        self
    }
}

impl<A: Arch> IntoUndefinedOutputs<A> for &[A::Flag] {
    fn add(self, target: &mut UndefinedOutputs<A>) {
        let mut unseen = FixedBitmapU64::<2>::new_all_ones(self.len());
        for reg in A::iter_regs() {
            if reg.is_flags() {
                for index in 0..reg.byte_size() {
                    let flag = A::flagreg_to_flags(reg, index, index)[0];
                    if let Some(position) = self.iter().position(|&f| f == flag) {
                        unseen.clear(position);
                        target
                            .items
                            .push(UndefinedOutput::from_target(RegOrMem::new_reg(reg, Size::new(index, index))));
                    }
                }
            }
        }

        assert!(unseen.is_all_zeros(), "Not all flags were found");
    }
}

impl<const N: usize, A: Arch> IntoUndefinedOutputs<A> for &[A::Flag; N] {
    fn add(self, target: &mut UndefinedOutputs<A>) {
        self.as_slice().add(target)
    }
}

impl<const N: usize, A: Arch> IntoUndefinedOutputs<A> for [A::Flag; N] {
    fn add(self, target: &mut UndefinedOutputs<A>) {
        self.as_slice().add(target)
    }
}

impl<A: Arch> IntoUndefinedOutputs<A> for UndefinedOutputs<A> {
    fn add(self, target: &mut UndefinedOutputs<A>) {
        target.items.extend(self.items)
    }
}

impl<A: Arch> IntoUndefinedOutputs<A> for () {
    fn add(self, _target: &mut UndefinedOutputs<A>) {}
}

impl<A: Arch> IntoUndefinedOutputs<A> for UndefinedOutput<A> {
    fn add(self, target: &mut UndefinedOutputs<A>) {
        target.items.push(self)
    }
}

impl<A: Arch> IntoUndefinedOutputs<A> for RegOrMem<A> {
    fn add(self, target: &mut UndefinedOutputs<A>) {
        target.items.push(UndefinedOutput::from_target(self))
    }
}
