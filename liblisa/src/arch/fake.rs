//! An implementation of a fake architecture that is used in various tests.

use std::fmt::{self, Debug, Display};

use serde::{Deserialize, Serialize};
pub use FakeFlag::*;
pub use FakeReg::*;

use crate::arch::{Arch, CpuState, Flag, NumberedRegister, Register};
use crate::oracle::{FallbackBatchObserveIter, MappableArea, Observation, Oracle, OracleError};
use crate::state::{Addr, AsSystemState, StateByte, SystemState};
use crate::value::{MutValue, Value, ValueType};

/// A simple, fake architecture for testing.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Hash, Debug, PartialEq, Eq, Copy, Clone, Default, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FakeArch;

/// The register available in [`FakeArch`].
///
/// - `R_` are integer registers.
/// - `B_` are byte registers.
/// - `RZ` is the zero register
/// - `RF` is the flag register. It contains three flags (F0, F1, F2)
#[allow(missing_docs)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Hash, Debug, PartialEq, Eq, Copy, Clone, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FakeReg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    B0,
    B1,
    B2,
    RF,
    RZ,
}

/// The flags available in [`FakeArch`].
#[allow(missing_docs)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Hash, Debug, PartialEq, Eq, Copy, Clone, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FakeFlag {
    F0 = 0,
    F1,
    F2,
}

const NUM_REGS: usize = 16;

/// The CPU state for [`FakeArch`].
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Hash, Debug, PartialEq, Eq, Copy, Clone, Default, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FakeState {
    regs: [u64; 20],
    byte_regs: [[u8; 8]; 3],
}

impl Arch for FakeArch {
    type CpuState = FakeState;
    type Reg = FakeReg;
    type GpReg = FakeReg;
    type Flag = FakeFlag;

    const PAGE_BITS: usize = 12;
    const PC: Self::GpReg = FakeReg::R0;
    const ZERO: Self::GpReg = FakeReg::RZ;
    const INSTRUCTION_ALIGNMENT: usize = 1;

    fn reg(reg: Self::GpReg) -> Self::Reg {
        reg
    }

    fn iter_gpregs() -> impl Iterator<Item = Self::GpReg> {
        use FakeReg::*;
        vec![R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, RF].into_iter()
    }

    fn iter_regs() -> impl Iterator<Item = Self::Reg> {
        use FakeReg::*;
        vec![
            R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, B0, B1, B2, RF,
        ]
        .into_iter()
    }

    fn flagreg_to_flags(reg: FakeReg, start_byte: usize, end_byte: usize) -> &'static [Self::Flag] {
        assert_eq!(reg, FakeReg::RF);
        &[FakeFlag::F0, FakeFlag::F1, FakeFlag::F2][start_byte..=end_byte]
    }

    fn try_reg_to_gpreg(reg: Self::Reg) -> Option<Self::GpReg> {
        Some(reg)
    }
}

impl CpuState<FakeArch> for FakeState {
    type DiffMask = ();

    fn gpreg(&self, reg: FakeReg) -> u64 {
        self.regs[reg as usize]
    }

    fn reg(&self, reg: <FakeArch as Arch>::Reg) -> Value<'_> {
        match reg {
            R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | RF => {
                Value::Num(self.regs[reg as usize])
            },
            B0 => Value::Bytes(&self.byte_regs[0]),
            B1 => Value::Bytes(&self.byte_regs[1]),
            B2 => Value::Bytes(&self.byte_regs[2]),
            RZ => panic!(),
        }
    }

    fn modify_reg<F: FnOnce(MutValue)>(&mut self, reg: <FakeArch as Arch>::Reg, update: F) {
        match reg {
            R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | RF => {
                update(MutValue::Num(&mut self.regs[reg as usize]))
            },
            B0 => update(MutValue::Bytes(&mut self.byte_regs[0])),
            B1 => update(MutValue::Bytes(&mut self.byte_regs[1])),
            B2 => update(MutValue::Bytes(&mut self.byte_regs[2])),
            RZ => panic!(),
        }
    }

    fn flag(&self, flag: FakeFlag) -> bool {
        (self.regs[FakeReg::RF as usize] >> (flag as usize * 8)) & 1 > 0
    }

    fn set_gpreg(&mut self, reg: FakeReg, value: u64) {
        self.regs[reg as usize] = value;
    }

    fn set_flag(&mut self, flag: FakeFlag, value: bool) {
        let mask = 1 << (flag as usize * 8);
        if value {
            self.regs[FakeReg::RF as usize] |= mask;
        } else {
            self.regs[FakeReg::RF as usize] &= !mask;
        }
    }

    fn size() -> usize {
        NUM_REGS * 8
    }

    fn state_byte_to_reg(byte: StateByte) -> (<FakeArch as Arch>::Reg, usize) {
        (
            match byte.as_usize() / 8 {
                0 => FakeReg::R0,
                1 => FakeReg::R1,
                2 => FakeReg::R2,
                3 => FakeReg::R3, // TODO: Rest of the regs
                _ => panic!(),
            },
            byte.as_usize() % 8,
        )
    }

    fn reg_to_state_byte(reg: <FakeArch as Arch>::Reg, byte: usize) -> StateByte {
        StateByte::new(reg as usize * 8 + byte)
    }

    fn find_differences<F: FnMut(StateByte)>(&self, other: &Self, found: &mut F) {
        for (index, (left, right)) in self
            .regs
            .iter()
            .zip(other.regs.iter())
            .enumerate()
            .filter(|(_, (left, right))| left != right)
        {
            for byte in 0..8 {
                let l = (left >> (byte * 8)) as u8;
                let r = (right >> (byte * 8)) as u8;

                if l != r {
                    found(StateByte::new(index * 8 + byte));
                }
            }
        }
    }

    fn create_diff_mask<I: Iterator<Item = StateByte>>(_items: I) -> Self::DiffMask {}
}

impl Display for FakeState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

impl fmt::Display for FakeReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl fmt::Display for FakeFlag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl NumberedRegister for FakeReg {
    fn as_num(&self) -> usize {
        match self {
            R0 => 0,
            R1 => 1,
            R2 => 2,
            R3 => 3,
            R4 => 4,
            R5 => 5,
            R6 => 6,
            R7 => 7,
            R8 => 8,
            R9 => 9,
            R10 => 10,
            R11 => 11,
            R12 => 12,
            R13 => 13,
            R14 => 14,
            R15 => 15,
            B0 => 16,
            B1 => 17,
            B2 => 18,
            RF => 19,
            RZ => 20,
        }
    }

    fn from_num(num: usize) -> Self {
        match num {
            0 => R0,
            1 => R1,
            2 => R2,
            3 => R3,
            4 => R4,
            5 => R5,
            6 => R6,
            7 => R7,
            8 => R8,
            9 => R9,
            10 => R10,
            11 => R11,
            12 => R12,
            13 => R13,
            14 => R14,
            15 => R15,
            16 => B0,
            17 => B1,
            18 => B2,
            19 => RF,
            20 => RZ,
            _ => unreachable!(),
        }
    }
}

impl Register for FakeReg {
    fn is_flags(&self) -> bool {
        self == &Self::RF
    }

    fn byte_size(&self) -> usize {
        match self {
            Self::RF => 3,
            Self::B0 | Self::B1 | Self::B2 => 32,
            _ => 8,
        }
    }

    fn mask(&self) -> Option<u64> {
        match self {
            Self::RF => Some(0x010101),
            _ => None,
        }
    }

    fn is_pc(&self) -> bool {
        self == &FakeArch::PC
    }

    fn is_zero(&self) -> bool {
        self == &FakeArch::ZERO
    }

    fn is_addr_reg(&self) -> bool {
        false
    }

    fn reg_type(self) -> ValueType {
        if matches!(self, FakeReg::B0 | FakeReg::B1 | FakeReg::B2) {
            ValueType::Bytes(8)
        } else {
            ValueType::Num
        }
    }
}

impl Flag for FakeFlag {
    fn iter() -> impl Iterator<Item = Self> {
        vec![FakeFlag::F0, FakeFlag::F1, FakeFlag::F2].into_iter()
    }
}

/// The [`MappableArea`] for [`FakeOracle`].
///
/// All addresses are valid.
#[derive(Copy, Clone, Debug)]
pub struct AnyArea;

impl MappableArea for AnyArea {
    fn can_map(&self, _addr: Addr) -> bool {
        true
    }
}

/// A fake observer for [`FakeArch`].
///
/// Observations are performed by invoking a closure provided to [`FakeOracle::new`].
pub struct FakeOracle<F, M> {
    op: F,
    scan_memory_accesses: M,
}

impl<F, M> FakeOracle<F, M>
where
    F: Fn(&SystemState<FakeArch>) -> Result<SystemState<FakeArch>, OracleError>,
    M: Fn(&SystemState<FakeArch>) -> Result<Vec<Addr>, OracleError>,
{
    /// Instantiates a new oracle.
    ///
    /// The `op` function should execute the instruction on the provided CPU state.
    /// The `scan_memory_accesses` function should return a list of all memory addresses accessed by the instruction, given the specific CPU state.
    pub fn new(op: F, scan_memory_accesses: M) -> FakeOracle<F, M> {
        FakeOracle {
            op,
            scan_memory_accesses,
        }
    }
}

impl<F, M> Oracle<FakeArch> for FakeOracle<F, M>
where
    F: Fn(&SystemState<FakeArch>) -> Result<SystemState<FakeArch>, OracleError>,
    M: Fn(&SystemState<FakeArch>) -> Result<Vec<Addr>, OracleError>,
{
    type MappableArea = AnyArea;

    fn mappable_area(&self) -> Self::MappableArea {
        AnyArea
    }

    fn page_size(&mut self) -> u64 {
        4096
    }

    fn observe(&mut self, before: &SystemState<FakeArch>) -> Result<SystemState<FakeArch>, OracleError> {
        (self.op)(before)
    }

    fn scan_memory_accesses(&mut self, before: &SystemState<FakeArch>) -> Result<Vec<Addr>, OracleError> {
        (self.scan_memory_accesses)(before)
    }

    fn debug_dump(&mut self) {}

    fn restart(&mut self) {}

    fn kill(self) {}

    fn batch_observe_iter<'a, S: AsSystemState<FakeArch> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, FakeArch>> {
        FallbackBatchObserveIter::new(self, states.into_iter())
    }

    fn batch_observe_gpreg_only_iter<'a, S: AsSystemState<FakeArch> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, states: I,
    ) -> impl Iterator<Item = Observation<S, FakeArch>> {
        self.batch_observe_iter(states)
    }

    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool = false;
}
