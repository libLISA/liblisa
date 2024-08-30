//! Definitions for the x86-64 architecture.
//!
//! The definition includes features up to AVX2.
//! AVX-512 registers are not modelled.

mod disasm;

#[cfg(feature = "x64-undef")]
pub mod undef;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::mem::size_of;
use std::ops::{Deref, DerefMut, Index, IndexMut, Range};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;

use disasm::{OpcodeMap, ParsedInstructionPrefixes, Prefix, SimplePrefix};
use itertools::Itertools;
use log::trace;
use rustc_apfloat::ieee::X87DoubleExtended;
use rustc_apfloat::Float;
use serde::{Deserialize, Serialize};

use crate::arch::{Arch, CpuState, Flag, NumberedRegister, Register, Scope};
use crate::state::{StateByte, SystemStateIoPair};
use crate::value::{AsValue, MutValue, Value, ValueType};

/// A prefix scope for enumeration.
/// This prefix scope aims to achieve maximal coverage, with acceptable runtime.
///
/// The prefix enforces a prefix ordering:
///
/// 1. LOCK
/// 2. REX prefix
///
/// Additionally, it excludes the following prefixes:
///
/// 1. REP/REPNZ
/// 2. Segment overrides
/// 3. Data size overrides
/// 4. Address size overrides
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PrefixScope;

impl Scope for PrefixScope {
    fn is_instr_in_scope(&self, b: &[u8]) -> bool {
        let (parsed, b) = ParsedInstructionPrefixes::parse(b);
        let prefixes = parsed.prefixes();

        trace!("Parsed prefixes: {prefixes:?}");

        if prefixes.iter().any(|prefix| {
            matches!(
                prefix,
                Prefix::Simple(
                    SimplePrefix::Repnz
                        | SimplePrefix::Repz
                        | SimplePrefix::OverrideCS
                        | SimplePrefix::OverrideSS
                        | SimplePrefix::OverrideDS
                        | SimplePrefix::OverrideES
                        | SimplePrefix::OverrideFS
                        | SimplePrefix::OverrideGS
                        | SimplePrefix::DataSizeOverride
                        | SimplePrefix::AddrSizeOverride
                )
            )
        }) {
            return false;
        }

        if !is_sorted_by_key_and_unequal(prefixes, |prefix| match prefix {
            // VEX prefixes do not need any other prefixes
            Prefix::Vex2(_)
            | Prefix::Vex3(_)
            | Prefix::IncompleteVex2
            | Prefix::IncompleteVex3
            | Prefix::Xop
            | Prefix::BrokenXop => 0,
            Prefix::Simple(v) => match v {
                // Prefix group 1
                SimplePrefix::Lock | SimplePrefix::Repnz | SimplePrefix::Repz => 1,

                // Prefix group 2
                SimplePrefix::OverrideCS
                | SimplePrefix::OverrideSS
                | SimplePrefix::OverrideDS
                | SimplePrefix::OverrideES
                | SimplePrefix::OverrideFS
                | SimplePrefix::OverrideGS => 2,

                // Prefix group 3
                SimplePrefix::DataSizeOverride => 3,

                // Prefix group 4
                SimplePrefix::AddrSizeOverride => 4,
            },
            Prefix::Rex(_) => 5,

            // The opcode map is always the last prefix
            Prefix::OpcodeMap(_) => i64::MAX,
        }) {
            return false;
        }

        // Exclude the unused (according to the docs) opcode maps
        if prefixes.iter().any(|p| match p {
            Prefix::Vex3(vex3) => vex3.m.is_invalid(),
            _ => false,
        }) {
            return false;
        }

        !matches!(
            (parsed.effective_opcode_map(), b),
            // Exclude LSS from analysis because we can't analyze it properly (due to segments) and it is really slow.
            (Some(OpcodeMap::Map0F), [0xB2 | 0xB4 | 0xB5, ..])
        )
    }
}

fn is_sorted_by_key_and_unequal<T>(items: &[T], value: impl Fn(&T) -> i64) -> bool {
    items.windows(2).all(|w| value(&w[0]) < value(&w[1]))
}

/// Defines the x86-64 architecture.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default, PartialOrd, Ord, Serialize, Deserialize)]
pub struct X64Arch;

impl Arch for X64Arch {
    type CpuState = X64State;
    type Reg = X64Reg;
    type GpReg = GpReg;
    type Flag = X64Flag;

    const PAGE_BITS: usize = 12;

    const PC: Self::GpReg = GpReg::Rip;
    const ZERO: Self::GpReg = GpReg::Riz;
    const INSTRUCTION_ALIGNMENT: usize = 1;

    #[inline]
    fn reg(reg: Self::GpReg) -> Self::Reg {
        X64Reg::GpReg(reg)
    }

    #[inline]
    fn iter_regs() -> impl Iterator<Item = Self::Reg> {
        X64RegIterator {
            current: Some(X64Reg::GpReg(GpReg::Rax)),
        }
    }

    #[inline]
    fn iter_gpregs() -> impl Iterator<Item = Self::GpReg> {
        GpRegIterator {
            current: Some(GpReg::Rax),
        }
    }

    #[inline]
    fn flagreg_to_flags(reg: X64Reg, start_byte: usize, end_byte: usize) -> &'static [Self::Flag] {
        match reg {
            X64Reg::GpReg(reg) => {
                assert_eq!(reg, GpReg::RFlags);
                &[X64Flag::Cf, X64Flag::Pf, X64Flag::Af, X64Flag::Zf, X64Flag::Sf, X64Flag::Of][start_byte..=end_byte]
            },
            X64Reg::X87(X87Reg::ConditionCodes) => &[
                X64Flag::ConditionCode(0),
                X64Flag::ConditionCode(1),
                X64Flag::ConditionCode(2),
                X64Flag::ConditionCode(3),
            ][start_byte..=end_byte],
            X64Reg::X87(X87Reg::ExceptionFlags) => &[
                X64Flag::ExceptionFlag(0),
                X64Flag::ExceptionFlag(1),
                X64Flag::ExceptionFlag(2),
                X64Flag::ExceptionFlag(3),
                X64Flag::ExceptionFlag(4),
                X64Flag::ExceptionFlag(5),
            ][start_byte..=end_byte],
            X64Reg::Xmm(XmmReg::ExceptionFlags) => &[
                X64Flag::XmmExceptionFlag(0),
                X64Flag::XmmExceptionFlag(1),
                X64Flag::XmmExceptionFlag(2),
                X64Flag::XmmExceptionFlag(3),
                X64Flag::XmmExceptionFlag(4),
                X64Flag::XmmExceptionFlag(5),
            ][start_byte..=end_byte],
            X64Reg::Xmm(XmmReg::DenormalsAreZero) => &[X64Flag::DenormalsAreZero],
            _ => panic!("Not a flag: {reg:?}"),
        }
    }

    fn try_reg_to_gpreg(reg: <X64Arch as Arch>::Reg) -> Option<<X64Arch as Arch>::GpReg> {
        match reg {
            X64Reg::GpReg(gpreg) => Some(gpreg),
            _ => None,
        }
    }
}

const NUM_GPREGS: usize = 20;
const NUM_XMM_REGS: usize = 16;

// RFlags is only 6 bytes.
const GPREGS_SIZE: usize = NUM_GPREGS * 8 - 2;
const XMM_REG_SIZE: usize = NUM_XMM_REGS * 32;
const XMM_SIZE: usize = XMM_REG_SIZE + 7;
const X87_REG_SIZE: usize = 8 * 10;
const X87_SIZE: usize = X87_REG_SIZE + 12;

const ZERO_STATE: X64State = DEFAULT_X64_STATE;

macro_rules! field_range {
    ($($path:tt)*) => {{
        // Temporarily store it in a const to make sure it is always computed at compile time
        const RANGE: std::ops::Range<usize> = {
            let zero_state = &$crate::arch::x64::ZERO_STATE;
            let base = zero_state as *const _;

            // TODO: This is UB if field is accessed via Deref
            let field = &zero_state.$($path)* as *const _;

            let offset = unsafe {
                (field as *const u8).offset_from(base as *const u8) as usize
            };
            let size = std::mem::size_of_val(&zero_state.$($path)*);

            offset..offset + size
        };

        RANGE
    }};
}

#[inline(always)]
const fn crop(range: Range<usize>, max: usize) -> Range<usize> {
    if range.end > range.start + max {
        range.start..range.start + max
    } else {
        range
    }
}

/// A bitmask type that covers the entire StateByte range for the [`X64State`].
#[derive(Clone)]
pub struct DiffMask([u32; 800 / 32]);

impl Default for DiffMask {
    #[inline]
    fn default() -> Self {
        Self([0; 800 / 32])
    }
}

impl Debug for DiffMask {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();

        for i in 0..self.0.len() * 32 {
            if self.0[i / 32] & (1 << (i % 32)) != 0 {
                list.entry(&i);
            }
        }

        list.finish()
    }
}

#[inline(always)]
fn translate_raw_offset_to_state_byte(b: usize) -> Option<usize> {
    #[inline(always)]
    fn translate(index: usize, range: Range<usize>, offset: usize) -> Option<usize> {
        if index < range.end {
            index.checked_sub(range.start).map(|base| base + offset)
        } else {
            None
        }
    }

    translate(b, crop(field_range!(regs), 158), 0)
        .or_else(|| translate(b, field_range!(xmm.regs), GPREGS_SIZE))
        .or_else(|| translate(b, field_range!(x87.fpr), GPREGS_SIZE + XMM_SIZE))
        .or_else(|| translate(b, crop(field_range!(xmm_exception_flags), 6), GPREGS_SIZE + XMM_REG_SIZE))
        .or_else(|| translate(b, field_range!(xmm_daz), GPREGS_SIZE + XMM_REG_SIZE + 6))
        .or_else(|| translate(b, crop(field_range!(x87.exception_flags), 6), GPREGS_SIZE + XMM_SIZE + 80))
        .or_else(|| translate(b, field_range!(x87.condition_codes), GPREGS_SIZE + XMM_SIZE + 86))
        .or_else(|| translate(b, field_range!(x87.tag_word), GPREGS_SIZE + XMM_SIZE + 90))
        .or_else(|| translate(b, field_range!(x87.top_of_stack), GPREGS_SIZE + XMM_SIZE + 91))
}

#[inline(always)]
fn translate_state_byte_to_raw_offset(b: usize) -> Option<usize> {
    #[inline(always)]
    fn translate(index: usize, range: Range<usize>, offset: usize) -> Option<usize> {
        index.checked_sub(offset).and_then(|n| {
            if n < range.end - range.start {
                Some(n + range.start)
            } else {
                None
            }
        })
    }

    translate(b, crop(field_range!(regs), 158), 0)
        .or_else(|| translate(b, field_range!(xmm.regs), GPREGS_SIZE))
        .or_else(|| translate(b, field_range!(x87.fpr), GPREGS_SIZE + XMM_SIZE))
        .or_else(|| translate(b, crop(field_range!(xmm_exception_flags), 6), GPREGS_SIZE + XMM_REG_SIZE))
        .or_else(|| translate(b, field_range!(xmm_daz), GPREGS_SIZE + XMM_REG_SIZE + 6))
        .or_else(|| translate(b, crop(field_range!(x87.exception_flags), 6), GPREGS_SIZE + XMM_SIZE + 80))
        .or_else(|| translate(b, field_range!(x87.condition_codes), GPREGS_SIZE + XMM_SIZE + 86))
        .or_else(|| translate(b, field_range!(x87.tag_word), GPREGS_SIZE + XMM_SIZE + 90))
        .or_else(|| translate(b, field_range!(x87.top_of_stack), GPREGS_SIZE + XMM_SIZE + 91))
}

/// A struct that enforces alignment to 32-byte boundaries.
#[repr(align(32))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct Align32<T>(pub T);

impl<T> Deref for Align32<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Align32<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// x86-64 XMM state.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Xmm {
    regs: Align32<[[u8; 32]; 16]>,
}

impl Index<usize> for Xmm {
    type Output = [u8; 32];

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.regs.0[index]
    }
}

impl IndexMut<usize> for Xmm {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.regs.0[index]
    }
}

impl Xmm {
    /// Iterates over all XMM register values.
    #[inline]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &[u8; 32]> + DoubleEndedIterator {
        self.regs.0.iter()
    }
}

/// x87 state.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct X87 {
    /// 80-bit floating-point registers
    pub fpr: [[u8; 10]; 8],

    /// status word
    pub top_of_stack: u8,

    /// exception flags (one flag per byte); Stack fault is excluded because it's impossible to set SF=1 without causing an exception directly afterwards.
    pub exception_flags: u64,

    /// condition codes (one condition code per byte)
    pub condition_codes: u32,

    /// tag word
    pub tag_word: u8,
}

/// x87 registers available in the x87 state.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum X87Reg {
    /// The 80-bit floating-point registers.
    Fpr(u8),

    /// Lower 7 bits of FSW split into separate bytes (byte N is 1 if bit N of the original value is 1)
    ExceptionFlags,

    /// Condition codes in FSW split into separate bytes (byte N is 1 if condition code N is 1)
    ConditionCodes,

    /// The floating point stack tag word
    TagWord,

    /// Top-of-stack pointer in FSW (3 bits)
    TopOfStack,
}

impl Display for X87Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            X87Reg::Fpr(index) => write!(f, "mm{index}"),
            X87Reg::ExceptionFlags => write!(f, "EF"),
            X87Reg::ConditionCodes => write!(f, "C"),
            X87Reg::TopOfStack => write!(f, "TOP"),
            X87Reg::TagWord => write!(f, "FTW"),
        }
    }
}

/// The CPU state of the x86-64 architecture.
#[repr(C, align(32))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct X64State {
    /// General purpose registers
    pub regs: Align32<[u64; NUM_GPREGS]>,

    /// XMM registers
    pub xmm: Xmm,

    /// X87 registers
    pub x87: X87,

    /// XMM exception flags.
    /// Defined as a separate field for better alignment.
    pub xmm_exception_flags: u64,

    /// XMM Denormals-are-zero flag.
    /// Defined as a separate field for better alignment.
    pub xmm_daz: u8,
}

const DEFAULT_X64_STATE: X64State = X64State {
    regs: Align32([0; NUM_GPREGS]),
    xmm: Xmm {
        regs: Align32([[0; 32]; 16]),
    },
    xmm_exception_flags: 0,
    xmm_daz: 0,
    x87: X87 {
        fpr: [[0; 10]; 8],
        top_of_stack: 0,
        exception_flags: 0,
        condition_codes: 0,
        tag_word: 0,
    },
};

impl Default for X64State {
    fn default() -> Self {
        DEFAULT_X64_STATE
    }
}

struct X87FloatCache {
    entries: Mutex<[([u8; 10], u32, String); 16]>,
    next_index: AtomicU32,
}

static X87_FLOAT_CACHE: X87FloatCache = X87FloatCache {
    entries: Mutex::new([
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
        ([0; 10], 0, String::new()),
    ]),
    next_index: AtomicU32::new(0),
};

impl X87FloatCache {
    pub fn get(&self, data: &[u8; 10]) -> String {
        let time = self.next_index.fetch_add(1, Ordering::SeqCst);
        let entries = &mut *self.entries.lock().unwrap();
        if let Some((_, last_use, found)) = entries.iter_mut().find(|(b, ..)| b == data) {
            *last_use = time;
            found.clone()
        } else {
            let nval = data.iter().rev().fold(0u128, |acc, val| (acc << 8) | *val as u128);
            let fval = X87DoubleExtended::from_bits(nval);
            let str = fval.to_string();

            let (stored_data, last_use, stored_str) =
                entries.iter_mut().min_by_key(|e| if e.1 < time { e.1 } else { 0 }).unwrap();
            *stored_data = *data;
            *last_use = time;
            stored_str.clone_from(&str);

            str
        }
    }
}

impl Display for X64State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f)?;
        for chunk in X64Arch::iter_gpregs().chunks(2).into_iter() {
            for reg in chunk {
                write!(
                    f,
                    "{:6} = 0x{:X}    ",
                    reg.to_string(),
                    CpuState::<X64Arch>::reg(self, X64Arch::reg(reg))
                )?;
            }

            writeln!(f)?;
        }

        for flag in X64Flag::iter() {
            write!(f, "{} = {}  ", flag, i32::from(CpuState::<X64Arch>::flag(self, flag)))?;
        }

        writeln!(f)?;

        let highest_xmm_set = self
            .xmm
            .iter()
            .enumerate()
            .rev()
            .find(|(_, v)| !v.iter().all(|&b| b == 0))
            .map(|(index, _)| index + 1);

        for index in 0..highest_xmm_set.unwrap_or(0) {
            let reg = X64Reg::Xmm(XmmReg::Reg(index as u8));
            writeln!(f, "{:6} = 0x{:X}", reg.to_string(), CpuState::<X64Arch>::reg(self, reg))?;
        }

        match highest_xmm_set {
            Some(16) => (),
            Some(index) => writeln!(f, "Xmm{index:02}..Xmm15 = 0x0")?,
            None => writeln!(f, "Xmm00..Xmm15 = 0x0")?,
        }

        for chunk in [XmmReg::ExceptionFlags, XmmReg::DenormalsAreZero]
            .into_iter()
            .chunks(2)
            .into_iter()
        {
            for reg in chunk {
                let arch_reg = X64Reg::Xmm(reg);
                write!(
                    f,
                    "{:6} = 0x{:X}    ",
                    arch_reg.to_string(),
                    CpuState::<X64Arch>::reg(self, arch_reg)
                )?;
            }

            writeln!(f)?;
        }

        writeln!(f)?;

        let highest_fpr_set = self
            .x87
            .fpr
            .iter()
            .enumerate()
            .rev()
            .find(|(_, v)| !v.iter().all(|&b| b == 0))
            .map(|(index, _)| index + 1);

        for index in 0..highest_fpr_set.unwrap_or(0) {
            let reg = X64Reg::X87(X87Reg::Fpr(index as u8));
            let val = CpuState::<X64Arch>::reg(self, reg);
            let s = X87_FLOAT_CACHE.get(val.unwrap_bytes().try_into().unwrap());

            writeln!(f, "{:6} = 0x{:X} ({})", reg.to_string(), val, s)?;
        }

        match highest_fpr_set {
            Some(8) => (),
            Some(index) => writeln!(f, "mm{index:02}..mm8 = 0x0")?,
            None => writeln!(f, "mm0..mm8 = 0x0")?,
        }

        for chunk in [X87Reg::ExceptionFlags, X87Reg::ConditionCodes, X87Reg::TagWord]
            .into_iter()
            .chunks(2)
            .into_iter()
        {
            for reg in chunk {
                let arch_reg = X64Reg::X87(reg);
                write!(
                    f,
                    "{:6} = 0x{:X}    ",
                    arch_reg.to_string(),
                    CpuState::<X64Arch>::reg(self, arch_reg)
                )?;
            }

            writeln!(f)?;
        }

        {
            let reg = X87Reg::TopOfStack;
            let arch_reg = X64Reg::X87(reg);
            write!(f, "{} = {} ", arch_reg, CpuState::<X64Arch>::reg(self, arch_reg).unwrap_num())?;
        }

        writeln!(f)?;

        Ok(())
    }
}

impl CpuState<X64Arch> for X64State {
    #[inline]
    fn reg(&self, reg: X64Reg) -> Value {
        match reg {
            X64Reg::GpReg(GpReg::Riz) => Value::Num(0),
            X64Reg::GpReg(reg) => Value::Num(self.regs[reg.as_num()]),
            X64Reg::Xmm(reg) => match reg {
                XmmReg::Reg(i) => Value::Bytes(&self.xmm[i as usize]),
                XmmReg::ExceptionFlags => Value::Num(self.xmm_exception_flags),
                XmmReg::DenormalsAreZero => Value::Num(self.xmm_daz as u64),
            },
            X64Reg::X87(reg) => match reg {
                X87Reg::Fpr(index) => Value::Bytes(&self.x87.fpr[index as usize]),
                X87Reg::ExceptionFlags => Value::Num(self.x87.exception_flags),
                X87Reg::ConditionCodes => Value::Num(self.x87.condition_codes as u64),
                X87Reg::TopOfStack => Value::Num(self.x87.top_of_stack as u64),
                X87Reg::TagWord => Value::Num(self.x87.tag_word as u64),
            },
        }
    }

    #[inline]
    fn modify_reg<F: FnOnce(MutValue)>(&mut self, reg: <X64Arch as Arch>::Reg, update: F) {
        match reg {
            X64Reg::GpReg(GpReg::Riz) => update(MutValue::Num(&mut 0)),
            X64Reg::GpReg(reg) => {
                update(MutValue::Num(&mut self.regs[reg.as_num()]));

                if let Some(mask) = Register::mask(&reg) {
                    debug_assert_eq!(
                        self.regs[reg.as_num()] & !mask,
                        0,
                        "For registers with masks, only bits in the mask can be set. New value: {:X}, mask: {:X}",
                        self.regs[reg.as_num()],
                        mask
                    );
                }
            },
            X64Reg::Xmm(reg) => match reg {
                XmmReg::Reg(i) => update(MutValue::Bytes(&mut self.xmm[i as usize])),
                XmmReg::ExceptionFlags => update(MutValue::Num(&mut self.xmm_exception_flags)),
                XmmReg::DenormalsAreZero => {
                    let mut v = self.xmm_daz as u64;
                    update(MutValue::Num(&mut v));
                    self.xmm_daz = v as _;
                },
            },
            X64Reg::X87(reg) => match reg {
                X87Reg::Fpr(index) => update(MutValue::Bytes(&mut self.x87.fpr[index as usize])),
                X87Reg::ExceptionFlags => update(MutValue::Num(&mut self.x87.exception_flags)),
                X87Reg::ConditionCodes => {
                    let mut v = self.x87.condition_codes as u64;
                    update(MutValue::Num(&mut v));
                    self.x87.condition_codes = v as _;
                },
                X87Reg::TopOfStack => {
                    let mut v = self.x87.top_of_stack as u64;
                    update(MutValue::Num(&mut v));
                    self.x87.top_of_stack = v as _;
                },
                X87Reg::TagWord => {
                    let mut v = self.x87.tag_word as u64;
                    update(MutValue::Num(&mut v));
                    self.x87.tag_word = v as _;
                },
            },
        }
    }

    #[inline]
    fn gpreg(&self, reg: GpReg) -> u64 {
        match reg {
            GpReg::Riz => 0,
            other => self.regs[other.as_num()],
        }
    }

    #[inline(always)]
    fn set_gpreg(&mut self, reg: GpReg, value: u64) {
        match reg {
            GpReg::Riz => {
                if value != 0 {
                    panic!("Cannot set RIZ to anything but 0")
                }
            },
            reg => {
                #[cfg(debug_assertions)]
                if let Some(mask) = Register::mask(&reg) {
                    debug_assert_eq!(
                        self.regs[reg.as_num()] & !mask,
                        0,
                        "For registers with masks, only bits in the mask can be set"
                    );
                }

                self.regs[reg.as_num()] = value;
            },
        }
    }

    #[inline]
    fn flag(&self, flag: X64Flag) -> bool {
        let (reg, offset) = translate_flag(flag);

        let mask = 1 << (offset * 8);
        let old_val = CpuState::<X64Arch>::reg(self, reg);

        old_val.unwrap_num() & mask != 0
    }

    #[inline]
    fn set_flag(&mut self, flag: X64Flag, value: bool) {
        let (reg, offset) = translate_flag(flag);

        let mask = 1 << (offset * 8);

        CpuState::<X64Arch>::modify_reg(self, reg, |old_val| match old_val {
            MutValue::Num(n) => *n = if value { *n | mask } else { *n & !mask },
            MutValue::Bytes(_) => unreachable!(),
        });
    }

    type DiffMask = DiffMask;

    fn size() -> usize {
        GPREGS_SIZE + XMM_SIZE + X87_SIZE
    }

    fn state_byte_to_reg(byte: StateByte) -> (<X64Arch as Arch>::Reg, usize) {
        debug_assert!(byte.as_usize() < Self::size());

        if let Some(n) = byte.as_usize().checked_sub(GPREGS_SIZE) {
            if let Some(n) = n.checked_sub(XMM_SIZE) {
                if let Some(n) = n.checked_sub(X87_REG_SIZE) {
                    match n {
                        0..=5 => (X64Reg::X87(X87Reg::ExceptionFlags), n),
                        6..=9 => (X64Reg::X87(X87Reg::ConditionCodes), n - 6),
                        10 => (X64Reg::X87(X87Reg::TagWord), 0),
                        11 => (X64Reg::X87(X87Reg::TopOfStack), 0),
                        _ => unreachable!(),
                    }
                } else {
                    (X64Reg::X87(X87Reg::Fpr((n / 10) as u8)), n % 10)
                }
            } else if let Some(n) = n.checked_sub(XMM_REG_SIZE) {
                match n {
                    0..=5 => (X64Reg::Xmm(XmmReg::ExceptionFlags), n),
                    6 => (X64Reg::Xmm(XmmReg::DenormalsAreZero), 0),
                    _ => unreachable!(),
                }
            } else {
                (X64Reg::Xmm(XmmReg::Reg((n / 32) as u8)), n % 32)
            }
        } else {
            (X64Reg::GpReg(GpReg::from_num(byte.as_usize() / 8)), byte.as_usize() % 8)
        }
    }

    fn reg_to_state_byte(reg: <X64Arch as Arch>::Reg, byte: usize) -> StateByte {
        debug_assert!(reg != X64Reg::GpReg(GpReg::Riz));
        debug_assert!(byte < Register::byte_size(&reg));
        match reg {
            X64Reg::GpReg(reg) => StateByte::new(reg.as_num() * 8 + byte),
            X64Reg::Xmm(reg) => StateByte::new(
                GPREGS_SIZE
                    + match reg {
                        XmmReg::Reg(i) => i as usize * 32 + byte,
                        XmmReg::ExceptionFlags => XMM_REG_SIZE + byte,
                        XmmReg::DenormalsAreZero => XMM_REG_SIZE + 6,
                    },
            ),
            X64Reg::X87(reg) => StateByte::new(
                GPREGS_SIZE
                    + XMM_SIZE
                    + match reg {
                        X87Reg::Fpr(i) => i as usize * 10 + byte,
                        X87Reg::ExceptionFlags => 80 + byte,
                        X87Reg::ConditionCodes => 86 + byte,
                        X87Reg::TagWord => 90 + byte,
                        X87Reg::TopOfStack => 91 + byte,
                    },
            ),
        }
    }

    fn find_differences<F: FnMut(StateByte)>(&self, other: &Self, found: &mut F) {
        #[cfg(not(target_arch = "x86_64"))]
        {
            for b in (0..Self::size()).map(StateByte::new) {
                if self.get_state_byte(b) != other.get_state_byte(b) {
                    found(b);
                }
            }
        }

        #[cfg(target_arch = "x86_64")]
        {
            const SIZE: usize = size_of::<X64State>();

            let left_ptr = self as *const _ as *const __m256i;
            let right_ptr = other as *const _ as *const __m256i;

            let mut max_index = 0;
            let mut results = [0u32; SIZE / 32];
            for (index, result) in results.iter_mut().enumerate() {
                unsafe {
                    let left = _mm256_load_si256(left_ptr.add(index));
                    let right = _mm256_load_si256(right_ptr.add(index));

                    let compared = _mm256_cmpeq_epi8(left, right);
                    let n = _mm256_movemask_epi8(compared) as u32;

                    if n != 0xffff_ffff {
                        max_index = index;
                    }

                    *result = n;
                }
            }

            for (index, n) in results.into_iter().enumerate().take(max_index + 1) {
                let mut byte_index = index * 32;
                let mut n = (!n) as u64;
                while n != 0 {
                    let index = n.trailing_zeros() as usize;
                    byte_index += index;

                    if let Some(b) = translate_raw_offset_to_state_byte(byte_index) {
                        found(StateByte::new(b));
                    }

                    n >>= index + 1;
                    byte_index += 1;
                }
            }
        }
    }

    fn create_diff_mask<I: Iterator<Item = StateByte>>(items: I) -> Self::DiffMask {
        let mut m = DiffMask::default();
        for item in items {
            if let Some(index) = translate_state_byte_to_raw_offset(item.as_usize()) {
                m.0[index / 32] |= 1 << (index % 32);
            } else {
                panic!("State byte {item:?} does not have a translated offset");
            }
        }

        m
    }

    fn get_state_byte(&self, byte: StateByte) -> u8 {
        debug_assert!(byte.as_usize() < Self::size());

        let offset = translate_state_byte_to_raw_offset(byte.as_usize()).expect("Translation is broken");

        // SAFETY: Assuming translation is correctly implemented, this always accesses a byte in the struct.
        unsafe { *(self as *const _ as *const u8).add(offset) }
    }

    fn set_state_byte(&mut self, byte: StateByte, value: u8) {
        debug_assert!(byte.as_usize() < Self::size());

        let offset = translate_state_byte_to_raw_offset(byte.as_usize()).expect("Translation is broken");

        // SAFETY: Assuming translation is correctly implemented, this always accesses a byte in the struct.
        unsafe {
            *(self as *mut _ as *mut u8).add(offset) = value;
        }

        #[cfg(debug_assertions)]
        {
            let (reg, _) = Self::state_byte_to_reg(byte);
            let mask = Register::mask(&reg).unwrap_or(u64::MAX);
            if let Value::Num(v) = self.reg(reg) {
                debug_assert_eq!(
                    v & !mask,
                    0,
                    "Mask must be respected. Setting {reg:?} to value {v:X?} is not possible"
                );
            }
        }
    }

    fn state_bytes_unequal(&self, dest: StateByte, other: &Self) -> bool {
        debug_assert!(dest.as_usize() < Self::size());

        let offset = translate_state_byte_to_raw_offset(dest.as_usize()).expect("Translation is broken");

        // SAFETY: Assuming translation is correctly implemented, this always accesses a byte in the struct.
        unsafe { *(self as *const _ as *const u8).add(offset) != *(other as *const _ as *const u8).add(offset) }
    }

    fn find_dataflows_masked<F: FnMut(StateByte)>(
        b: SystemStateIoPair<X64Arch>, a: SystemStateIoPair<X64Arch>, dest_diff_mask: &Self::DiffMask,
        diff_mask: &Self::DiffMask, found: &mut F,
    ) {
        #[cfg(not(target_arch = "x86_64"))]
        panic!("find_dataflows_masked is only supported on x86_64");

        #[cfg(target_arch = "x86_64")]
        {
            const SIZE: usize = size_of::<X64State>();

            let b_in_ptr = b.state_in.cpu() as *const _ as *const __m256i;
            let b_out_ptr = b.state_out.cpu() as *const _ as *const __m256i;
            let a_in_ptr = a.state_in.cpu() as *const _ as *const __m256i;
            let a_out_ptr = a.state_out.cpu() as *const _ as *const __m256i;

            let mut max_index = 0;
            let mut results = [0u32; SIZE / 32];
            for (index, (result, (mask, dest_mask))) in results
                .iter_mut()
                .zip(diff_mask.0.iter().zip(dest_diff_mask.0.iter()))
                .enumerate()
            {
                unsafe {
                    let b_in = _mm256_load_si256(b_in_ptr.add(index));
                    let b_out = _mm256_load_si256(b_out_ptr.add(index));

                    let a_in = _mm256_load_si256(a_in_ptr.add(index));
                    let a_out = _mm256_load_si256(a_out_ptr.add(index));

                    let b_compared = _mm256_cmpeq_epi8(b_in, b_out);
                    let a_compared = _mm256_cmpeq_epi8(a_in, a_out);
                    let n = _mm256_movemask_epi8(a_compared) as u32 & _mm256_movemask_epi8(b_compared) as u32;
                    let n = n | mask;

                    let n = if n != 0xffff_ffff {
                        let compared = _mm256_cmpeq_epi8(a_out, b_out);
                        let k = _mm256_movemask_epi8(compared) as u32;

                        // if n is 0, then k or dest_mask must also be 0
                        let n = n | (k & dest_mask);

                        if n != 0xffff_ffff {
                            max_index = index;
                        }

                        n
                    } else {
                        0xffff_ffff
                    };

                    *result = n;
                }
            }

            for (index, n) in results.into_iter().enumerate().take(max_index + 1) {
                let mut byte_index = index * 32;
                let mut n = (!n) as u64;
                while n != 0 {
                    let index = n.trailing_zeros() as usize;
                    byte_index += index;

                    if let Some(b) = translate_raw_offset_to_state_byte(byte_index) {
                        found(StateByte::new(b));
                    }

                    n >>= index + 1;
                    byte_index += 1;
                }
            }
        }
    }
}

fn translate_flag(flag: X64Flag) -> (X64Reg, i32) {
    let (reg, offset) = match flag {
        X64Flag::Cf => (X64Reg::GpReg(GpReg::RFlags), 0),
        X64Flag::Pf => (X64Reg::GpReg(GpReg::RFlags), 1),
        X64Flag::Af => (X64Reg::GpReg(GpReg::RFlags), 2),
        X64Flag::Zf => (X64Reg::GpReg(GpReg::RFlags), 3),
        X64Flag::Sf => (X64Reg::GpReg(GpReg::RFlags), 4),
        X64Flag::Of => (X64Reg::GpReg(GpReg::RFlags), 5),
        X64Flag::ExceptionFlag(n) => (X64Reg::X87(X87Reg::ExceptionFlags), n as _),
        X64Flag::ConditionCode(n) => (X64Reg::X87(X87Reg::ConditionCodes), n as _),
        X64Flag::DenormalsAreZero => (X64Reg::Xmm(XmmReg::DenormalsAreZero), 0),
        X64Flag::XmmExceptionFlag(n) => (X64Reg::Xmm(XmmReg::ExceptionFlags), n as _),
    };
    (reg, offset)
}

/// The general-purpose registers in the x86-64 state.
#[allow(missing_docs)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum GpReg {
    Rax,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    Rip,
    Rbp,
    Rbx,
    Rsp,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,

    FsBase,
    GsBase,

    RFlags,
    Riz,
}

/// The XMM registers in the x86-64 state.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum XmmReg {
    /// 256-bit floating-point registers.
    Reg(u8),

    /// XMM exception flags
    ExceptionFlags,

    /// XMM DAZ flag
    DenormalsAreZero,
}

/// All registers in the x86-64 state.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum X64Reg {
    /// General-purpose register
    GpReg(GpReg),

    /// XMM register
    Xmm(XmmReg),

    /// X87 register
    X87(X87Reg),
}

impl Display for GpReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GpReg::Rax => write!(f, "RAX"),
            GpReg::Rcx => write!(f, "RCX"),
            GpReg::Rdx => write!(f, "RDX"),
            GpReg::Rsi => write!(f, "RSI"),
            GpReg::Rdi => write!(f, "RDI"),
            GpReg::Rip => write!(f, "RIP"),
            GpReg::Rbp => write!(f, "RBP"),
            GpReg::Rbx => write!(f, "RBX"),
            GpReg::Rsp => write!(f, "RSP"),
            GpReg::R8 => write!(f, "R8"),
            GpReg::R9 => write!(f, "R9"),
            GpReg::R10 => write!(f, "R10"),
            GpReg::R11 => write!(f, "R11"),
            GpReg::R12 => write!(f, "R12"),
            GpReg::R13 => write!(f, "R13"),
            GpReg::R14 => write!(f, "R14"),
            GpReg::R15 => write!(f, "R15"),
            GpReg::Riz => write!(f, "RIZ"),
            GpReg::RFlags => write!(f, "RFLAGS"),
            GpReg::FsBase => write!(f, "FS"),
            GpReg::GsBase => write!(f, "GS"),
        }
    }
}

impl Display for X64Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            X64Reg::GpReg(reg) => write!(f, "{reg}"),
            X64Reg::Xmm(reg) => write!(f, "{reg}"),
            X64Reg::X87(reg) => write!(f, "{reg}"),
        }
    }
}

impl Display for XmmReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            XmmReg::Reg(i) => write!(f, "Xmm{i:02}"),
            XmmReg::ExceptionFlags => write!(f, "XEF"),
            XmmReg::DenormalsAreZero => write!(f, "DAZ"),
        }
    }
}

impl Register for GpReg {
    #[inline]
    fn is_pc(&self) -> bool {
        self == &GpReg::Rip
    }

    #[inline]
    fn is_flags(&self) -> bool {
        self == &GpReg::RFlags
    }

    #[inline]
    fn mask(&self) -> Option<u64> {
        match self {
            GpReg::RFlags => Some(0x0101_0101_0101),
            _ => None,
        }
    }

    #[inline]
    fn should_avoid(&self) -> bool {
        // Some extra knowledge about X86:
        // | reg | encoding |
        // |-----|----------|
        // | rax | 0000     |
        // | rcx | 0001     |
        // | rsp | 0100     |
        // | rbp | 0101     |
        // | rsi | 0110     |
        // |  r8 | 1000     |
        // |  r9 | 1001     |
        // | r12 | 1100     |
        // | r13 | 1101     |
        // | r14 | 1110     |
        //
        // 100 000 110 101
        //
        // These are all one bit flip away from 0100 or 0101, which sometimes has a double meaning.
        // See ModR/M in the x86 reference manuals for details.
        // For normal inputs, it's better to pick a register that never has a double meaning.
        // Note that libLISA is still free to ignore this advice if it thinks it knows better.
        // Riz is special and can't be modified, making it a bad default register choice.
        matches!(
            self,
            GpReg::Rsp
                | GpReg::Rbp
                | GpReg::Rax
                | GpReg::Rcx
                | GpReg::Rsi
                | GpReg::R8
                | GpReg::R9
                | GpReg::R12
                | GpReg::R13
                | GpReg::R14
                | GpReg::Riz
        )
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self == &GpReg::Riz
    }

    #[inline]
    fn byte_size(&self) -> usize {
        match self {
            GpReg::RFlags => 6,
            _ => 8,
        }
    }

    #[inline]
    fn is_addr_reg(&self) -> bool {
        matches!(self, GpReg::FsBase | GpReg::GsBase)
    }

    fn reg_type(self) -> ValueType {
        ValueType::Num
    }
}

impl NumberedRegister for GpReg {
    #[inline]
    fn as_num(&self) -> usize {
        match self {
            GpReg::Rax => 0,
            GpReg::Rcx => 1,
            GpReg::Rdx => 2,
            GpReg::Rsi => 3,
            GpReg::Rdi => 4,
            GpReg::Rip => 5,
            GpReg::Rbp => 6,
            GpReg::Rbx => 7,
            GpReg::Rsp => 8,
            GpReg::R8 => 9,
            GpReg::R9 => 10,
            GpReg::R10 => 11,
            GpReg::R11 => 12,
            GpReg::R12 => 13,
            GpReg::R13 => 14,
            GpReg::R14 => 15,
            GpReg::R15 => 16,
            GpReg::FsBase => 17,
            GpReg::GsBase => 18,
            GpReg::RFlags => 19,
            GpReg::Riz => unreachable!(),
        }
    }

    #[inline]
    fn from_num(num: usize) -> Self {
        match num {
            0 => GpReg::Rax,
            1 => GpReg::Rcx,
            2 => GpReg::Rdx,
            3 => GpReg::Rsi,
            4 => GpReg::Rdi,
            5 => GpReg::Rip,
            6 => GpReg::Rbp,
            7 => GpReg::Rbx,
            8 => GpReg::Rsp,
            9 => GpReg::R8,
            10 => GpReg::R9,
            11 => GpReg::R10,
            12 => GpReg::R11,
            13 => GpReg::R12,
            14 => GpReg::R13,
            15 => GpReg::R14,
            16 => GpReg::R15,
            17 => GpReg::FsBase,
            18 => GpReg::GsBase,
            19 => GpReg::RFlags,
            usize::MAX => GpReg::Riz,
            _ => panic!("{num} is not a valid register index"),
        }
    }
}

impl Register for X64Reg {
    #[inline]
    fn is_pc(&self) -> bool {
        match self {
            X64Reg::GpReg(reg) => reg.is_pc(),
            _ => false,
        }
    }

    #[inline]
    fn is_flags(&self) -> bool {
        match self {
            X64Reg::GpReg(reg) => reg.is_flags(),
            X64Reg::X87(X87Reg::ConditionCodes | X87Reg::ExceptionFlags) => true,
            X64Reg::Xmm(XmmReg::ExceptionFlags | XmmReg::DenormalsAreZero) => true,
            _ => false,
        }
    }

    #[inline]
    fn mask(&self) -> Option<u64> {
        match self {
            X64Reg::GpReg(reg) => reg.mask(),
            X64Reg::X87(X87Reg::ExceptionFlags) => Some(0x0101_0101_0101),
            X64Reg::X87(X87Reg::ConditionCodes) => Some(0x0101_0101),
            X64Reg::X87(X87Reg::TopOfStack) => Some(0b111),
            X64Reg::Xmm(XmmReg::ExceptionFlags) => Some(0x0101_0101_0101),
            X64Reg::Xmm(XmmReg::DenormalsAreZero) => Some(1),
            _ => None,
        }
    }

    #[inline]
    fn should_avoid(&self) -> bool {
        match self {
            X64Reg::GpReg(reg) => reg.should_avoid(),
            _ => false,
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        match self {
            X64Reg::GpReg(reg) => reg.is_zero(),
            _ => false,
        }
    }

    #[inline]
    fn byte_size(&self) -> usize {
        match self {
            X64Reg::GpReg(reg) => reg.byte_size(),
            X64Reg::Xmm(reg) => match reg {
                XmmReg::Reg(_) => 32,
                XmmReg::ExceptionFlags => 6,
                XmmReg::DenormalsAreZero => 1,
            },
            X64Reg::X87(reg) => match reg {
                X87Reg::Fpr(_) => 10,
                X87Reg::ExceptionFlags => 6,
                X87Reg::ConditionCodes => 4,
                X87Reg::TopOfStack => 1,
                X87Reg::TagWord => 1,
            },
        }
    }

    #[inline]
    fn is_addr_reg(&self) -> bool {
        match self {
            X64Reg::GpReg(r) => r.is_addr_reg(),
            X64Reg::Xmm(_) => false,
            X64Reg::X87(_) => false,
        }
    }

    #[inline]
    fn reg_type(self) -> ValueType {
        match self {
            X64Reg::GpReg(r) => r.reg_type(),
            X64Reg::Xmm(XmmReg::ExceptionFlags | XmmReg::DenormalsAreZero) => ValueType::Num,
            X64Reg::Xmm(_) => ValueType::Bytes(Register::byte_size(&self)),
            X64Reg::X87(reg) => {
                if matches!(reg, X87Reg::Fpr(_)) {
                    ValueType::Bytes(Register::byte_size(&self))
                } else {
                    ValueType::Num
                }
            },
        }
    }
}
struct GpRegIterator {
    current: Option<GpReg>,
}

#[inline]
fn next_gpreg(reg: GpReg) -> Option<GpReg> {
    use GpReg::*;
    Some(match reg {
        Rax => Rcx,
        Rcx => Rdx,
        Rdx => Rsi,
        Rsi => Rdi,
        Rdi => Rip,
        Rip => Rbp,
        Rbp => Rbx,
        Rbx => Rsp,
        Rsp => R8,
        R8 => R9,
        R9 => R10,
        R10 => R11,
        R11 => R12,
        R12 => R13,
        R13 => R14,
        R14 => R15,
        R15 => FsBase,
        FsBase => GsBase,
        GsBase => RFlags,
        RFlags => return None,
        Riz => return None,
    })
}

impl Iterator for GpRegIterator {
    type Item = GpReg;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current;
        if let Some(val) = result {
            self.current = next_gpreg(val);
        }

        result
    }
}

struct X64RegIterator {
    current: Option<X64Reg>,
}

impl Iterator for X64RegIterator {
    type Item = X64Reg;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current;
        if let Some(val) = result {
            self.current = (|| {
                Some(match val {
                    X64Reg::GpReg(reg) => {
                        if let Some(next) = next_gpreg(reg) {
                            X64Reg::GpReg(next)
                        } else {
                            X64Reg::Xmm(XmmReg::Reg(0))
                        }
                    },
                    X64Reg::Xmm(XmmReg::Reg(15)) => X64Reg::Xmm(XmmReg::ExceptionFlags),
                    X64Reg::Xmm(XmmReg::Reg(i)) => X64Reg::Xmm(XmmReg::Reg(i + 1)),
                    X64Reg::Xmm(XmmReg::ExceptionFlags) => X64Reg::Xmm(XmmReg::DenormalsAreZero),
                    X64Reg::Xmm(XmmReg::DenormalsAreZero) => X64Reg::X87(X87Reg::Fpr(0)),
                    X64Reg::X87(reg) => X64Reg::X87(match reg {
                        X87Reg::Fpr(7) => X87Reg::ExceptionFlags,
                        X87Reg::Fpr(n) => X87Reg::Fpr(n + 1),
                        X87Reg::ExceptionFlags => X87Reg::ConditionCodes,
                        X87Reg::ConditionCodes => X87Reg::TopOfStack,
                        X87Reg::TopOfStack => X87Reg::TagWord,
                        X87Reg::TagWord => return None,
                    }),
                })
            })();
        }

        result
    }
}

/// All flags in the x86-64 state (including MMX/XMM flags).
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum X64Flag {
    /// RFLAGS - carry flag
    Cf,

    /// RFLAGS - parity flag
    Pf,

    /// RFLAGS - affinity flag
    Af,

    /// RFLAGS - zero flag
    Zf,

    /// RFLAGS - sign flag
    Sf,

    /// RFLAGS - overflow flag
    Of,

    /// MMX exception flag
    ExceptionFlag(u8),

    /// MMX condition code
    ConditionCode(u8),

    /// XMM DAZ flag
    DenormalsAreZero,

    /// XMM exception flag
    XmmExceptionFlag(u8),
}

impl Display for X64Flag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            X64Flag::Cf => write!(f, "CF"),
            X64Flag::Pf => write!(f, "PF"),
            X64Flag::Af => write!(f, "AF"),
            X64Flag::Zf => write!(f, "ZF"),
            X64Flag::Sf => write!(f, "SF"),
            X64Flag::Of => write!(f, "OF"),
            X64Flag::ExceptionFlag(n) => write!(f, "EF{n}"),
            X64Flag::ConditionCode(n) => write!(f, "CC{n}"),
            X64Flag::DenormalsAreZero => write!(f, "DAZ"),
            X64Flag::XmmExceptionFlag(n) => write!(f, "XEF{n}"),
        }
    }
}

impl Flag for X64Flag {
    fn iter() -> impl Iterator<Item = Self> {
        X64FlagIterator {
            current: Some(X64Flag::Cf),
        }
    }
}

struct X64FlagIterator {
    current: Option<X64Flag>,
}

impl Iterator for X64FlagIterator {
    type Item = X64Flag;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current;
        if let Some(val) = result {
            use X64Flag::*;
            self.current = match val {
                Cf => Some(Pf),
                Pf => Some(Af),
                Af => Some(Zf),
                Zf => Some(Sf),
                Sf => Some(Of),
                Of => Some(ExceptionFlag(0)),
                ExceptionFlag(n) => Some(if n < 5 { ExceptionFlag(n + 1) } else { ConditionCode(0) }),
                ConditionCode(n) => Some(if n < 3 { ConditionCode(n + 1) } else { DenormalsAreZero }),
                DenormalsAreZero => Some(XmmExceptionFlag(0)),
                XmmExceptionFlag(n) => {
                    if n < 5 {
                        Some(XmmExceptionFlag(n + 1))
                    } else {
                        None
                    }
                },
            };
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use memoffset::offset_of;
    use rand::Rng;

    use super::{
        crop, translate_raw_offset_to_state_byte, translate_state_byte_to_raw_offset, CpuState, Flag, X64Arch, X64Flag, X64State,
    };
    use crate::arch::{Arch, Register};
    use crate::encoding::dataflows::MemoryAccesses;
    use crate::instr::Instruction;
    use crate::state::{StateByte, SystemState, SystemStateByteView, SystemStateByteViewReg};
    use crate::value::Value;

    #[test]
    pub fn state_layout() {
        let size = size_of::<X64State>();
        println!("X64State's size: {size}");

        println!("field_range!(regs),  = {:?}", field_range!(regs));
        println!("field_range!(xmm.regs) = {:?}", field_range!(xmm.regs));
        println!(
            "crop(field_range!(xmm_exception_flags) = {:?}",
            crop(field_range!(xmm_exception_flags), 6)
        );
        println!("field_range!(xmm_daz),  = {:?}", field_range!(xmm_daz));
        println!("field_range!(x87.fpr) = {:?}", field_range!(x87.fpr));
        println!(
            "crop(field_range!(x87.exception_flags) = {:?}",
            crop(field_range!(x87.exception_flags), 7)
        );
        println!("field_range!(x87.condition_codes) = {:?}", field_range!(x87.condition_codes));
        println!("field_range!(x87.tag_word) = {:?}", field_range!(x87.tag_word));
        println!("field_range!(x87.top_of_stack) = {:?}", field_range!(x87.top_of_stack));

        assert!(
            size % 32 == 0,
            "X64State must have a size that is a multiple of 32, current size = {size}"
        );

        let regs = offset_of!(X64State, regs);
        let xmm = offset_of!(X64State, xmm);
        let x87 = offset_of!(X64State, x87);

        println!("regs={regs}, xmm={xmm}, x87={x87}");
    }

    #[test]
    pub fn get_set_flags() {
        let mut s = X64State::default();

        for f in X64Flag::iter() {
            CpuState::<X64Arch>::set_flag(&mut s, f, false);
            assert!(!CpuState::<X64Arch>::flag(&s, f));

            CpuState::<X64Arch>::set_flag(&mut s, f, true);
            assert!(CpuState::<X64Arch>::flag(&s, f));
        }
    }

    #[test]
    pub fn state_byte_match() {
        for n in (0..X64State::size()).map(StateByte::new) {
            let (reg, byte) = X64State::state_byte_to_reg(n);
            let again = X64State::reg_to_state_byte(reg, byte);

            assert_eq!(
                n, again,
                "Register {reg:?} byte index {byte:?} is not correctly mapped to a byte"
            );
        }
    }

    #[test]
    pub fn state_size_correct() {
        let state_size = X64State::size();
        for reg in X64Arch::iter_regs() {
            let size = reg.byte_size();
            let sb = X64State::reg_to_state_byte(reg, size - 1);

            assert!(
                sb.as_usize() < state_size,
                "{} does not fit in state size: {} < {} failed",
                reg,
                sb.as_usize(),
                state_size
            );
        }
    }

    #[test]
    pub fn find_difference_test() {
        // TODO: Test multiple differences (in the same 32-byte region)
        let state: SystemState<X64Arch> = SystemState::new_without_memory(X64State::default());
        let accesses = MemoryAccesses {
            instr: Instruction::new(&[0x00]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let view = SystemStateByteView::new(&accesses);
        let mut rng = rand::thread_rng();

        for b in (0..X64State::size()).map(StateByte::new) {
            println!("Checking: {:?}", X64State::state_byte_to_reg(b));
            for _ in 0..100_000 {
                let mut state2 = state.clone();
                let old = view.get(&state, b);
                let (reg, index) = X64State::state_byte_to_reg(b);
                let new = loop {
                    let mask = reg.mask().map(|mask| (mask >> (index * 8)) as u8).unwrap_or(u8::MAX);
                    assert!(mask != 0);
                    let v: u8 = rng.gen::<u8>() & mask;
                    if v != old {
                        break v;
                    }
                };

                let old_val = view.get_reg(&state, &SystemStateByteViewReg::Reg(reg));
                let mut tmp;
                let new_val = match old_val {
                    Value::Num(n) => Value::Num(n & !(0xff << (index * 8)) | (new as u64) << (index * 8)),
                    Value::Bytes(b) => {
                        tmp = b.to_vec();
                        tmp[index] = new;

                        Value::Bytes(&tmp)
                    },
                };
                view.set_reg(&mut state2, &SystemStateByteViewReg::Reg(reg), new_val);

                let mut found = false;
                view.find_differences(&state, &state2, &mut |c| {
                    assert_eq!(c, b);
                    found = true;
                });

                assert!(found);
            }
        }
    }

    #[test]
    pub fn translation_is_ok() {
        for b in 0..X64State::size() {
            let n = translate_state_byte_to_raw_offset(b).unwrap();
            let k = translate_raw_offset_to_state_byte(n).unwrap();

            assert!(n < std::mem::size_of::<X64State>());

            assert_eq!(b, k);
        }

        for n in 0..size_of::<X64State>() {
            println!("Testing {n}");
            if let Some(b) = translate_raw_offset_to_state_byte(n) {
                let k = translate_state_byte_to_raw_offset(b).unwrap();
                assert_eq!(
                    n, k,
                    "Offset {n} translates to state byte {b}, but that translates back to offset {k} instead of {n}"
                );
            }
        }
    }
}
