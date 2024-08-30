//! Registers in the command frames.

use core::mem::size_of;

use static_assertions::const_assert;

/// The general-purpose registers.
#[repr(C)]
#[derive(Default, Copy, Debug, Clone, PartialEq, Eq)]
pub struct GpRegs {
    pub rax: u64,
    pub rbx: u64,
    pub rcx: u64,
    pub rdx: u64,

    pub rbp: u64,
    pub rsi: u64,
    pub rdi: u64,

    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,

    // Note that the ordering here is chosen so that memory is accessed linearly in userspace::handle_interrupt
    // Make sure to benchmark any changes you make to the order of the fields.
    pub exception_id: u64,
    pub error_code: u64,
    pub rip: u64,
    pub rsp: u64,
    pub access_address: u64,
    pub rflags: u64,

    pub fs_base: u64,
    pub gs_base: u64,
}

impl GpRegs {
    pub fn clear(&mut self) {
        *self = Default::default();
    }
}

/// The debug registers.
#[repr(C)]
#[derive(Default, Copy, Debug, Clone, PartialEq, Eq)]
pub struct DebugRegs {
    pub dr0: u64,
    pub dr1: u64,
    pub dr2: u64,
    pub dr3: u64,
    pub dr6: u64,
    pub dr7: u64,
}

/// Error returned by [`crate::frame::command::ExtendedRegs::restore`].
#[derive(Debug)]
pub enum RestoreError {
    /// Reserved flags in the MXCSR register (bit 16, 18-31) must be cleared.
    ReservedMxcsrFlagsSet,
}

/// A trait representing an XSAVE component.
pub trait XsaveComponent {}
impl XsaveComponent for YmmRegs {}
impl XsaveComponent for XsaveLegacyArea {}
impl XsaveComponent for XsaveHeader {}

/// The x87 ST(n) registers.
#[repr(C)]
#[derive(Copy, Clone, Default)]
pub struct St([u8; 10], [u8; 6]);

impl St {
    #[inline]
    pub fn new(bytes: [u8; 10]) -> Self {
        St(bytes, Default::default())
    }

    #[inline]
    pub fn bytes(&self) -> [u8; 10] {
        self.0
    }
}

impl core::fmt::Debug for St {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.0, f)
    }
}

const_assert!(size_of::<St>() == 16);

/// The XSAVE legacy area (which contains mostly x87).
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct XsaveLegacyArea {
    /// The fcw register (rounding mode, precision control, exception masking)
    pub control_word: u16,
    /// The fsw register
    pub status_word: u16,
    /// The ftw register
    pub tag_word: u8,
    pub _reserved1: u8,
    pub fop: u16,
    /// The last instruction pointer
    pub rip: u64,

    /// The last data pointer
    pub rdp: u64,
    pub mxcsr: u32,
    pub mxcsr_mask: u32,

    pub st: [St; 8],
    pub xmm: [u128; 16],
}

// TODO: Assert sizes and offsets of legacy area

impl Default for XsaveLegacyArea {
    fn default() -> Self {
        Self {
            control_word: 0x37F,
            status_word: 0x3800,
            tag_word: 0x80,
            _reserved1: 0x00,
            fop: 0,
            rip: 0,
            rdp: 0,
            mxcsr: 0x1f80,
            mxcsr_mask: 0x2ffff,
            st: Default::default(),
            xmm: [0; 16],
        }
    }
}

/// The XSAVE header.
#[repr(packed, C)]
#[derive(Copy, Clone, Debug)]
pub struct XsaveHeader {
    pub xstate_bv: u64,
    pub xcomp_bv: u64,
}

/// The AVX YMM registers.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct YmmRegs {
    pub ymm_hi128: [u128; 16],
}
