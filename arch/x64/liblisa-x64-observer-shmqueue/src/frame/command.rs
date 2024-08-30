//! Types representing the command frames.

use core::arch::asm;
use core::intrinsics::transmute;
use core::mem::size_of;

use static_assertions::const_assert_eq;

use crate::regs::{DebugRegs, GpRegs, RestoreError, XsaveHeader, XsaveLegacyArea};

/// The access permissions of a memory mapping.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Permissions {
    Executable = 0,
    Read = 1,
    ReadWrite = 2,
}

/// An efficient representation of a single memory mapping.
#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct MemoryMapping {
    packed_page_info: u64,
    frame_index: u16,
}

impl MemoryMapping {
    /// Ignores the lower 12 bits of page_start_addr.
    #[inline]
    pub fn new(page_start_addr: u64, frame_index: u32, permissions: Permissions) -> MemoryMapping {
        debug_assert!(frame_index <= u16::MAX as u32);
        let page = page_start_addr >> 12;

        MemoryMapping {
            packed_page_info: page | ((permissions as u64) << 52),
            frame_index: frame_index as u16,
        }
    }

    #[inline]
    pub const fn empty() -> MemoryMapping {
        MemoryMapping {
            packed_page_info: 0,
            frame_index: 0,
        }
    }

    #[inline]
    pub fn permissions(&self) -> Permissions {
        // SAFETY: As long as the host never writes incorrect permissions, the packed_page_info will always contain valid Permissions
        unsafe { transmute::<u8, Permissions>((self.packed_page_info >> 52) as u8) }
    }

    #[inline]
    pub fn page_start_addr(&self) -> u64 {
        self.packed_page_info << 12
    }

    #[inline]
    pub fn frame_index(&self) -> u32 {
        self.frame_index as u32
    }
}

#[repr(C)]
/// A structure that can contain up to 64 memory mappings.
/// ! **NOTE:** This is not an "absurd" amount of memory mappings for a single instruction.
/// The `enter` instruction can access up to 63 individual memory locations.
pub struct MemoryMappings([MemoryMapping; MemoryMappings::MAX_LEN], u8);

impl MemoryMappings {
    pub const MAX_LEN: usize = 64;

    #[inline]
    pub fn active(&self) -> &[MemoryMapping] {
        &self.0[..self.1 as usize]
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.1 as usize
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn recycle(&mut self, iter: impl Iterator<Item = MemoryMapping>) {
        let mut count = 0;
        for mapping in iter {
            self.0[count] = mapping;
            count += 1;
        }

        self.1 = count as u8;
    }
}

impl FromIterator<MemoryMapping> for MemoryMappings {
    #[inline]
    fn from_iter<T: IntoIterator<Item = MemoryMapping>>(iter: T) -> Self {
        let mut mappings = [MemoryMapping::empty(); 64];
        let mut count = 0;
        for mapping in iter {
            mappings[count] = mapping;
            count += 1;
        }

        MemoryMappings(mappings, count as u8)
    }
}

/// The command frame is structured such that important values will be nicely aligned.
/// The extended register data is at the front, which means it will be aligned on a page bound.
/// The GpRegs are aligned on a 1024-byte boundary.
/// Memory mappings and other configuration follow after that.
/// ! NOTE: Do not modify the field order without benchmarking! Ordering the fields incorrectly can easily cost ~5-10% performance.
#[repr(C, align(4096))]
pub struct CommandFrame {
    /// Data for the extended registers (3072 bytes)
    pub extended_regs: ExtendedRegs,

    /// The basic general-purpose registers (184 bytes)
    pub gpregs: GpRegs,

    /// The bitmask of extended registers that should be set (8 bytes)
    pub restore_extended_registers: u64,

    /// The bitmask of extended registers that should be copied back into extended_register_data (8 bytes)
    pub save_extended_registers: u64,

    /// The memory mappings (780 bytes)
    pub memory_mappings: MemoryMappings,

    /// The debugging registers DR0-DR3, DR6 & DR7 (48 bytes)
    pub debug_regs: DebugRegs,

    _padding: [u8; 128],
}

const_assert_eq!(size_of::<CommandFrame>(), 4096);
const_assert_eq!(size_of::<MemoryMapping>(), 10);

/// Provides access to all extended registers in the XSAVE area.
#[repr(C, align(64))]
pub struct ExtendedRegs([u8; 3072]);

impl ExtendedRegs {
    #[inline]
    pub fn new() -> Self {
        Self([0; 3072])
    }

    /// # Safety
    /// You must not read this struct while the ptr exists.
    #[inline]
    pub unsafe fn as_mut_ptr(&mut self) -> *mut u8 {
        self.0.as_mut_ptr()
    }

    #[inline]
    pub fn legacy_area(&self) -> &XsaveLegacyArea {
        unsafe { self.component(0) }
    }

    #[inline]
    pub fn header(&self) -> &XsaveHeader {
        unsafe { self.component(512) }
    }

    /// # Safety
    /// You must ensure that `self` lives longer than the reference returned by this function.
    /// You must ensure that you do not modify this component while the reference exists.
    #[inline]
    pub unsafe fn component<T>(&self, offset: usize) -> &T {
        &*(self.0.as_ptr().wrapping_add(offset) as *const T)
    }

    #[inline]
    pub fn legacy_area_mut(&mut self) -> &mut XsaveLegacyArea {
        unsafe { self.component_mut(0) }
    }

    #[inline]
    pub fn header_mut(&mut self) -> &mut XsaveHeader {
        unsafe { self.component_mut(512) }
    }

    /// # Safety
    /// You must ensure that `self` lives longer than the reference returned by this function.
    /// You must ensure that you do not obtain any other references to this component.
    #[inline]
    pub unsafe fn component_mut<T>(&mut self, offset: usize) -> &mut T {
        &mut *(self.0.as_mut_ptr().wrapping_add(offset) as *mut T)
    }

    /// XSAVE the current CPU state into the memory region.
    ///
    /// # Safety
    /// The memory region must be large enough to hold the entire CPU state.
    /// The required size depends on various control registers.
    #[inline]
    pub unsafe fn save_current(&mut self, component_bitmap: u64) {
        #[cfg(target_arch = "x86_64")]
        asm!(
            // We CANNOT use XSAVEOPT here because it has problematic behavior with instructions like C581D123 where it might/might not save at all if the state is in the initialization state.
            // If we want to use xsaveopt64 here, we probably need to check which parts were written and reset the parts that weren't written to their reset state.
            "xsave64 [{0}]",
            in(reg) self.0.as_mut_ptr(),

            // Save x86/mmx, sse and avx
            in("rax") component_bitmap as u32,
            in("rdx") (component_bitmap >> 32) as u32,
        );

        #[cfg(not(target_arch = "x86_64"))]
        panic!("save_current not supported on non-x86_64 architectures");
    }

    /// XRSTOR the CPU state from this save
    ///
    /// # Safety
    ///
    /// You must ensure that the components contain valid XSAVE data.
    /// You must ensure that `component_bitmap` is a valid component bitmap for the current CPU.
    #[inline]
    pub unsafe fn restore(&mut self, component_bitmap: u64) -> Result<(), RestoreError> {
        if self.legacy_area().mxcsr & 0xfffd_0000 != 0 {
            return Err(RestoreError::ReservedMxcsrFlagsSet);
        }

        #[cfg(target_arch = "x86_64")]
        asm!(
            "xrstor64 [{0}]",
            in(reg) self.0.as_mut_ptr(),

            // Save x86/mmx, sse and avx
            in("rax") component_bitmap as u32,
            in("rdx") (component_bitmap >> 32) as u32,
        );

        #[cfg(not(target_arch = "x86_64"))]
        panic!("restore not supported on non-x86_64 architectures");

        Ok(())
    }
}

impl Default for ExtendedRegs {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for CommandFrame {
    #[inline]
    fn default() -> Self {
        Self {
            extended_regs: ExtendedRegs([0; 3072]),
            gpregs: Default::default(),
            debug_regs: Default::default(),
            restore_extended_registers: 0,
            save_extended_registers: 0,
            memory_mappings: MemoryMappings([MemoryMapping::empty(); 64], 0),
            _padding: [0; 128],
        }
    }
}

impl CommandFrame {
    #[inline]
    pub fn new(gpregs: GpRegs, memory_mappings: impl Iterator<Item = MemoryMapping>) -> CommandFrame {
        Self {
            gpregs,
            restore_extended_registers: 0,
            memory_mappings: MemoryMappings::from_iter(memory_mappings),
            ..Default::default()
        }
    }
}
