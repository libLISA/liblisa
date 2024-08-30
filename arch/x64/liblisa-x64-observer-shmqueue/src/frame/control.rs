//! Types representing the control frames.

use core::fmt::Debug;
use core::mem::size_of;
use core::ops::Range;
use core::sync::atomic::{AtomicU32, Ordering};

use memoffset::offset_of;
use static_assertions::const_assert;

/// Converts a pointer `*mut u32` into a pointer to an [`AtomicU32`].
///
/// # Safety
/// You must ensure the lifetime 'a is not greater than the time that you're borrowing ptr for.
pub unsafe fn make_atomic_u32<'a>(ptr: *mut u32) -> &'a AtomicU32 {
    // SAFETY: AtomicU32 is guaranteed to have the same in-memory representation as u32.
    &*(ptr as *const AtomicU32)
}

/// Represents the host of the VM.
#[derive(Copy, Clone, Debug, Default)]
pub struct Host;

/// Represents the VM client.
#[derive(Copy, Clone, Debug, Default)]
pub struct Client;

/// Information about the VM client.
#[repr(C)]
pub struct ClientInfo {
    pub reserved_start: u64,
    pub reserved_end: u64,
}

/// The data inside a control frame.
#[repr(C)]
pub struct ControlFrameData {
    /// The next empty command frame index.
    /// Must only be modified by the host.
    pub next: AtomicU32,
    _next_padding: [u8; 60],

    /// The command frame index that's currently being processed/waited on by the observer.
    /// Must only be modified by the client.
    /// The host may set this value to u32::MAX before starting the client.
    /// The client must initialise this value to 0.
    pub current: AtomicU32,
    _current_padding: [u8; 60],

    /// The number of command frames
    pub num_command_frames: u32,

    /// Next control frame (in case the observer is split)
    pub next_control_frame: u32,
    _info_padding: [u8; 56],

    /// The information about the client.
    pub client_info: ClientInfo,

    /// Layout of the XSAVE area.
    pub xsave_layout: Layout,
}

// ! WARNING: If you see an error here, the size of the control frame has changed.
// You should make sure offsets of fields in ControlFrameData are still correct.
// Run the tests to verify that the most important offsets are still correct.
// This structure is shared between the host (liblisa-x64-observer) and the client (vmimage-x86-64).
// Make sure to also recompile `vmimage-x86-64` if you have changed ControlFrameData.
// This *should* happen automatically via `build.rs`.
const_assert!(size_of::<ControlFrameData>() == 256);

/// SAFETY: `ptr` must point to a valid control frame, and the observer must have initialised.
/// Once the observer has initialised, only `next` and `current` in the control frame can be updated.
pub struct ControlFrame<'a, K> {
    data: &'a ControlFrameData,
    // /// The next empty command frame index.
    // next: &'a AtomicU32,

    // /// The command frame index that's currently being processed/waited on by the observer.
    // current: &'a AtomicU32,

    // // The rest of the data in the control frame.
    // rest: &'a [u8],
    _kind: K,
}

impl<'a, K> Debug for ControlFrame<'a, K> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ControlFrame")
            .field("next", &self.data.next.load(Ordering::Acquire))
            .field("current", &self.data.current.load(Ordering::Acquire))
            .field("num_control_frames", &self.data.num_command_frames)
            .finish()
    }
}

impl<'a, K: Default> ControlFrame<'a, K> {
    pub const NEXT_OFFSET: usize = offset_of!(ControlFrameData, next);
    pub const CURRENT_OFFSET: usize = offset_of!(ControlFrameData, current);
    pub const NUM_CONTROL_FRAMES_OFFSET: usize = offset_of!(ControlFrameData, num_command_frames);

    /// # Safety
    /// `ptr` must point to a control frame.
    /// Caller must ensure that the lifetime is correct.
    pub unsafe fn new(ptr: *mut u8) -> ControlFrame<'a, K> {
        // SAFETY: mem will live as long as `self` exists ('a). ControlFrame will live no longer than 'a.
        ControlFrame {
            data: &*(ptr as *const ControlFrameData),
            // next: make_atomic_u32(ptr.wrapping_add(Self::NEXT_OFFSET) as *mut u32),
            // current: make_atomic_u32(ptr.wrapping_add(Self::CURRENT_OFFSET) as *mut u32),

            // EXTRA SAFETY: the observer will never write to the rest of the control frame after initialisation.
            // We ensure initialisation in [`VmObserver::start`].
            // rest: core::slice::from_raw_parts(ptr.wrapping_add(8), PAGE_SIZE - 8),
            _kind: K::default(),
        }
    }

    #[inline]
    pub fn reserved_range(&self) -> Range<u64> {
        self.data.client_info.reserved_start..self.data.client_info.reserved_end
    }

    #[inline]
    pub fn xsave_layout(&self) -> &Layout {
        &self.data.xsave_layout
    }

    #[inline]
    pub fn num_command_frames(&self) -> u32 {
        self.data.num_command_frames
    }
}

impl<'a> ControlFrame<'a, Host> {
    /// Returns the command frame index that's currently being processed or waited on by the observer.
    /// If the command queue is empty, the observer is waiting for us to fill the command frame pointed to by `current`.
    /// If the command queue is not empty, the observer is currently processing the command frame pointed to by `current`.
    /// `current` is updated *after* the command frame itself has been updated.
    /// The command frame `self.current() - 1` is guaranteed to not be modified as long as `next` < `self.current() - 1`.
    #[inline]
    pub fn current(&self) -> u32 {
        self.data.current.load(Ordering::Acquire) % self.data.num_command_frames
    }

    #[inline]
    pub fn update_next(&self, index: u32) {
        self.data.next.store(index, Ordering::Release)
    }
}

impl<'a> ControlFrame<'a, Client> {
    #[inline]
    pub fn next(&self) -> u32 {
        self.data.next.load(Ordering::Acquire) % self.data.num_command_frames
    }

    #[inline]
    pub fn update_current(&self, index: u32) {
        self.data.current.store(index, Ordering::Release)
    }
}

/// An XSAVE layout entry.
#[repr(C)]
#[derive(Clone, Debug)]
pub struct Layout {
    pub x87: LayoutEntry,
    pub avx256: LayoutEntry,
}

/// XSAVE area layout information.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct LayoutEntry {
    pub available: bool,
    pub offset: u64,
    pub size: u64,
}

#[cfg(test)]
mod tests {
    use memoffset::offset_of;

    use crate::frame::control::ControlFrameData;

    #[test]
    pub fn verify_control_frame_alignment() {
        assert!(offset_of!(ControlFrameData, current) - offset_of!(ControlFrameData, next) >= 64);
    }
}
