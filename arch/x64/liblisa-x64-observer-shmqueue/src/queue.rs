//! A shared memory queue for communication between the host and the VM client.

use core::fmt::Debug;
use core::marker::PhantomData;

use crate::frame::command::CommandFrame;
use crate::frame::control::{Client, ControlFrame, Host};

/// A shared memory queue.
pub struct Queue<K> {
    queue_ptr: *mut u8,
    command_frame_base: *mut CommandFrame,
    read_index: u32,
    cached_current_pos: u32,
    total_size: usize,
    _phantom: PhantomData<K>,
}

impl<K: Default> Debug for Queue<K> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Queue")
            .field("control", &self.control_frame())
            .field("command_frame_base", &self.command_frame_base)
            .field("read_index", &self.read_index)
            .field("total_size", &self.total_size)
            .finish()
    }
}

impl<K: Default> Queue<K> {
    /// # Safety
    /// You must ensure that queue_ptr is valid for the lifetime of the returned struct.
    pub unsafe fn new(queue_ptr: *mut u8, queue_byte_size: usize) -> Queue<K> {
        Queue {
            queue_ptr,
            command_frame_base: (queue_ptr as *mut CommandFrame).wrapping_add(1),
            read_index: 0,
            cached_current_pos: 0,
            total_size: queue_byte_size,
            _phantom: PhantomData,
        }
    }

    #[inline(always)]
    pub fn total_size(&self) -> usize {
        self.total_size
    }

    #[inline(always)]
    pub fn read_index(&self) -> u32 {
        self.read_index
    }

    #[inline]
    pub fn control_frame(&self) -> ControlFrame<'_, K> {
        unsafe {
            // SAFETY: `self.queue_ptr` must be a valid queue pointer for Self::new
            // SAFETY: The lifetime of the returned struct is less than or equal to the lifetime of self
            ControlFrame::new(self.queue_ptr)
        }
    }

    #[inline]
    pub fn command_frame(&mut self, index: usize) -> &mut CommandFrame {
        debug_assert!(index < self.control_frame().num_command_frames() as usize);
        unsafe { &mut *self.command_frame_base.wrapping_add(index) }
    }
}

impl<K: CurrentPos + Default> Queue<K> {
    #[inline]
    pub fn try_dequeue(&mut self) -> Option<&mut CommandFrame> {
        if self.request_available() {
            let frame_index = self.read_index as usize;
            self.read_index = (self.read_index + 1) % self.control_frame().num_command_frames();
            let frame = self.command_frame(frame_index);
            Some(frame)
        } else {
            // No commands are ready to be read
            None
        }
    }

    #[inline(always)]
    pub fn request_available(&mut self) -> bool {
        if self.read_index != self.cached_current_pos {
            true
        } else {
            self.cached_current_pos = K::current_pos(&self.control_frame());
            self.read_index != self.cached_current_pos
        }
    }
}

/// A trait that returns the current read position in the queue.
///
/// It is implemented separately for the [`Host`] and [`Client`].
pub trait CurrentPos: Sized {
    fn current_pos(control: &ControlFrame<Self>) -> u32;
}

impl CurrentPos for Host {
    #[inline(always)]
    fn current_pos(control: &ControlFrame<Self>) -> u32 {
        control.current()
    }
}

impl CurrentPos for Client {
    #[inline(always)]
    fn current_pos(control: &ControlFrame<Self>) -> u32 {
        control.next()
    }
}
