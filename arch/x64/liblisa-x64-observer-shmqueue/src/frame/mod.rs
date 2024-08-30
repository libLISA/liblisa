//! Types representing the frames in the shared memory queue.

pub mod command;
pub mod control;

/// The size of a single command or control frame, which is equal to the x86 page size.
pub const FRAME_SIZE: usize = 4096;
