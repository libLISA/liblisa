use std::fmt::{Debug, Display};

use serde::{Deserialize, Serialize};

use crate::state::{Addr, Area};

/// A memory mapping in a [`MemoryState`].
pub type MemoryEntry = (Addr, Permissions, Vec<u8>);

/// Memory state of a CPU.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct MemoryState {
    data: Box<[MemoryEntry]>,
}

struct DisplayBytesAsHex<'a>(&'a [u8]);

impl Debug for DisplayBytesAsHex<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", hex::encode(self.0))
    }
}

impl Display for DisplayBytesAsHex<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", hex::encode(self.0))
    }
}

impl Debug for MemoryState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut c = f.debug_struct("Memory");

        for (addr, perms, data) in self.iter() {
            c.field(&format!("0x{addr:X}({perms:?})"), &DisplayBytesAsHex(data));
        }

        c.finish()
    }
}

impl Display for MemoryState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (addr, perms, data) in self.iter() {
            let qualifier = match perms {
                Permissions::Read => "R.Mem",
                Permissions::ReadWrite => "RwMem",
                Permissions::Execute => "X.Mem",
            };

            writeln!(f, "{}[0x{:X}] = {}", qualifier, addr, &DisplayBytesAsHex(data))?;
        }

        Ok(())
    }
}

/// The access permissions of a memory mapping.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Permissions {
    /// Read-only data
    Read,

    /// Readable and writable data
    ReadWrite,

    /// Executable instructions
    Execute,
}

/// A mutable reference to a memory mapping in [`MemoryState`].
pub struct MemoryStateItemMut<'m> {
    memory_state: &'m mut MemoryState,
    index: usize,
}

impl<'m> MemoryStateItemMut<'m> {
    /// Replaces the current data in the memory mapping with `new_data`.
    #[inline]
    pub fn set_data(&mut self, new_data: &[u8]) {
        let vec = &mut self.memory_state.data[self.index].2;
        vec.clear();
        vec.extend_from_slice(new_data);
    }

    /// Allows the data in the memory mapping to be modified through a `&mut` pointer.
    #[inline]
    pub fn modify_data(&mut self, f: impl FnOnce(&mut [u8])) {
        f(&mut self.memory_state.data[self.index].2)
    }

    /// Crops or extends the data in the mapping to be exactly `max_size` bytes.
    #[inline]
    pub fn crop_data(&mut self, max_size: usize) {
        let vec = &mut self.memory_state.data[self.index].2;
        if vec.len() > max_size {
            self.memory_state.data[self.index].2.resize(max_size, 0)
        }
    }

    /// Replaces the address of the mapping with `new_addr`.
    #[inline]
    pub fn set_addr(&mut self, new_addr: Addr) {
        self.memory_state.data[self.index].0 = new_addr;
    }

    /// Returns the address of the mapping.
    #[inline]
    pub fn addr(&self) -> Addr {
        self.memory_state.data[self.index].0
    }

    /// Returns the permissions of the mapping.
    #[inline]
    pub fn permissions(&self) -> Permissions {
        self.memory_state.data[self.index].1
    }

    /// Returns a read-only reference to the data of the mapping.
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.memory_state.data[self.index].2
    }
}

impl MemoryState {
    /// Creates a new memory state from the items in `items`.
    #[inline]
    pub fn new<I: Iterator<Item = MemoryEntry>>(items: I) -> MemoryState {
        MemoryState {
            data: items.collect(),
        }
    }

    /// Creates a new memory state from the items in `data`.
    #[inline]
    pub fn from_vec(data: Vec<MemoryEntry>) -> MemoryState {
        MemoryState {
            data: data.into_boxed_slice(),
        }
    }

    /// Returns a mutable reference to the memory entry at position `index`.
    /// Does not panic until the item is used.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> MemoryStateItemMut<'_> {
        MemoryStateItemMut {
            memory_state: self,
            index,
        }
    }

    /// Iterates over all memory entries in the mapping.
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, MemoryEntry> {
        self.data.iter()
    }

    /// Iterates over all areas mapped by the memory mappings.
    #[inline]
    pub fn areas(&self) -> impl ExactSizeIterator<Item = Area> + '_ {
        self.data.iter().map(|(addr, _, data)| addr.into_area(data.len() as u64))
    }

    /// Returns a read-only reference to a memory entry.
    #[inline]
    pub fn get(&self, index: usize) -> &MemoryEntry {
        &self.data[index]
    }

    /// Returns the memory entry at position `index`, or `None` if it does not exist.
    #[must_use]
    #[inline]
    pub fn get_checked(&self, index: usize) -> Option<&MemoryEntry> {
        self.data.get(index)
    }

    /// Returns the address of the memory entry at position `index`.
    #[must_use]
    #[inline]
    pub fn addr(&self, index: usize) -> Addr {
        self.data[index].0
    }

    /// Returns the number of memory entries in the mapping.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the mapping contains no memory entries.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
