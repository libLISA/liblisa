use std::cell::{Ref, RefCell};
use std::rc::Rc;

use crate::arch::Arch;
use crate::encoding::dataflows::MemoryAccesses;
use crate::oracle::MappableArea;
use crate::state::random::{update_memory_addresses_unchecked, StateGen};
use crate::state::{AsSystemState, StateByte, SystemState, SystemStateByteView};

#[derive(Clone)]
enum SimpleMapping {
    Single(StateByte, u8),
    Multiple(Vec<(StateByte, u8)>),
}

/// A simple just-in-time CPU state, that replaces a fixed set of state bytes with the correct value.
///
/// Each derived state must change a specific subset of bytes, so this structure is unsuitable if many different state bytes might be changed.
/// In that case, use [`super::ComplexJitState`] instead.
#[derive(Clone)]
pub struct SimpleJitState<'a, A: Arch> {
    data: Rc<RefCell<SimpleState<A>>>,
    mapping: SimpleMapping,
    view: SystemStateByteView<'a, A>,
    accesses: &'a MemoryAccesses<A>,
    need_address_update: bool,
    id: usize,
}

struct SimpleState<A: Arch> {
    state: SystemState<A>,
    active: usize,
}

/// A reference to a [`SimpleJitState`].
pub struct SimpleStateRef<'a, A: Arch>(Ref<'a, SimpleState<A>>);

impl<'a, A: Arch> AsRef<SystemState<A>> for SimpleStateRef<'a, A> {
    fn as_ref(&self) -> &SystemState<A> {
        self.0.state.as_ref()
    }
}

impl<A: Arch> AsSystemState<A> for SimpleJitState<'_, A> {
    type Output<'a>
        = SimpleStateRef<'a, A>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        if self.data.borrow().active != self.id {
            let data = &mut *self.data.borrow_mut();
            data.active = self.id;
            let state = &mut data.state;
            // Update the bytes we modified
            match &self.mapping {
                SimpleMapping::Single(byte, value) => self.view.set(state, *byte, *value),
                SimpleMapping::Multiple(mapping) => {
                    for &(byte, value) in mapping.iter() {
                        self.view.set(state, byte, value);
                    }
                },
            }

            // Update memory addresses
            if self.need_address_update {
                update_memory_addresses_unchecked(self.accesses, state);
            }
        }

        SimpleStateRef(self.data.borrow())
    }

    fn num_memory_mappings(&self) -> usize {
        self.data.borrow().state.memory().len()
    }
}

impl<'a, A: Arch> SimpleJitState<'a, A> {
    /// Creates a new JIT state.
    /// All returned states will use the same underlying base state.
    ///
    /// The affected bytes must be pre-determined.
    /// Panics in debug mode when any bytes outside the `bytes_affected` list are modified.
    pub fn build<'ret, M: MappableArea>(
        bytes_affected: &'ret [StateByte], state_gen: &'ret StateGen<'a, A, M>, view: SystemStateByteView<'a, A>,
        base_state: &'ret SystemState<A>, mut create: impl FnMut(usize, &mut SystemState<A>) -> bool + 'ret, num: usize,
    ) -> impl Iterator<Item = SimpleJitState<'a, A>> + 'ret
    where
        'a: 'ret,
    {
        let need_address_update = state_gen.needs_adapt_from_bytes(&view, bytes_affected);
        let state = Rc::new(RefCell::new(SimpleState {
            state: base_state.clone(),
            active: usize::MAX,
        }));
        (0..num).flat_map(move |index| {
            let mut s = state.borrow_mut();
            if !create(index, &mut s.state) {
                None
            } else {
                let mapping = if bytes_affected.len() == 1 {
                    let byte = bytes_affected[0];
                    SimpleMapping::Single(byte, view.get(&s.state, byte))
                } else {
                    SimpleMapping::Multiple(bytes_affected.iter().map(|&byte| (byte, view.get(&s.state, byte))).collect())
                };

                // Make sure only the bytes specified in bytes_affected were modified
                debug_assert!((0..view.size())
                    .map(StateByte::new)
                    .all(|b| bytes_affected.contains(&b) || view.get(base_state, b) == view.get(&s.state, b)));

                if !need_address_update || state_gen.adapt(&mut s.state, false) {
                    Some(SimpleJitState {
                        data: state.clone(),
                        mapping,
                        view,
                        accesses: state_gen.accesses,
                        need_address_update,
                        id: index,
                    })
                } else {
                    None
                }
            }
        })
    }
}
