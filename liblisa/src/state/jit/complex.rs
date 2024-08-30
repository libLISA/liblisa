use std::cell::{Ref, RefCell};
use std::rc::Rc;

use crate::arch::Arch;
use crate::encoding::dataflows::MemoryAccesses;
use crate::oracle::MappableArea;
use crate::state::random::{update_memory_addresses_unchecked, StateGen};
use crate::state::{AsSystemState, StateByte, SystemState, SystemStateByteView};

#[derive(Copy, Clone)]
struct ComplexMappingEntry {
    byte: StateByte,
    from: u8,
    to: u8,
}

impl ComplexMappingEntry {
    fn apply<A: Arch>(&self, state: &mut SystemState<A>, view: &SystemStateByteView<A>) {
        view.set(state, self.byte, self.to);
    }

    fn revert<A: Arch>(&self, state: &mut SystemState<A>, view: &SystemStateByteView<A>) {
        view.set(state, self.byte, self.from);
    }
}

enum ComplexMapping {
    Single(ComplexMappingEntry),
    Multiple(Vec<ComplexMappingEntry>),
}

/// A CPU state that is constructed just-in-time by replacing specific state bytes with the correct values.
/// Each state change can be applied and reverted, reducing memory usage when specific instances of the state change different state bytes each time.
///
/// If the same state bytes are changed for every state, use a [`super::SimpleJitState`] instead.
#[derive(Clone)]
pub struct ComplexJitState<'a, A: Arch> {
    data: Rc<RefCell<ComplexState<'a, A>>>,
    id: usize,
}

struct ComplexItem {
    mapping: ComplexMapping,
    need_address_update: bool,
}

impl ComplexItem {
    fn apply<A: Arch>(&self, state: &mut SystemState<A>, view: &SystemStateByteView<A>) {
        match &self.mapping {
            ComplexMapping::Single(item) => item.apply(state, view),
            ComplexMapping::Multiple(items) => {
                for item in items.iter() {
                    item.apply(state, view)
                }
            },
        }
    }

    fn revert<A: Arch>(&self, state: &mut SystemState<A>, view: &SystemStateByteView<A>) {
        match &self.mapping {
            ComplexMapping::Single(item) => item.revert(state, view),
            ComplexMapping::Multiple(items) => {
                for item in items.iter() {
                    item.revert(state, view)
                }
            },
        }
    }
}

struct ComplexState<'a, A: Arch> {
    state: SystemState<A>,
    active: usize,
    items: Vec<ComplexItem>,
    view: SystemStateByteView<'a, A>,
    accesses: &'a MemoryAccesses<A>,
}

/// A reference to [`ComplexJitState`].
pub struct ComplexStateRef<'a, A: Arch>(Ref<'a, ComplexState<'a, A>>);

impl<'a, A: Arch> AsRef<SystemState<A>> for ComplexStateRef<'a, A> {
    fn as_ref(&self) -> &SystemState<A> {
        self.0.state.as_ref()
    }
}

impl<A: Arch> AsSystemState<A> for ComplexJitState<'_, A> {
    type Output<'a> = ComplexStateRef<'a, A>
        where Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        if self.data.borrow().active != self.id {
            let data = &mut *self.data.borrow_mut();
            let state = &mut data.state;
            if data.active != usize::MAX {
                data.items[data.active].revert(state, &data.view);
            }

            data.items[self.id].apply(state, &data.view);

            // Update memory addresses
            if (data.active != usize::MAX && data.items[data.active].need_address_update)
                || data.items[self.id].need_address_update
            {
                update_memory_addresses_unchecked(data.accesses, state);
            }

            data.active = self.id;
        }

        ComplexStateRef(self.data.borrow())
    }

    fn num_memory_mappings(&self) -> usize {
        self.data.borrow().state.memory().len()
    }
}

/// A builder for [`ComplexJitState`].
pub struct ComplexJitStateBuilder<'a, 's, A: Arch, M: MappableArea> {
    data: Rc<RefCell<ComplexState<'a, A>>>,
    state_gen: &'s StateGen<'a, A, M>,
    view: SystemStateByteView<'a, A>,
}

impl<'a, A: Arch> ComplexJitState<'a, A> {
    /// Creates a new [`ComplexJitStateBuilder`].
    /// The [`ComplexJitStateBuilder::create`] method can be invoked multiple times to create states that use the same underlying `base_state`.
    pub fn build<'s, M: MappableArea>(
        base_state: SystemState<A>, state_gen: &'s StateGen<'a, A, M>, view: SystemStateByteView<'a, A>,
    ) -> ComplexJitStateBuilder<'a, 's, A, M> {
        ComplexJitStateBuilder {
            data: Rc::new(RefCell::new(ComplexState {
                state: base_state,
                active: usize::MAX,
                items: Vec::new(),
                view,
                accesses: state_gen.accesses,
            })),
            state_gen,
            view,
        }
    }
}

impl<'a, 's, A: Arch, M: MappableArea> ComplexJitStateBuilder<'a, 's, A, M> {
    /// Returns a [`ComplexStateRef`] that will give the original base state passed to [`ComplexJitState::build`].
    pub fn as_original_system_state(&self) -> ComplexStateRef<A> {
        {
            let data = &mut *self.data.borrow_mut();
            let s = &mut data.state;
            if data.active != usize::MAX {
                data.items[data.active].revert(s, &self.view);
                if data.items[data.active].need_address_update {
                    update_memory_addresses_unchecked(data.accesses, s);
                }

                data.active = usize::MAX;
            }
        }

        ComplexStateRef(self.data.borrow())
    }

    /// Creates a new state that uses the same shared base state.
    /// The bytes changed must be declared in `bytes_affected`, relative to the base state.
    /// If any bytes outside the bytes in `bytes_affected` are changed, behavior is unspecified.
    ///
    /// The `bytes_affected` list may be different for every call.
    pub fn create(
        &self, bytes_affected: &[StateByte], create: impl FnOnce(&mut SystemState<A>) -> bool,
    ) -> Option<ComplexJitState<'a, A>> {
        let need_address_update = self.state_gen.needs_adapt_from_bytes(&self.view, bytes_affected);
        let data = &mut *self.data.borrow_mut();
        let id = data.items.len();

        let s = &mut data.state;

        if data.active != usize::MAX {
            data.items[data.active].revert(s, &self.view);
            if data.items[data.active].need_address_update {
                update_memory_addresses_unchecked(data.accesses, s);
            }

            data.active = usize::MAX;
        }

        let mut item = ComplexItem {
            mapping: if bytes_affected.len() == 1 {
                let byte = bytes_affected[0];
                ComplexMapping::Single(ComplexMappingEntry {
                    byte,
                    from: self.view.get(s, byte),
                    to: 0,
                })
            } else {
                ComplexMapping::Multiple(
                    bytes_affected
                        .iter()
                        .map(|&byte| ComplexMappingEntry {
                            byte,
                            from: self.view.get(s, byte),
                            to: 0,
                        })
                        .collect(),
                )
            },
            need_address_update,
        };

        if !create(s) {
            item.revert(s, &self.view);
            if need_address_update {
                update_memory_addresses_unchecked(data.accesses, s);
            }

            None
        } else if !need_address_update || self.state_gen.adapt(s, false) {
            match &mut item.mapping {
                ComplexMapping::Single(item) => item.to = self.view.get(s, item.byte),
                ComplexMapping::Multiple(items) => {
                    for item in items.iter_mut() {
                        item.to = self.view.get(s, item.byte)
                    }

                    items.retain(|item| item.from != item.to);
                },
            }

            data.active = id;
            data.items.push(item);

            Some(ComplexJitState {
                data: self.data.clone(),
                id,
            })
        } else {
            item.revert(s, &self.view);
            if need_address_update {
                update_memory_addresses_unchecked(data.accesses, s);
            }

            None
        }
    }

    /// Same as [`Self::create`], but uses the values from `new_values` zipped with `bytes_affected` instead of calling a function to modify the state.
    pub fn create_with_change_list(
        &self, bytes_affected: &[StateByte], mut new_values: impl Iterator<Item = u8>,
    ) -> Option<ComplexJitState<'a, A>> {
        if self.state_gen.needs_adapt_from_bytes(&self.view, bytes_affected) {
            self.create(bytes_affected, move |state| {
                for (&b, v) in bytes_affected.iter().zip(new_values) {
                    self.view.set(state, b, v);
                }

                true
            })
        } else {
            let data = &mut *self.data.borrow_mut();
            let id = data.items.len();

            let s = &mut data.state;

            // We need to revert, otherwise we'll save the wrong `from` values
            if data.active != usize::MAX {
                data.items[data.active].revert(s, &self.view);
                if data.items[data.active].need_address_update {
                    update_memory_addresses_unchecked(data.accesses, s);
                }

                data.active = usize::MAX;
            }

            let item = ComplexItem {
                mapping: if bytes_affected.len() == 1 {
                    let byte = bytes_affected[0];
                    ComplexMapping::Single(ComplexMappingEntry {
                        byte,
                        from: self.view.get(s, byte),
                        to: new_values.next().unwrap(),
                    })
                } else {
                    ComplexMapping::Multiple({
                        let mut items = bytes_affected
                            .iter()
                            .zip(new_values)
                            .map(|(&byte, to)| ComplexMappingEntry {
                                byte,
                                from: self.view.get(s, byte),
                                to,
                            })
                            .collect::<Vec<_>>();

                        items.retain(|item| item.from != item.to);
                        items
                    })
                },
                need_address_update: false,
            };

            data.items.push(item);

            Some(ComplexJitState {
                data: self.data.clone(),
                id,
            })
        }
    }
}
