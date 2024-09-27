use std::cell::{Ref, RefCell};
use std::rc::Rc;

use crate::arch::{Arch, CpuState};
use crate::encoding::dataflows::MemoryAccesses;
use crate::oracle::MappableArea;
use crate::state::random::{update_memory_addresses_unchecked, StateGen};
use crate::state::{AsSystemState, SystemState};

#[derive(Clone)]
struct GpRegMapping<A: Arch> {
    reg: A::GpReg,
    from: u64,
    to: u64,
    need_address_update: bool,
}

impl<A: Arch> GpRegMapping<A> {
    fn apply(&self, state: &mut SystemState<A>) {
        state.cpu_mut().set_gpreg(self.reg, self.to);
    }

    fn revert(&self, state: &mut SystemState<A>) {
        state.cpu_mut().set_gpreg(self.reg, self.from);
    }
}

/// A just-in-time CPU state that replaces one or more general-purpose registers with the correct values.
#[derive(Clone)]
pub struct GpRegJitState<'a, A: Arch> {
    data: Rc<RefCell<GpRegState<'a, A>>>,
    id: usize,
}

struct GpRegState<'a, A: Arch> {
    state: SystemState<A>,
    items: Vec<GpRegMapping<A>>,
    accesses: &'a MemoryAccesses<A>,
    active: usize,
}

/// A reference to a [`GpRegJitState`].
pub struct GpRegStateRef<'a, A: Arch>(Ref<'a, GpRegState<'a, A>>);

impl<'a, A: Arch> AsRef<SystemState<A>> for GpRegStateRef<'a, A> {
    fn as_ref(&self) -> &SystemState<A> {
        self.0.state.as_ref()
    }
}

impl<A: Arch> AsSystemState<A> for GpRegJitState<'_, A> {
    type Output<'a>
        = GpRegStateRef<'a, A>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        if self.data.borrow().active != self.id {
            let data = &mut *self.data.borrow_mut();
            let state = &mut data.state;
            if data.active != usize::MAX {
                data.items[data.active].revert(state);
            }

            data.items[self.id].apply(state);

            // Update memory addresses
            if (data.active != usize::MAX && data.items[data.active].need_address_update)
                || data.items[self.id].need_address_update
            {
                update_memory_addresses_unchecked(data.accesses, state);
            }

            data.active = self.id;
        }

        GpRegStateRef(self.data.borrow())
    }

    fn num_memory_mappings(&self) -> usize {
        self.data.borrow().state.memory().len()
    }
}

/// A builder for [`GpRegJitState`].
pub struct GpRegJitStateBuilder<'a, 's, A: Arch, M: MappableArea> {
    data: Rc<RefCell<GpRegState<'a, A>>>,
    state_gen: &'s StateGen<'a, A, M>,
}

impl<'a, A: Arch> GpRegJitState<'a, A> {
    /// Creates a new builder.
    /// The [`GpRegJitStateBuilder::create`] method can be invoked multiple times to create multiple states that all use the same provided base state.
    pub fn build<'s, M: MappableArea>(
        base_state: &SystemState<A>, state_gen: &'s StateGen<'a, A, M>,
    ) -> GpRegJitStateBuilder<'a, 's, A, M> {
        GpRegJitStateBuilder {
            data: Rc::new(RefCell::new(GpRegState {
                state: base_state.clone(),
                active: usize::MAX,
                items: Vec::new(),
                accesses: state_gen.accesses,
            })),
            state_gen,
        }
    }
}

impl<'a, 's, A: Arch, M: MappableArea> GpRegJitStateBuilder<'a, 's, A, M> {
    /// Creates a new state using the same base state.
    pub fn create(&mut self, reg: A::GpReg, mut create: impl FnMut(&mut SystemState<A>) -> bool) -> Option<GpRegJitState<'a, A>> {
        let need_address_update = self.state_gen.needs_adapt_from_gpregs(&[reg]);
        let data = &mut *self.data.borrow_mut();
        let id = data.items.len();

        let s = &mut data.state;

        if data.active != usize::MAX {
            data.items[data.active].revert(s);
            if data.items[data.active].need_address_update {
                update_memory_addresses_unchecked(data.accesses, s);
            }

            data.active = usize::MAX;
        }

        let mut mapping = GpRegMapping {
            reg,
            from: s.cpu().gpreg(reg),
            to: 0,
            need_address_update,
        };

        if !create(s) {
            mapping.revert(s);
            if need_address_update {
                update_memory_addresses_unchecked(self.state_gen.accesses, s);
            }

            None
        } else if !need_address_update || self.state_gen.adapt(s, false) {
            mapping.to = s.cpu().gpreg(reg);

            // TODO: debug_assert only `reg` was modified in the new state

            assert_eq!(id, data.items.len());
            data.active = id;
            data.items.push(mapping);

            Some(GpRegJitState {
                data: self.data.clone(),
                id,
            })
        } else {
            mapping.revert(s);
            if need_address_update {
                update_memory_addresses_unchecked(self.state_gen.accesses, s);
            }

            None
        }
    }
}
