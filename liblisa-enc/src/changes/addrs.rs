use liblisa::arch::{Arch, Register};
use liblisa::encoding::bitpattern::FlowOutputLocation;
use liblisa::encoding::dataflows::MemoryAccesses;
use liblisa::semantics::{Computation, ARG_NAMES};
use liblisa::state::Location;
use log::{debug, info};

use crate::changes::{Change, ChangeLocation};

fn check_change<A: Arch>(
    base_accesses: &MemoryAccesses<A>, new_accesses: &MemoryAccesses<A>, mut current_change: Change<A>,
) -> Change<A> {
    for (access_index, (base, new)) in base_accesses.memory.iter().zip(new_accesses.memory.iter()).enumerate() {
        if base.size.end < new.size.end {
            // We can model a smaller memory access as leaving the extra bytes unmodified.
            // We cannot do the inverse, so we have to reject those cases here.
            debug!(
                "No valid change because new memory size is bigger: {:?} vs {:?}",
                base.size, new.size
            );
            return Change::Invalid;
        }

        let c1 = &base.calculation;
        let c2 = &new.calculation;
        if c1 != c2 {
            if let Some(fixed_offset) = c1.constant_offset_with(c2) {
                info!("Fixed offset = {:}", fixed_offset);
                let bit_indexes = (0..64)
                    .filter(|index| (fixed_offset.abs() >> index) & 1 == 1)
                    .collect::<Vec<_>>();
                let decreasing = fixed_offset < 0;

                match current_change {
                    Change::None => {
                        current_change = Change::MemoryOffset {
                            locations: vec![FlowOutputLocation::MemoryAccess(access_index)],
                            offset: c1.offset,
                            bit_indexes,
                            decreasing,
                            guessed: false,
                        }
                    },
                    Change::MemoryOffset {
                        ref mut locations,
                        ref mut offset,
                        bit_indexes: ref other_bit_indexes,
                        decreasing: other_decreasing,
                        ..
                    } => {
                        if other_bit_indexes != &bit_indexes {
                            info!(
                                "Found incompatible bit indexes between {} and {}: {:?} vs {:?}",
                                base, new, bit_indexes, other_bit_indexes
                            );
                            return Change::Invalid;
                        }

                        if decreasing != other_decreasing {
                            info!(
                                "Found incompatible inc/dec between {} and {}: {:?} vs {:?}",
                                base, new, decreasing, other_decreasing
                            );
                            return Change::Invalid;
                        }

                        if !locations.contains(&FlowOutputLocation::MemoryAccess(access_index)) {
                            locations.push(FlowOutputLocation::MemoryAccess(access_index));
                        }

                        if offset.abs() > c1.offset.abs() {
                            *offset = c1.offset;
                        }
                    },
                    _ => {
                        // TODO: What if this is a register change to zero and we're just detecting the fact that one register has been zeroed.
                        info!(
                            "Found an address Imm between {} and {}, but we're already tracking another change {:?}",
                            base, new, current_change
                        );
                        debug!("Computations: {:?} vs {:?}", c1, c2);
                        return Change::Invalid;
                    },
                }
            } else {
                match current_change {
                    Change::None => {
                        current_change = Change::MemoryComputation {
                            memory_indexes: vec![access_index],
                            from: *c1,
                            to: *c2,
                        };
                    },
                    Change::MemoryComputation {
                        memory_indexes: ref mut locations,
                        from,
                        to,
                    } if &from == c1 && &to == c2 => {
                        if !locations.contains(&access_index) {
                            locations.push(access_index);
                        }
                    },
                    Change::Register {
                        ref locations,
                        ref from,
                        ref to,
                    } => {
                        if let Some(ChangeLocation::MemoryAddress {
                            input_index, ..
                        }) = locations.iter().find(|x| match x {
                            ChangeLocation::MemoryAddress {
                                memory_index, ..
                            } => *memory_index == access_index,
                            _ => false,
                        }) {
                            if to.is_zero() {
                                let adjusted = c1.remove_term(*input_index);
                                info!(
                                    "Removed zero term = {} {:?}, equality = {}",
                                    adjusted.display(ARG_NAMES),
                                    adjusted,
                                    &adjusted == c2
                                );

                                if &adjusted != c2 {
                                    info!(
                                        "Found an address Imm between {} and {}, but we're already tracking a register change {:?} => {:?}",
                                        base, new, from, to
                                    );
                                    debug!("Computations: {:?} vs {:?}", c1, c2);
                                    return Change::Invalid;
                                }
                            } else if let Some(first_index) = base.inputs.iter().position(|input| input == &Location::Reg(*to)) {
                                let adjusted = c1.unify_terms(first_index, *input_index);
                                info!(
                                    "Accounted for duplicate term at indexes {} and {} = {:?} {:?} (c1={}, c2={}), equality = {}",
                                    first_index,
                                    input_index,
                                    adjusted.map(|x| x.display(ARG_NAMES).to_string()),
                                    adjusted,
                                    c1.display(ARG_NAMES),
                                    c2.display(ARG_NAMES),
                                    adjusted.as_ref() == Some(c2)
                                );

                                if adjusted.as_ref() != Some(c2) {
                                    info!(
                                        "Found an address Imm between {} and {}, but we're already tracking a register change {:?} => {:?}",
                                        base, new, from, to
                                    );
                                    debug!("Computations: {:?} vs {:?}", c1, c2);
                                    return Change::Invalid;
                                }
                            }
                        } else {
                            info!(
                                "Found an address Imm between {} and {}, but we're already tracking a register change {:?} => {:?}",
                                base, new, from, to
                            );
                            debug!("Computations: {:?} vs {:?}", c1, c2);
                            return Change::Invalid;
                        }
                    },
                    _ => {
                        info!(
                            "Found an address Imm between {} and {}, but we're already tracking another change {:?}",
                            base, new, current_change
                        );
                        debug!("Computations: {:?} vs {:?}", c1, c2);
                        return Change::Invalid;
                    },
                }
            }
        }
    }

    current_change
}

pub fn find_memory_access_imm<A: Arch>(
    base_accesses: &MemoryAccesses<A>, new_accesses: &MemoryAccesses<A>, change: Change<A>,
) -> Change<A> {
    if let Change::Multiple(changes) = change {
        Change::Multiple(
            changes
                .into_iter()
                .flat_map(|change| {
                    let change = check_change(base_accesses, new_accesses, change);
                    if change != Change::Invalid {
                        Some(change)
                    } else {
                        None
                    }
                })
                .collect(),
        )
    } else {
        check_change(base_accesses, new_accesses, change)
    }
}
