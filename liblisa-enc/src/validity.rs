use std::fmt::Display;
use std::iter::once;

use liblisa::arch::{Arch, CpuState, Scope};
use liblisa::instr::Instruction;
use liblisa::oracle::{MappableArea, Oracle, OracleError};
use liblisa::state::{Addr, MemoryState, Permissions, SystemState};
use liblisa::utils::{bitmask_u64, EitherIter};
use log::{trace, warn};
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

/// Determines whether a byte string is too short, too long, invalid, out-of-scope, or a valid instruction.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Validity {
    TooShort,
    TooLong,
    InvalidInstruction,
    Excluded,
    Error,
    Ok,
}

fn create_state_with_cropped_instr<A: Arch, M: MappableArea>(
    instr: &Instruction, rng: &mut Xoshiro256PlusPlus, mappable: &M,
) -> SystemState<A> {
    assert!(instr.byte_len() > A::INSTRUCTION_ALIGNMENT);
    let len = instr.byte_len() - A::INSTRUCTION_ALIGNMENT;
    create_state_with_cropped_instr_unchecked(rng, len, instr, mappable)
}

fn create_state_with_all_possible_cropped_instr<'a, A: Arch, M: MappableArea>(
    instr: &'a Instruction, rng: &'a mut Xoshiro256PlusPlus, mappable: &'a M,
) -> impl Iterator<Item = SystemState<A>> + 'a {
    (A::INSTRUCTION_ALIGNMENT..instr.byte_len())
        .step_by(A::INSTRUCTION_ALIGNMENT)
        .map(move |len| create_state_with_cropped_instr_unchecked(rng, len, instr, mappable))
}

fn create_state_with_cropped_instr_unchecked<A: Arch, M: MappableArea>(
    rng: &mut Xoshiro256PlusPlus, len: usize, instr: &Instruction, mappable: &M,
) -> SystemState<A> {
    loop {
        let page = loop {
            let addr = Addr::new(rng.gen::<u64>() & !bitmask_u64(A::PAGE_BITS as u32));
            if mappable.can_map(addr) {
                break addr.page::<A>()
            }
        };

        let pc = page.first_address_after_page() - len as u64;
        let mut cpu_state = A::CpuState::default();
        cpu_state.set_gpreg(A::PC, pc.as_u64());
        let memory = [
            (pc, Permissions::Execute, instr.bytes()[0..len].to_owned()),
            (page.first_address_after_page(), Permissions::ReadWrite, vec![0]),
        ];

        if memory.iter().all(|&(addr, ..)| mappable.can_map(addr)) {
            break SystemState::new(cpu_state, MemoryState::new(memory.into_iter()))
        }
    }
}

fn create_state_with_instr<A: Arch, M: MappableArea>(
    instr: &Instruction, rng: &mut Xoshiro256PlusPlus, mappable: &M,
) -> SystemState<A> {
    loop {
        let page = loop {
            let addr = Addr::new(rng.gen::<u64>() & !bitmask_u64(A::PAGE_BITS as u32));
            if mappable.can_map(addr) {
                break addr.page::<A>()
            }
        };

        let pc = page.first_address_after_page() - instr.byte_len() as u64;
        let mut cpu_state = A::CpuState::default();
        cpu_state.set_gpreg(A::PC, pc.as_u64());
        let memory = [
            (pc, Permissions::Execute, instr.bytes().to_owned()),
            (page.first_address_after_page(), Permissions::ReadWrite, vec![0]),
        ];

        if memory.iter().all(|&(addr, ..)| mappable.can_map(addr)) {
            break SystemState::new(cpu_state, MemoryState::new(memory.into_iter()))
        }
    }
}

impl Validity {
    pub fn check_if_cropped_instruction_executed_successfully<A: Arch>(
        state: &SystemState<A>, result: &Result<SystemState<A>, OracleError>,
    ) -> Option<Validity> {
        let (instr_addr, _, data) = state.memory().get(0);
        let len = data.len();
        let first_addr_after_instr = *instr_addr + len as u64;
        match result {
            // We expect this error; The instruction is too short, so we get a page fault at the memory address
            // We mapped an RW page at this address, so if this still get a page fault here it must be the instruction fetch
            Err(OracleError::MemoryAccess(addr)) if addr == &first_addr_after_instr => None,
            Err(OracleError::InstructionFetchMemoryAccess(addr)) => {
                if *addr == first_addr_after_instr {
                    // Instruction fetching failed because the next page isn't mapped.
                    // This is exactly what we expected to see if the instruction is not too long.
                    None
                } else {
                    warn!(
                        "Something is wrong; Execution is fetching instructions from random places. Instruction is @ 0x{instr_addr:X}, but we got an instruction fetch @ 0x{addr:X}, for instruction {data:02X?}"
                    );
                    Some(Validity::Error)
                }
            },
            // If we see any other error, or see no error at all, this means the instruction was fully interpreted (which shouldn't be possible because we sliced it down to len bytes)
            Err(OracleError::ApiError(e)) => {
                panic!("Unable to verify instruction: {e:?}")
            },
            Err(OracleError::MultipleInstructionsExecuted) => {
                unreachable!("This should never happen because we always use the trap flag here...")
            },
            Ok(_)
            | Err(OracleError::GeneralFault)
            | Err(OracleError::InvalidInstruction)
            | Err(OracleError::MemoryAccess(_))
            | Err(OracleError::ComputationError)
            | Err(OracleError::Unreliable)
            | Err(OracleError::Timeout) => {
                // Not a minimal instruction because instruction size changed
                Some(Validity::TooLong)
            },
        }
    }

    fn check_instruction<A: Arch>(state: SystemState<A>, result: Result<SystemState<A>, OracleError>) -> Validity {
        let (instr_addr, _, data) = state.memory().get(0);
        let len = data.len();
        let first_addr_after_instr = *instr_addr + len as u64;
        match result {
            Err(OracleError::MemoryAccess(addr)) if addr == first_addr_after_instr => Validity::TooShort,
            Err(OracleError::InstructionFetchMemoryAccess(addr)) => {
                if addr == first_addr_after_instr {
                    Validity::TooShort
                } else {
                    warn!(
                        "Something is wrong; Execution is fetching instructions from random places. Instruction is @ 0x{instr_addr:X}, but we got an instruction fetch @ 0x{addr:X}, for instruction {data:02X?}"
                    );
                    Validity::Error
                }
            },
            Err(OracleError::ApiError(e)) => panic!("Unable to verify instruction: {e:?}"),
            Err(OracleError::InvalidInstruction) => Validity::InvalidInstruction,
            Err(OracleError::MultipleInstructionsExecuted) => {
                unreachable!("This should never happen because we always use the trap flag here...")
            },

            // Anything other than these errors means the instruction was decoded succesfully!
            _ => Validity::Ok,
        }
    }

    pub fn infer<A: Arch, O: Oracle<A>>(o: &mut O, instr: &Instruction) -> Validity {
        if instr.byte_len() < A::INSTRUCTION_ALIGNMENT {
            return Validity::TooShort
        }

        let mappable = o.mappable_area();

        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());

        // Determine if the instruction is too long
        if O::UNRELIABLE_INSTRUCTION_FETCH_ERRORS {
            let state = create_state_with_instr(instr, &mut rng, &mappable);
            let cropped_states = create_state_with_all_possible_cropped_instr(instr, &mut rng, &mappable);

            let mut results = o.batch_observe_iter(once(state).chain(cropped_states));
            let (state, result) = results.next().unwrap();
            let cropped_results = results.collect::<Vec<_>>();

            trace!(
                "Observing to determine if the instruction is too long: {:X?}",
                cropped_results
            );
            trace!("Observing to determine if the instruction is too short: {:X?}", state);
            trace!("Result = {:X?}", result);

            for (cropped_state, cropped_result) in cropped_results {
                if let Some(validity) = Self::check_if_cropped_instruction_executed_successfully(&cropped_state, &cropped_result)
                {
                    return validity;
                }
            }

            Self::check_instruction(state, result)
        } else if instr.byte_len() > A::INSTRUCTION_ALIGNMENT {
            let cropped_state = create_state_with_cropped_instr(instr, &mut rng, &mappable);
            let state = create_state_with_instr(instr, &mut rng, &mappable);

            let [(_, cropped_result), (_, result)] = o.batch_observe([&cropped_state, &state]);

            trace!("Observing to determine if the instruction is too long: {:X?}", cropped_state);
            trace!("Result = {:X?}", cropped_result);
            trace!("Observing to determine if the instruction is too short: {:X?}", state);
            trace!("Result = {:X?}", result);

            if let Some(validity) = Self::check_if_cropped_instruction_executed_successfully(&cropped_state, &cropped_result) {
                return validity;
            }

            Self::check_instruction(state, result)
        } else {
            let state = create_state_with_instr(instr, &mut rng, &mappable);
            trace!("Observing to determine if the instruction is too short: {:X?}", state);
            let result = o.observe(&state);
            trace!("Result = {:X?}", result);
            Self::check_instruction(state, result)
        }
    }

    pub fn infer_batch<'a, A: Arch, O: Oracle<A>>(
        o: &'a mut O, instrs: &'a [Instruction], scope: &'a impl Scope,
    ) -> impl Iterator<Item = Validity> + 'a {
        let mappable = o.mappable_area();
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());

        let observations = instrs
            .iter()
            .flat_map(move |instr| {
                if instr.byte_len() < A::INSTRUCTION_ALIGNMENT {
                    None
                } else if scope.is_instr_in_scope(instr.bytes()) {
                    let state = create_state_with_instr(instr, &mut rng, &mappable);

                    if instr.byte_len() > A::INSTRUCTION_ALIGNMENT {
                        let cropped_state = create_state_with_cropped_instr(instr, &mut rng, &mappable);
                        Some(EitherIter::Right([cropped_state, state].into_iter()))
                    } else {
                        Some(EitherIter::Left(once(state)))
                    }
                } else {
                    None
                }
            })
            .flatten();

        ObservationResultIter {
            instrs,
            iter: o.batch_observe_gpreg_only_iter(observations),
            scope,
        }
    }
}

struct ObservationResultIter<'a, A: Arch, I: Iterator<Item = (SystemState<A>, Result<SystemState<A>, OracleError>)>, S: Scope> {
    instrs: &'a [Instruction],
    iter: I,
    scope: &'a S,
}

impl<'a, A: Arch, I: Iterator<Item = (SystemState<A>, Result<SystemState<A>, OracleError>)>, S: Scope> Iterator
    for ObservationResultIter<'a, A, I, S>
{
    type Item = Validity;

    fn next(&mut self) -> Option<Self::Item> {
        let instrs = self.instrs;
        if !self.instrs.is_empty() {
            self.instrs = &instrs[1..];

            let instr = instrs[0];

            trace!("Instr: {instr:#?}");
            Some(if instr.byte_len() < A::INSTRUCTION_ALIGNMENT {
                Validity::TooShort
            } else if self.scope.is_instr_in_scope(instr.bytes()) {
                if instr.byte_len() > A::INSTRUCTION_ALIGNMENT {
                    let (cropped_state, cropped_result) = self.iter.next().unwrap();
                    trace!("Cropped state: {cropped_state:X?}, result: {cropped_result:X?}");
                    if let Some(validity) =
                        Validity::check_if_cropped_instruction_executed_successfully(&cropped_state, &cropped_result)
                    {
                        // Skip normal state
                        drop(self.iter.next().unwrap());
                        return Some(validity);
                    }
                }

                let (state, result) = self.iter.next().unwrap();
                trace!("State: {state:X?}, result: {result:X?}");
                Validity::check_instruction(state, result)
            } else {
                Validity::Excluded
            })
        } else {
            None
        }
    }
}

impl Display for Validity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Validity::TooShort => f.write_str("TooShort"),
            Validity::TooLong => f.write_str("TooLong"),
            Validity::InvalidInstruction => f.write_str("InvalidInstruction"),
            Validity::Excluded => f.write_str("Excluded"),
            Validity::Ok => f.write_str("Ok"),
            Validity::Error => f.write_str("Error"),
        }
    }
}
