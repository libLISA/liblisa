use std::collections::HashSet;
use std::iter::once;
use std::mem::swap;
use std::time::Instant;

use itertools::Itertools;
use liblisa::arch::{Arch, CpuState};
use liblisa::encoding::dataflows::{AddrTerm, AddressComputation, Dest, Inputs, MemoryAccesses, Size, Source};
use liblisa::oracle::{MappableArea, Oracle, OracleError};
use liblisa::state::jit::GpRegJitState;
use liblisa::state::random::{RandomizationError, StateGen};
use liblisa::state::{Addr, AsSystemState, Permissions, SystemState};
use liblisa::value::Value;
use log::{debug, error, info, trace, warn};
use rand::Rng;
use rand_xoshiro::Xoshiro256PlusPlus;

use super::AccessAnalysisError;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OffsetConstraint {
    pub start: i64,

    /// The length of the area (range is inclusive).
    /// A constraint of length 0 includes 1 address.
    pub length: u64,
}

impl OffsetConstraint {
    pub const ALL: OffsetConstraint = OffsetConstraint {
        start: i64::MIN,
        length: u64::MAX,
    };

    pub fn fixed(offset: i64) -> OffsetConstraint {
        OffsetConstraint {
            start: offset,
            length: 0,
        }
    }

    pub fn intersect(self, other: OffsetConstraint) -> Option<OffsetConstraint> {
        let (lo, hi, length, max_length) = if self.start < other.start {
            (self.start, other.start, self.length, other.length)
        } else {
            (other.start, self.start, other.length, self.length)
        };

        length
            .checked_sub(if hi >= 0 {
                (hi as u64).wrapping_sub(lo as u64)
            } else {
                (hi - lo) as u64
            })
            .map(|length| OffsetConstraint {
                start: hi,
                length: length.min(max_length),
            })
    }
}

#[derive(Debug)]
pub struct OffsetConstraints {
    constraints: HashSet<OffsetConstraint>,
    only_fixed_offsets: bool,
}

impl OffsetConstraints {
    pub fn new() -> Self {
        let mut constraints = HashSet::new();
        constraints.insert(OffsetConstraint::ALL);
        OffsetConstraints {
            constraints,
            only_fixed_offsets: false,
        }
    }

    pub fn and<I: Iterator<Item = OffsetConstraint>>(&mut self, iter: impl Fn() -> I) {
        if self.only_fixed_offsets {
            // The constrains are already length 0, so we only need to remove them if they don't match any new constraint.
            self.constraints
                .retain(|old| iter().any(|item| item.intersect(*old).is_some()));
        } else if !self.constraints.is_empty() {
            let mut old = HashSet::new();
            let mut only_fixed_offsets = true;
            swap(&mut old, &mut self.constraints);
            for old in old.iter() {
                for item in iter() {
                    // debug!("  with {:?}", item);
                    // old.retain(|old| {
                    if let Some(new_item) = item.intersect(*old) {
                        // println!("    new: {:X?}", new_item);
                        self.constraints.insert(new_item);
                        only_fixed_offsets &= new_item.length == 0;

                        if old.length == 0 {
                            break;
                        }
                    }
                    // });
                }
            }

            self.only_fixed_offsets = only_fixed_offsets;
        }
    }

    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    pub fn real_offsets(&self) -> impl Iterator<Item = i64> + '_ {
        self.constraints.iter().filter(|c| c.length == 0).map(|c| c.start)
    }
}

impl Default for OffsetConstraints {
    fn default() -> Self {
        Self::new()
    }
}

pub struct AddressComputationIterator<'a, A: Arch> {
    inputs: &'a [A::GpReg],
    terms: &'a [Vec<AddrTerm>],
    bases: &'a [(SystemState<A>, Addr)],
}

impl<'a, A: Arch> AddressComputationIterator<'a, A> {
    pub fn new(
        inputs: &'a [A::GpReg], terms: &'a [Vec<AddrTerm>], bases: &'a [(SystemState<A>, Addr)],
    ) -> AddressComputationIterator<'a, A> {
        AddressComputationIterator {
            inputs,
            terms,
            bases,
        }
    }

    /// Enumerates all possible offsets.
    /// The function `f` is called once for each offset that is consistent with all bases.
    pub fn run(&self, f: impl Fn(&AddressComputation) -> bool) -> Vec<AddressComputation> {
        let mut seen = HashSet::new();
        let mut possible_calculations = Vec::new();
        let mut counter = [0; 4];

        loop {
            let terms = {
                let mut index = 0;
                counter.map(|n| {
                    let terms = self.terms.get(index);
                    index += 1;

                    terms.map(|terms| terms[n]).unwrap_or_default()
                })
            };

            debug!("{:?} = {:?}", counter, terms);

            seen.clear();
            let base_computation = AddressComputation {
                terms,
                offset: 0,
            };

            // Figure out what offsets are possible.
            let mut constraints = OffsetConstraints::new();
            for (base, addr) in self.bases.iter() {
                let base_addr = base_computation.compute_from_gpregs(self.inputs, base);
                let offset = addr.as_u64().wrapping_sub(base_addr) as i64;

                trace!(
                    "Adding (without offset: {:X?}) {:X?} => {:X?}, giving offset {:X?}",
                    base_addr,
                    self.inputs.iter().map(|reg| base.cpu().gpreg(*reg)).collect::<Vec<_>>(),
                    addr,
                    offset
                );
                // Either the correct offset was observed, or the offset is such that the address ends up in one of the already mapped areas.
                constraints.and(|| {
                    once(OffsetConstraint::fixed(offset)).chain(base.memory().iter().map(|(other_addr, ..)| OffsetConstraint {
                        start: other_addr.page::<A>().start_addr().as_u64().wrapping_sub(base_addr) as i64,
                        length: (1 << A::PAGE_BITS) - 1,
                    }))
                });

                if constraints.is_empty() {
                    debug!("No offsets are valid.");
                    break;
                }
            }

            debug!("Constraints: {:X?}", constraints);

            for offset in constraints.real_offsets() {
                debug!("Trying offset: {:X?}", offset);
                let c = AddressComputation {
                    terms,
                    offset,
                };

                if !seen.contains(&c.offset) {
                    seen.insert(c.offset);

                    if f(&c) {
                        possible_calculations.push(c);
                    }
                }
            }

            for (item, terms) in counter.iter_mut().zip(self.terms.iter()) {
                *item += 1;
                if *item >= terms.len() {
                    *item = 0;
                } else {
                    break;
                }
            }

            if counter == [0; 4] {
                break;
            }
        }

        possible_calculations
    }
}

pub struct InferComputation<'a, A: Arch, M: MappableArea> {
    pub directly_after_other_mapping: usize,
    pub other_mapping: Option<usize>,
    pub bases: Vec<(SystemState<A>, Addr)>,
    pub accesses: &'a MemoryAccesses<A>,
    pub state_gen: &'a StateGen<'a, A, M>,
    pub oks: Vec<SystemState<A>>,
    pub more_memory_accesses_expected: bool,
}

struct Test<'b, A: Arch> {
    state_in: GpRegJitState<'b, A>,
    base: &'b SystemState<A>,
    addr: Addr,
}

impl<'b, A: Arch> AsSystemState<A> for Test<'b, A> {
    type Output<'a>
        = <GpRegJitState<'b, A> as AsSystemState<A>>::Output<'a>
    where
        Self: 'a;

    fn as_system_state(&self) -> Self::Output<'_> {
        self.state_in.as_system_state()
    }

    fn num_memory_mappings(&self) -> usize {
        self.state_in.num_memory_mappings()
    }
}

#[derive(Debug)]
struct RegisterCandidates<A: Arch> {
    registers: Vec<(A::GpReg, Vec<AddrTerm>)>,
    priority_bases: Vec<(SystemState<A>, Addr)>,
    extra_bases: Vec<(SystemState<A>, Addr)>,
}

#[derive(Debug)]
pub struct InferredComputation<A: Arch> {
    pub inputs: Inputs<A>,
    pub calculation: AddressComputation,
    pub bases: Vec<(SystemState<A>, Addr)>,
}

impl<'a, A: Arch, M: MappableArea> InferComputation<'a, A, M> {
    fn find_register_candidates<O: Oracle<A>, R: Rng>(
        &self, o: &mut O, rng: &mut R, assume_last_memory_access: bool,
    ) -> Result<RegisterCandidates<A>, RandomizationError> {
        // ARCHITECTURE ASSUMPTION: Memory access addresses only depend on GPRegs
        let mut registers = Vec::new();
        let mut priority_bases = Vec::new();
        let mut extra_bases = Vec::with_capacity(100_000);
        let mut bases = self
            .bases
            .iter()
            .filter(|(base, addr)| {
                !base.memory().iter().any(|(mem_addr, _, data)| {
                    mem_addr
                        .into_area(data.len() as u64)
                        .shares_page_with::<A>(&addr.into_area(1))
                })
            })
            .take(10_000)
            .map(|(base, addr)| (base, GpRegJitState::build(base, self.state_gen), *addr))
            .collect::<Vec<_>>();
        for gpreg in A::iter_gpregs() {
            let s = Instant::now();
            let mut tests = Vec::with_capacity(bases.len());
            let mut n = 0;
            let needs_adapt = self.state_gen.needs_adapt_from_gpregs(&[gpreg]);

            for (base, builder, addr) in bases.iter_mut() {
                let modified = builder.create(gpreg, |modified| {
                    let mut n = 0;
                    loop {
                        let from = modified.cpu().gpreg(gpreg);
                        modified.cpu_mut().set_gpreg(gpreg, self.state_gen.randomize_register(rng, A::reg(gpreg)));
                        if (!needs_adapt || self.state_gen.adapt(modified, false)) && !modified.memory().iter().any(|(mem_addr, _, data)| mem_addr.into_area(data.len() as u64).shares_page_with::<A>(&addr.into_area(1))) {
                            debug_assert!(
                                modified.memory().iter().enumerate().all(|(i1, m1)|
                                    !modified.memory().iter().enumerate().any(|(i2, m2)|
                                        i1 != i2 && m1.0.into_area(m1.2.len() as u64).shares_page_with::<A>(
                                            &m2.0.into_area(m2.2.len() as u64)
                                        ) && matches!((m1.1, m2.1),
                                            (Permissions::Read | Permissions::ReadWrite, Permissions::Execute)
                                            | (Permissions::Execute, Permissions::Read | Permissions::ReadWrite)
                                        )
                                    )
                                ),
                                "Adapting {base:X?} with modified {gpreg} from {from:X?} => {:X?} produces invalid state: {modified:X?}",
                                modified.cpu().gpreg(gpreg),
                            );
                            break;
                        }

                        n += 1;
                        if n > 5000 {
                            return false;
                        }
                    }

                    true
                });

                if modified.is_none() {
                    n += 1;
                }

                if n > 500 {
                    warn!("Modifying register {gpreg:?} in base (addr=0x{addr:X?}) {base:?} failed");
                    return Err(RandomizationError::ModifyingValuesFailed);
                }

                if let Some(modified) = modified {
                    tests.push(Test {
                        state_in: modified,
                        addr: *addr,
                        base,
                    });
                }
            }

            info!("{:?} test generation in {}ms", gpreg, s.elapsed().as_millis());

            let mut might_be_used = false;
            let mut terms = AddrTerm::all().into_iter().enumerate().collect::<Vec<_>>();
            let mut applicable_terms: Vec<(usize, AddrTerm, usize)> = Vec::new();
            let mut num_changed = 0;
            let s = Instant::now();
            for (index, (test, test_result)) in o.batch_observe_iter(tests.into_iter()).enumerate() {
                // Early exit if this register doesn't alter the address
                if index >= 10_000 && num_changed <= 0 {
                    break;
                }

                let original_addr = test.addr;
                let original_input = test.base;
                let test_input = test.state_in.as_system_state();
                let test_input = test_input.as_ref();
                match test_result {
                    Err(OracleError::MemoryAccess(addr)) => {
                        num_changed += 1;
                        let mut is_priority_base = false;
                        if addr != original_addr {
                            trace!(
                                "0x{:X} => 0x{:X} gives 0x{:X} => 0x{:X}",
                                test_input.cpu().gpreg(gpreg),
                                original_input.cpu().gpreg(gpreg),
                                original_addr,
                                addr
                            );

                            // There are four cases to consider:
                            // 1. both original_input and test_input do not have mappings that overlap with the new memory access
                            // 2. only original_input has a mapping that overlaps
                            // 3. only test_input has a mapping that overlaps
                            // 4. both original_input and test_input have mappings that overlap
                            //
                            // In case 1, the real delta is the delta we measure.
                            // In case 2, the real delta has an upper bound: the largest distance between a page mapping and the address from test_input.
                            // In case 3, the real delta has an upper bound: the largest distance between a page mapping and the address from original_input.
                            // In case 4, the real delta has an upper bound: the largest distance between two page mappings.

                            // let minimal_distance_to_overlap = test_input.memory.areas().map(|area| area.start_addr().distance_between())
                            let original_value = original_input.cpu().gpreg(gpreg);
                            let new_value = test_input.cpu().gpreg(gpreg);
                            terms.retain(|(term_index, term)| {
                                // TODO: Count number of times term is valid delta. At the end, remove if we didn't find any applicable terms
                                if term.is_valid_delta(original_value, new_value, original_addr.as_u64(), addr.as_u64()) {
                                    let mut found_applicable_term = false;
                                    for (applicable_term_index, term, num) in applicable_terms.iter_mut() {
                                        if *applicable_term_index < *term_index && term.is_valid_delta(original_value, new_value, original_addr.as_u64(), addr.as_u64()) {
                                            found_applicable_term = true;
                                            *num += 1;
                                            break;
                                        }
                                    }

                                    if !found_applicable_term {
                                        debug!("New applicable term: {:?} on 0x{:X} => 0x{:X} gives 0x{:X} => 0x{:X}", term, original_input.cpu().gpreg(gpreg), test_input.cpu().gpreg(gpreg), original_addr, addr);
                                        applicable_terms.push((*term_index, *term, 1));

                                        applicable_terms.sort_by_key(|&(index, _, _)| index);

                                        priority_bases.push((test_input.clone(), addr));
                                        is_priority_base = true;

                                        return false;
                                    } else {
                                        trace!("Applicable but ignored because we already have another term covering it: {:?}", term);
                                    }
                                } else if assume_last_memory_access {
                                    return false;
                                }

                                if assume_last_memory_access {
                                    let possible = term.is_possible_with_delta(original_addr.as_u64(), addr.as_u64());
                                    if !possible {
                                        debug!("Eliminating term {:?} early, because it's not possible with accesses: {:X?} vs {:X?}", term, original_addr, addr);
                                    }

                                    possible
                                } else {
                                    true
                                }
                            });

                            might_be_used = true;
                        }

                        if !is_priority_base {
                            extra_bases.push((test_input.clone(), addr));
                        }
                    },
                    Err(OracleError::MultipleInstructionsExecuted) => {
                        return Err(RandomizationError::OracleError(OracleError::MultipleInstructionsExecuted))
                    },
                    Err(OracleError::GeneralFault) => {
                        num_changed += 1;
                    },
                    result => {
                        trace!(
                            "Result {:?} when changing {:?} in: {:X?} to {:X?}",
                            result,
                            gpreg,
                            original_input,
                            test_input
                        );
                    },
                }
            }

            info!(
                "{:?} terms ({}): {:X?} in {}ms",
                gpreg,
                applicable_terms.len(),
                applicable_terms,
                s.elapsed().as_millis()
            );

            if might_be_used {
                // Pick only the applicable terms for which we found more than one case per thousand bases.
                let threshold = self.bases.len().min(100_000) / 5000;
                debug!("Applicable terms before threshold filtering (threshold={threshold}): {applicable_terms:?}");
                let mut applicable_terms = applicable_terms
                    .into_iter()
                    .map(|(_, term, num)| (term, num))
                    .filter(|&(_, num)| num > threshold)
                    .map(|(term, _)| term)
                    .collect::<Vec<_>>();
                if !applicable_terms.contains(&AddrTerm::identity()) {
                    applicable_terms.push(AddrTerm::identity());
                }

                debug!("Applicable terms after threshold filtering: {applicable_terms:?}");

                registers.push((gpreg, applicable_terms));
            }
        }

        registers.sort_by_key(|(_, choices)| choices.len());

        Ok(RegisterCandidates {
            registers,
            priority_bases,
            extra_bases,
        })
    }

    /// Finds the calculation that computes the memory address for bases, if such a calculation exists.
    /// Calculations are a sum of inputs where one input might be scaled by a constant.
    fn find_calculation_with_inputs(
        inputs: &[A::GpReg], terms: &[Vec<AddrTerm>], bases: &[(SystemState<A>, Addr)], _oks: &[SystemState<A>],
    ) -> Vec<AddressComputation> {
        debug!("Inputs: {:?}", inputs);
        let possible_calculations = AddressComputationIterator::new(inputs, terms, bases).run(|calculation| {
            // The computation must be double-mapped to another existing address
            // TODO: Do we need this? It prevents us from analyzing instructions like f348ab (rep stosb)
            // for ok in oks.iter() {
            //     let v = Addr::new(calculation.compute_from_gpregs(inputs, ok));
            //     if !ok.memory().iter().any(|(addr, _, _)| addr.page::<A>() == v.page::<A>()) {
            //         trace!("{:?} does not produce ok state for: {:?}", calculation, ok);
            //         return false;
            //     }
            // }

            debug!(
                "{:?} w/ {:?} is acceptable for all {} bases",
                inputs,
                calculation,
                bases.len()
            );

            // If we only saw overlapping instances, we consider the calculation invalid
            // There will always be 1 instance valid, because of the way we generate the offset
            true
        });

        possible_calculations
    }

    fn find_calculation<R: Rng, O: Oracle<A>>(
        &self, registers: &[(A::GpReg, Vec<AddrTerm>)], rng: &mut R, oracle: &mut O, assume_last_memory_access: bool,
    ) -> Option<(Inputs<A>, AddressComputation)> {
        let sources = registers;
        let mut possible_calculations = Vec::new();
        let input_range = if assume_last_memory_access {
            let n = sources.len().min(4);
            n..n + 1
        } else {
            0..5
        };
        for num_inputs in input_range {
            for mut combination in sources.iter().cloned().combinations(num_inputs) {
                // Sort first to make sure the reg <=> term relation stays the same.
                // We must sort to keep the ordering consistent between multiple executions.
                combination.sort_by_key(|(reg, _)| *reg);

                let inputs = combination.iter().map(|(reg, _)| *reg).collect::<Vec<_>>();
                let terms = combination.iter().map(|(_, term)| term.clone()).collect::<Vec<_>>();
                let new = Self::find_calculation_with_inputs(&inputs, &terms, &self.bases, &self.oks)
                    .into_iter()
                    .filter(|v| {
                        self.accesses.iter().all(|access| {
                            if access.inputs == inputs.as_ref() {
                                if let Some(offset) = access.calculation.constant_offset_with(v) {
                                    if offset >= 0 && offset < access.size.end as i64 {
                                        // This is an 'invisible' access. We have no actual evidence it exists.
                                        // It's just a possibility for which we can't find a counterexample.
                                        // We're eliminating it because if it did exist, we wouldn't be able to analyze the instruction at all.
                                        // In a way, memory accesses that are always within another memory access aren't real memory accesses anyway.
                                        // We can always approximate the semantics by re-using data from the other memory access it overlaps.
                                        return false;
                                    }
                                }
                            }

                            true
                        })
                    })
                    .map(|v| (inputs.clone(), v));
                possible_calculations.extend(new);
            }
        }

        // TODO: If we have multiple calculations, try to filter out calculations that would hide other calculations. I.e., if we pick one of these calculations, would they hide all other calculations?

        if possible_calculations.len() > 1 {
            // We only keep calculations that are visible at least once in the bases
            possible_calculations.retain(|(inputs, calculation)| {
                let num_matched = self
                    .bases
                    .iter()
                    .filter(|(base, addr)| addr == &Addr::new(calculation.compute_from_gpregs(inputs, base)))
                    .count();

                if num_matched == 0 {
                    debug!("For {inputs:?} with calculation {calculation:?}: {num_matched} matched");
                }

                num_matched > 0
            });

            for _ in 0..1000 {
                if let Some(assignments) = self.find_differing_inputs(&possible_calculations, rng) {
                    let mut state = self.state_gen.randomize_new(rng).unwrap();
                    for &(reg, val) in assignments.iter() {
                        state.set_reg(A::reg(reg), Value::Num(val));
                    }

                    if self.state_gen.adapt(&mut state, false) {
                        // TODO: We sometimes have a state here that tries to map reserved addresses!
                        let any_not_covered = possible_calculations.iter().any(|(inputs, calculation)| {
                            let predicted_addr = Addr::new(calculation.compute_from_gpregs(inputs, &state));

                            state.memory().iter().all(|(addr, _, data)| {
                                !addr
                                    .into_area(data.len() as u64)
                                    .shares_page_with::<A>(&predicted_addr.into_area(1))
                            })
                        });

                        if any_not_covered {
                            let result = oracle.observe(&state);
                            debug!(
                                "Verifying calculations {possible_calculations:?} against ({assignments:X?}) {state:X?} -> {result:X?}"
                            );
                            possible_calculations.retain(|(inputs, computation)| {
                                let predicted_addr = Addr::new(computation.compute_from_gpregs(inputs, &state));

                                state.memory().iter().any(|(addr, _, data)| {
                                    addr.into_area(data.len() as u64)
                                        .shares_page_with::<A>(&predicted_addr.into_area(1))
                                }) || match result {
                                    Err(OracleError::MemoryAccess(found_addr)) if found_addr == predicted_addr => true,
                                    Err(OracleError::GeneralFault) => true,
                                    _ => false,
                                }
                            });
                            debug!("Calculations remaining: {possible_calculations:?}");

                            if possible_calculations.len() <= 1 {
                                break
                            }
                        }
                    }
                }
            }
        }

        let mut possible_calculations = possible_calculations
            .into_iter()
            .map(|(inputs, calculation)| {
                let num_matched = self
                    .bases
                    .iter()
                    .filter(|(base, addr)| addr == &Addr::new(calculation.compute_from_gpregs(&inputs, base)))
                    .count();

                let num_overlapping = self
                    .bases
                    .iter()
                    .filter(|(base, _)| {
                        let computed = Addr::new(calculation.compute_from_gpregs(&inputs, base)).into_area(1);
                        base.memory()
                            .iter()
                            .any(|(addr, _, data)| addr.into_area(data.len() as u64).overlaps_with(&computed))
                    })
                    .count();

                debug!("For {inputs:?} with calculation {calculation:?}: {num_matched} matched, {num_overlapping} overlapped");

                ((inputs, calculation), (num_matched, usize::MAX - num_overlapping))
            })
            .collect::<Vec<_>>();

        if let Some(max) = possible_calculations.iter().map(|(_, key)| key).max().cloned() {
            // if let Some((inputs, calculation)) = possible_calculations {
            possible_calculations.retain(|(_, key)| key == &max);
            debug!("Possible calculations: {possible_calculations:X?}");

            // TODO: Should we do something here?
            // if possible_calculations.len() > 0 {
            //     // todo!()
            // }

            let ((inputs, calculation), _) = possible_calculations.into_iter().next().unwrap();
            Some((
                Inputs::unsorted(
                    inputs
                        .into_iter()
                        .map(|reg| Source::Dest(Dest::Reg(A::reg(reg), Size::qword())))
                        .collect(),
                ),
                calculation,
            ))
        } else {
            warn!("No calculations");
            // if !assume_last_memory_access {
            // for (addr, base) in self.bases.iter() {
            //     println!("{addr:X?} => {base:X?}");
            // }
            // panic!();
            // }

            None
        }
    }

    fn find_differing_inputs<R: Rng>(
        &self, possible_calculations: &[(Vec<<A as Arch>::GpReg>, AddressComputation)], rng: &mut R,
    ) -> Option<Vec<(A::GpReg, u64)>> {
        let regs = {
            let mut v = possible_calculations
                .iter()
                .flat_map(|(inputs, _)| inputs.iter())
                .collect::<Vec<_>>();
            v.sort();
            v.dedup();

            v
        };

        let reg_indices = possible_calculations
            .iter()
            .map(|(inputs, _)| {
                inputs
                    .iter()
                    .map(|input| regs.iter().position(|&r| r == input).unwrap())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut values = vec![0u64; regs.len()];
        for _ in 0..100_000 {
            // Randomize all registers
            for (reg, value) in regs.iter().zip(values.iter_mut()) {
                *value = self.state_gen.randomize_register(rng, A::reg(**reg));
            }

            // Check if we would be able to distinguish between the different possibilities
            // TODO: Addresses must be on different page!
            let differs = possible_calculations
                .iter()
                .zip(reg_indices.iter())
                .map(|((_, calculation), reg_indices)| {
                    calculation.evaluate_from_iter(reg_indices.iter().map(|&index| values[index]))
                })
                .map(|x| (Addr::new(x).page::<A>(), true))
                .reduce(|(x1, b1), (x2, b2)| (x2, x1 != x2 || b1 || b2))?
                .1;

            if differs {
                // panic!("We could differentiate with {:?} = {:X?} for possibilities: {:?}", regs, values, possible_calculations);
                return Some(
                    regs.iter()
                        .zip(values.iter())
                        .map(|(reg, val)| (**reg, *val))
                        .collect::<Vec<_>>(),
                )
            }
        }

        None
    }

    pub fn infer_computation<O: Oracle<A>>(
        mut self, o: &mut O, rng: &mut Xoshiro256PlusPlus,
    ) -> Result<InferredComputation<A>, AccessAnalysisError<A>> {
        Ok(if self.directly_after_other_mapping >= self.bases.len() {
            let other_mapping = self.other_mapping.unwrap();

            // Figure out the offset
            let offset = self
                .bases
                .iter()
                .map(|(base, addr)| {
                    let other_addr = base.memory().get(other_mapping).0.as_u64();

                    addr.as_u64().wrapping_sub(other_addr) as i64
                })
                .try_fold(None, |acc, offset| match acc {
                    Some(prev) => {
                        if prev == offset {
                            Ok(Some(prev))
                        } else {
                            Err(())
                        }
                    },
                    None => Ok(Some(offset)),
                })
                .map_err(|_| AccessAnalysisError::AccessNotAnalyzable(other_mapping))?
                .unwrap();

            let inputs = self.accesses.memory[other_mapping].inputs.clone();
            let mut calculation = self.accesses.memory[other_mapping].calculation;
            calculation.offset += offset;

            InferredComputation {
                inputs,
                calculation,
                bases: self.bases,
            }
        } else {
            // TODO: Share test-cases between assume_last_memory_access=true and assume_last_memory_access=false below
            // If we don't expect any more memory accesses we can make more assumptions about the access,
            // but we should only spend time on that if we don't expect any more accesses.
            if !self.more_memory_accesses_expected {
                let stopwatch = Instant::now();
                let RegisterCandidates {
                    registers,
                    priority_bases,
                    extra_bases,
                } = self.find_register_candidates(o, rng, true)?;
                self.bases = {
                    info!(
                        "Discovered {} extra bases while finding register candidates",
                        extra_bases.len()
                    );
                    let mut v = priority_bases;
                    let mut bases = self.bases;
                    v.append(&mut bases);
                    v.extend(extra_bases);
                    v
                };

                // We will almost always find a calculation here. Only instructions that access >1 memory location might fail here.
                info!(
                    "Candidate registers identified as: {:?} in {}ms",
                    registers,
                    stopwatch.elapsed().as_millis()
                );
                if let Some(result) = self.find_calculation(&registers, rng, o, true) {
                    return Ok(InferredComputation {
                        inputs: result.0,
                        calculation: result.1,
                        bases: self.bases,
                    });
                }
            }

            let stopwatch = Instant::now();
            let RegisterCandidates {
                registers,
                priority_bases,
                extra_bases,
            } = self.find_register_candidates(o, rng, false)?;
            self.bases = {
                info!(
                    "Discovered {} extra bases while finding register candidates",
                    extra_bases.len()
                );
                let mut v = priority_bases;
                let mut bases = self.bases;
                v.append(&mut bases);
                v.extend(extra_bases);
                v
            };

            info!(
                "Candidate registers (assuming multiple memory accesses) identified as: {:?} in {}ms",
                registers,
                stopwatch.elapsed().as_millis()
            );
            if let Some(result) = self.find_calculation(&registers, rng, o, false) {
                InferredComputation {
                    inputs: result.0,
                    calculation: result.1,
                    bases: self.bases,
                }
            } else {
                error!(
                    "Could not find a good calculation for new access after {:?}, instruction {:X}",
                    self.accesses, self.accesses.instr
                );
                return Err(AccessAnalysisError::Randomization(RandomizationError::Unsatisfiable(
                    self.accesses.len(),
                )));
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::accesses::computation::OffsetConstraint;

    #[test]
    pub fn offset_constraints_and() {
        let address_on_page1 = OffsetConstraint::fixed(0x1234);
        let page1 = OffsetConstraint {
            start: 0x1000,
            length: 0x1000,
        };
        assert_eq!(address_on_page1.intersect(page1).unwrap(), address_on_page1);
        assert_eq!(page1.intersect(address_on_page1).unwrap(), address_on_page1);

        let zero = OffsetConstraint::fixed(0);
        let all = OffsetConstraint::ALL;
        assert_eq!(zero.intersect(all).unwrap(), zero);
        assert_eq!(all.intersect(zero).unwrap(), zero);

        assert_eq!(all.intersect(page1).unwrap(), page1);
        assert_eq!(page1.intersect(all).unwrap(), page1);

        let overlapping_page12 = OffsetConstraint {
            start: 0x1800,
            length: 0x2800,
        };

        assert_eq!(
            overlapping_page12.intersect(page1).unwrap(),
            OffsetConstraint {
                start: 0x1800,
                length: 0x800,
            }
        );
    }

    #[test]
    pub fn offset_constraints_and2() {
        let address_on_page1 = OffsetConstraint::fixed(0x2400);
        let page1 = OffsetConstraint {
            start: 0x1400,
            length: 0x1000,
        };
        let page2 = OffsetConstraint {
            start: 0x1400,
            length: 0xfff,
        };
        assert_eq!(address_on_page1.intersect(page1).unwrap(), address_on_page1);
        assert_eq!(page1.intersect(address_on_page1).unwrap(), address_on_page1);
        assert_eq!(address_on_page1.intersect(page2), None);
        assert_eq!(page2.intersect(address_on_page1), None);
    }
}
