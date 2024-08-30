use std::fmt;
use std::fmt::Debug;

use log::trace;

use crate::instr::{merge_filters, FilterBit, Instruction, InstructionFilter};
use crate::utils::minisat::{SatSolver, SolverResult, Term};

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ExtendedFilter {
    pub(crate) matching: InstructionFilter,
    pub(crate) nonmatching: Vec<InstructionFilter>,
    matching_instr: Instruction,
}

impl Debug for ExtendedFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} except {:?}", self.matching, self.nonmatching)
    }
}

impl ExtendedFilter {
    pub fn new_ex(
        mut matching: InstructionFilter, mut nonmatching: Vec<InstructionFilter>, merge: bool,
    ) -> Option<ExtendedFilter> {
        loop {
            let mut changed = false;
            if nonmatching.iter().any(|f| f.covers(&matching)) {
                return None
            }

            let len_before = nonmatching.len();
            nonmatching.retain(|f| f.overlaps(&matching));
            trace!("Remaining nonmatching: {nonmatching:?}");
            changed |= len_before != nonmatching.len();

            if merge {
                let len_before = nonmatching.len();
                nonmatching = merge_filters(nonmatching);
                changed |= len_before != nonmatching.len();
            }

            for nm in nonmatching.iter() {
                if let Some(f) = matching.try_exclude(nm) {
                    trace!("Excluded {nm:?} from {matching:?} = {f:?}");
                    matching = f;
                    changed = true;
                }
            }

            if !changed {
                break
            }
        }

        // Check if there is an instruction I which matches matching, but none of nonmatching.
        let mut sat = SatSolver::new(matching.bit_len());
        sat.and_conjunction(Self::as_terms(&matching));
        for f in nonmatching.iter() {
            sat.and_not_conjunction(Self::as_terms(f));
        }

        trace!("Checking if matching={matching:?}, nonmatching={nonmatching:?} is inhabitable via SAT solver");
        match sat.solve() {
            SolverResult::Sat(conf) => {
                let mut matching_instr = Instruction::new(&vec![0; matching.bit_len() / 8]);

                for (index, bit) in conf.iter().enumerate() {
                    matching_instr = matching_instr.with_nth_bit_from_left(index, bit as u8);
                }

                let extended_filter = ExtendedFilter {
                    matching,
                    nonmatching,
                    matching_instr,
                };

                debug_assert!(extended_filter.matches(&matching_instr));

                Some(extended_filter)
            },
            SolverResult::Unsat => None,
        }
    }

    fn as_terms(filter: &InstructionFilter) -> impl Iterator<Item = Term> + '_ {
        (0..filter.bit_len()).flat_map(|n| match filter.nth_bit_from_left(n) {
            FilterBit::Is0 => Some(Term::ff(n.try_into().unwrap())),
            FilterBit::Is1 => Some(Term::tt(n.try_into().unwrap())),
            FilterBit::Wildcard => None,
        })
    }

    pub fn matching_instr(&self) -> Instruction {
        self.matching_instr
    }

    pub fn matches(&self, instr: &Instruction) -> bool {
        self.matching.matches(instr) && !self.nonmatching.iter().any(|nm| nm.matches(instr))
    }
}

#[cfg(test)]
mod tests {
    use super::ExtendedFilter;
    use crate::instr::InstructionFilter;

    #[test]
    pub fn extended_filter_new() {
        let matching = InstructionFilter::parse("0100_0_0 01110110 00000000");

        let nonmatching = vec![
            InstructionFilter::parse("01000__0 0111001_ ________"),
            InstructionFilter::parse("0100_0__ 01111010 000_____"),
            InstructionFilter::parse("0100____ 0111110_ ________"),
            InstructionFilter::parse("0100____ 0111001_ ________"),
            InstructionFilter::parse("0100____ 0111101_ ________"),
            InstructionFilter::parse("0100____ 0111100_ ________"),
            InstructionFilter::parse("01000_0_ 01111111 00_____0"),
            InstructionFilter::parse("0100_0__ 0111111_ _______0"),
            InstructionFilter::parse("0100___0 0111000_ ________"),
            InstructionFilter::parse("0100____ 0111010_ ________"),
            InstructionFilter::parse("01000__0 01110100 00_____0"),
            InstructionFilter::parse("0100____ 0111111_ ________"),
            InstructionFilter::parse("01000000 01111000 00_____0"),
            InstructionFilter::parse("0100____ 0111000_ ________"),
        ];

        let filter = ExtendedFilter::new_ex(matching, nonmatching, true).unwrap();
        println!("{filter:?}");
    }

    #[test]
    pub fn extended_filter_new_nonmatching_merge() {
        let matching = InstructionFilter::parse("10000011 00110101 ________ ________ ___1____ ________ ________");

        let nonmatching = vec![
            InstructionFilter::parse("10000011 00110101 1_______ ________ ________ ________ ________"),
            InstructionFilter::parse("10000011 0011_101 ________ ________ ________ ________ 00000000"),
            InstructionFilter::parse("10000011 00110101 001_____ ________ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 01______ ________ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ ________ 0_______"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ _______1 ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ ______10 ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ _____100 ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ ____1___ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ ___1____ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ __1_____ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ _1______ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ________ 1_______ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ _______1 ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ______1_ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ _____1__ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ ____1___ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ __1_____ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ _1______ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ________ 1_______ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ _______1 ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ______1_ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ _____1__ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ____1___ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ ___1____ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ __1_____ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ _1______ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ________ 1_______ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 _______1 ________ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ______1_ ________ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 _____1__ ________ ________ ________ ________"),
            InstructionFilter::parse("10000011 00110101 ___1____ ________ ________ ________ ________"),
        ];

        let filter = ExtendedFilter::new_ex(matching, nonmatching, true).unwrap();
        assert_eq!(
            filter.matching,
            InstructionFilter::parse("10000011 00110101 0000_000 00000000 00010000 00000000 1_______")
        );
        assert_eq!(filter.nonmatching, vec![]);
    }
}
