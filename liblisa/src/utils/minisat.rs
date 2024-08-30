use std::collections::HashSet;
use std::fmt;
use std::ops::Not;

use log::{debug, trace};

use crate::utils::bitmap::GrowingBitmap;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(u8);

impl fmt::Debug for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

impl VarId {
    pub fn index(self) -> usize {
        self.into()
    }
}

impl From<VarId> for usize {
    fn from(value: VarId) -> Self {
        value.0 as usize
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Term {
    var: VarId,
    value: bool,
}

impl Term {
    pub fn new(var: VarId, value: bool) -> Term {
        Term {
            var,
            value,
        }
    }

    pub fn tt(var: u8) -> Term {
        Term::new(VarId(var), true)
    }

    pub fn ff(var: u8) -> Term {
        Term::new(VarId(var), false)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.value {
            write!(f, "{:?}", self.var)
        } else {
            write!(f, "!{:?}", self.var)
        }
    }
}

impl Not for Term {
    type Output = Term;

    fn not(self) -> Self::Output {
        Term {
            var: self.var,
            value: !self.value,
        }
    }
}

#[derive(Debug)]
struct Conjunction(Vec<Term>);

#[derive(Debug)]
struct Disjunction(Vec<Term>);

/// A custom "SAT"-solver, because other Rust libraries require CNF form, which isn't great in our case.
/// Delegating to a SAT solver in an external process is too slow.
///
/// Represents forAll(terms) & forAll(disjunctions) & exists(disjunctionOfConjunctions)
#[derive(Debug)]
pub struct SatSolver {
    terms: Vec<Option<bool>>,
    disjunctions: Vec<Disjunction>,
    disjunction_of_conjunctions: Vec<Conjunction>,
    has_disjunction_of_conjunctions: bool,
    unsat: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SolverResult {
    Sat(GrowingBitmap),
    Unsat,
}

impl SatSolver {
    pub fn new(max_terms: usize) -> Self {
        Self {
            terms: vec![None; max_terms],
            disjunctions: Vec::new(),
            disjunction_of_conjunctions: Vec::new(),
            has_disjunction_of_conjunctions: false,
            unsat: false,
        }
    }

    pub fn and_conjunction(&mut self, items: impl Iterator<Item = Term>) {
        if self.unsat {
            return;
        }

        for item in items {
            if self.terms[item.var.index()] == Some(!item.value) {
                self.unsat = true;
                return;
            } else {
                self.terms[item.var.index()] = Some(item.value);
            }
        }
    }

    pub fn and_not_conjunction(&mut self, items: impl Iterator<Item = Term>) {
        // Applying: !(a & b & !c) = !a | !b | c
        self.disjunctions.push(Disjunction(items.map(|term| !term).collect()));
    }

    fn check_disjunctions<T>(
        &self, assumptions: &mut [Option<bool>], found: impl FnMut(&[Option<bool>]) -> Option<T>,
    ) -> Option<T> {
        fn check_disjunctions_internal<T>(
            disjunctions: &[Disjunction], assumptions: &mut [Option<bool>], mut found: impl FnMut(&[Option<bool>]) -> Option<T>,
        ) -> Option<T> {
            if disjunctions.is_empty() {
                return found(assumptions);
            }

            let mut stack: Vec<(usize, Option<usize>)> = vec![(0, None)];

            while let Some((depth, term_index)) = stack.last_mut() {
                let depth = *depth;
                trace!("At depth {depth}, term_index={term_index:?}");
                let disjunction = &disjunctions[depth];
                let num_done = if let Some(term_index) = term_index {
                    let last_index = disjunction.0[*term_index].var.index();
                    trace!("Resetting assumptions[{last_index}] = -");
                    assumptions[last_index] = None;

                    *term_index + 1
                } else {
                    0
                };

                let next = disjunction
                    .0
                    .iter()
                    .enumerate()
                    .skip(num_done)
                    .find(|(_, t)| assumptions[t.var.index()].is_none());

                trace!("next = {next:?}");

                if let Some((new_index, new_term)) = next {
                    *term_index = Some(new_index);
                    let index = new_term.var.index();
                    debug_assert!(assumptions[index].is_none());

                    trace!("Setting assumptions[{index}] = {}", new_term.value);
                    assumptions[index] = Some(new_term.value);

                    let next_depth = disjunctions.iter().enumerate().skip(depth + 1).find(|(_, disjunction)| {
                        !disjunction
                            .0
                            .iter()
                            .any(|term| assumptions[term.var.index()] == Some(term.value))
                    });

                    if let Some((next_depth, _)) = next_depth {
                        stack.push((next_depth, None));
                    } else if let Some(result) = found(assumptions) {
                        return Some(result)
                    }
                } else {
                    stack.pop();
                }
            }

            None
        }

        trace!("Checking disjunctions with these assumptions: {assumptions:?}");

        check_disjunctions_internal(&self.disjunctions, assumptions, found)
    }

    pub fn solve(&mut self) -> SolverResult {
        self.solve_with(|solution| Some(SolverResult::Sat(solution.iter().map(|v| v.unwrap_or_default()).collect())))
            .unwrap_or(SolverResult::Unsat)
    }

    pub fn solve_with<T>(&mut self, mut found: impl FnMut(&[Option<bool>]) -> Option<T>) -> Option<T> {
        // if self.terms says a=True, then a term a=False will obviously never be true
        self.disjunction_of_conjunctions
            .retain(|conj| conj.0.iter().all(|term| self.terms[term.var.index()] != Some(!term.value)));
        for disjunction in self.disjunctions.iter_mut() {
            disjunction.0.retain(|term| self.terms[term.var.index()] != Some(!term.value));
        }

        // TODO: If any of the disjunctions is a subset of another disjunction, we can remove the bigger disjunction.

        // Solve the most constraining disjunctions first.
        self.disjunctions.sort_by_key(|d| d.0.len());

        debug!("Running solve() on {self:#?}");

        if !self.has_disjunction_of_conjunctions {
            let mut assumptions = self.terms.clone();
            if let Some(result) = self.check_disjunctions(&mut assumptions, &mut found) {
                return Some(result)
            }
        } else {
            let mut seen = HashSet::new();
            for conjunction in self.disjunction_of_conjunctions.iter() {
                let mut assumptions = self.terms.clone();
                for term in conjunction.0.iter() {
                    // Because of the checks above, this will never overwrite Some(true) with Some(false) or vice versa.
                    assumptions[term.var.index()] = Some(term.value);
                }

                // TODO: How often do we get hits here? Is it worth keeping track?
                if !seen.contains(&assumptions) {
                    seen.insert(assumptions.clone());

                    if let Some(result) = self.check_disjunctions(&mut assumptions, &mut found) {
                        return Some(result)
                    }
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::{SatSolver, SolverResult, Term};

    #[test]
    pub fn simple_sat() {
        let mut solver = SatSolver::new(4);
        solver.and_conjunction([Term::tt(0), Term::ff(2)].into_iter());
        solver.and_not_conjunction([Term::tt(0), Term::tt(1), Term::ff(2), Term::ff(3)].into_iter());

        assert_eq!(
            solver.solve(),
            SolverResult::Sat([true, false, false, false,].into_iter().collect())
        );
    }

    #[test]
    pub fn big_formula() {
        let mut solver = SatSolver::new(88);
        solver.and_conjunction(
            [
                Term::tt(0),
                Term::tt(1),
                Term::ff(2),
                Term::ff(3),
                Term::ff(4),
                Term::tt(5),
                Term::ff(6),
                Term::ff(7),
                Term::ff(8),
                Term::ff(9),
                Term::ff(11),
                Term::ff(12),
                Term::ff(13),
                Term::tt(14),
                Term::tt(15),
                Term::tt(17),
                Term::tt(18),
                Term::tt(19),
                Term::tt(20),
                Term::tt(21),
                Term::ff(22),
                Term::tt(23),
                Term::ff(24),
                Term::ff(25),
                Term::ff(26),
                Term::ff(27),
                Term::tt(28),
                Term::ff(29),
                Term::ff(30),
                Term::ff(31),
                Term::ff(32),
                Term::ff(33),
                Term::tt(34),
                Term::ff(35),
                Term::ff(36),
                Term::tt(37),
                Term::ff(38),
                Term::ff(39),
                Term::tt(45),
                Term::ff(46),
                Term::tt(47),
                Term::ff(48),
                Term::ff(54),
                Term::ff(55),
                Term::ff(56),
                Term::ff(57),
                Term::ff(58),
                Term::ff(62),
                Term::ff(70),
                Term::ff(81),
                Term::ff(83),
                Term::tt(84),
                Term::ff(85),
                Term::tt(86),
                Term::ff(87),
            ]
            .into_iter(),
        );

        solver.and_not_conjunction(
            [
                Term::ff(41),
                Term::ff(42),
                Term::ff(43),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(60),
                Term::ff(64),
                Term::ff(65),
                Term::ff(66),
                Term::ff(67),
                Term::ff(68),
                Term::tt(69),
                Term::ff(71),
                Term::tt(75),
                Term::tt(76),
                Term::ff(77),
                Term::ff(78),
                Term::tt(79),
                Term::ff(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(42), Term::tt(43), Term::tt(44)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(52),
                Term::ff(53),
                Term::ff(67),
                Term::tt(68),
                Term::tt(72),
                Term::tt(73),
                Term::ff(74),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(43),
                Term::ff(51),
                Term::ff(52),
                Term::tt(59),
                Term::ff(60),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(41),
                Term::ff(42),
                Term::ff(44),
                Term::ff(53),
                Term::ff(59),
                Term::ff(60),
                Term::ff(64),
                Term::ff(65),
                Term::ff(66),
                Term::tt(76),
                Term::ff(77),
                Term::tt(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(41),
                Term::ff(42),
                Term::ff(61),
                Term::ff(63),
                Term::ff(67),
                Term::ff(74),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::tt(42), Term::ff(43), Term::ff(44)].into_iter());
        solver.and_not_conjunction([Term::ff(42), Term::ff(44), Term::ff(66), Term::ff(71)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(49),
                Term::ff(50),
                Term::ff(71),
                Term::tt(72),
                Term::ff(77),
                Term::tt(78),
                Term::ff(79),
                Term::tt(80),
                Term::ff(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(40), Term::ff(44), Term::ff(61), Term::ff(75), Term::tt(76)].into_iter());
        solver.and_not_conjunction([Term::tt(43), Term::ff(44)].into_iter());
        solver.and_not_conjunction([Term::tt(42), Term::tt(44)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(41),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(59),
                Term::ff(60),
                Term::ff(68),
                Term::ff(69),
                Term::tt(71),
                Term::ff(72),
                Term::tt(73),
                Term::ff(78),
                Term::tt(79),
                Term::tt(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(44),
                Term::ff(53),
                Term::ff(59),
                Term::ff(60),
                Term::ff(61),
                Term::tt(77),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(67),
                Term::tt(73),
                Term::tt(74),
                Term::ff(75),
                Term::tt(76),
                Term::tt(77),
                Term::ff(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(44),
                Term::ff(49),
                Term::ff(65),
                Term::ff(66),
                Term::tt(67),
                Term::ff(75),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(41),
                Term::ff(42),
                Term::ff(43),
                Term::ff(44),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::tt(61),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(41),
                Term::ff(44),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(59),
                Term::tt(63),
                Term::tt(64),
                Term::tt(73),
                Term::ff(78),
                Term::tt(79),
                Term::ff(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(40),
                Term::ff(43),
                Term::ff(49),
                Term::ff(50),
                Term::ff(65),
                Term::ff(66),
                Term::tt(77),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(40), Term::ff(44), Term::tt(60), Term::tt(65), Term::ff(80)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(42),
                Term::ff(43),
                Term::ff(44),
                Term::ff(65),
                Term::tt(66),
                Term::tt(67),
                Term::ff(71),
                Term::tt(75),
                Term::tt(76),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(44),
                Term::tt(63),
                Term::ff(69),
                Term::ff(71),
                Term::ff(72),
                Term::ff(73),
                Term::ff(74),
                Term::ff(75),
                Term::tt(76),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(49),
                Term::ff(50),
                Term::ff(65),
                Term::ff(76),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(42), Term::ff(53), Term::ff(78), Term::tt(79), Term::tt(80)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(43),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(59),
                Term::ff(60),
                Term::ff(61),
                Term::ff(63),
                Term::ff(64),
                Term::ff(65),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(43),
                Term::ff(49),
                Term::ff(50),
                Term::tt(63),
                Term::tt(64),
                Term::tt(71),
                Term::tt(72),
                Term::tt(73),
                Term::tt(74),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(42),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(59),
                Term::tt(73),
                Term::ff(74),
                Term::ff(75),
                Term::tt(76),
                Term::ff(77),
                Term::tt(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(44),
                Term::ff(49),
                Term::tt(60),
                Term::tt(61),
                Term::ff(66),
                Term::tt(74),
                Term::ff(75),
                Term::ff(80),
                Term::ff(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(43),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(59),
                Term::ff(66),
                Term::ff(67),
                Term::ff(75),
                Term::ff(76),
                Term::tt(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(61),
                Term::tt(67),
                Term::tt(76),
                Term::ff(77),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(42), Term::ff(43)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(41),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(59),
                Term::ff(64),
                Term::ff(69),
                Term::ff(74),
                Term::ff(75),
                Term::tt(76),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(43),
                Term::ff(49),
                Term::ff(50),
                Term::ff(59),
                Term::ff(60),
                Term::tt(71),
                Term::ff(72),
                Term::tt(73),
                Term::tt(74),
                Term::ff(78),
                Term::tt(79),
                Term::ff(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(41),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(59),
                Term::ff(60),
                Term::ff(61),
                Term::ff(63),
                Term::ff(64),
                Term::tt(65),
                Term::ff(66),
                Term::tt(67),
                Term::tt(68),
                Term::ff(69),
                Term::ff(71),
                Term::tt(72),
                Term::tt(73),
                Term::ff(78),
                Term::ff(79),
                Term::tt(80),
                Term::tt(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(42),
                Term::ff(44),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::tt(66),
                Term::ff(72),
                Term::ff(77),
                Term::tt(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(52),
                Term::ff(60),
                Term::tt(61),
                Term::tt(63),
                Term::ff(64),
                Term::tt(65),
                Term::tt(66),
                Term::ff(67),
                Term::ff(71),
                Term::ff(72),
                Term::tt(73),
                Term::tt(74),
                Term::tt(75),
                Term::ff(76),
                Term::ff(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(42), Term::ff(49), Term::ff(50), Term::ff(63), Term::ff(69)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(44),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::tt(60),
                Term::tt(61),
                Term::tt(63),
                Term::ff(64),
                Term::tt(65),
                Term::ff(66),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(60),
                Term::ff(61),
                Term::tt(63),
                Term::tt(64),
                Term::ff(69),
                Term::tt(71),
                Term::tt(72),
                Term::ff(76),
                Term::ff(77),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(40),
                Term::ff(43),
                Term::ff(44),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::tt(66),
                Term::ff(67),
                Term::tt(68),
                Term::tt(69),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(61),
                Term::ff(63),
                Term::ff(64),
                Term::tt(65),
                Term::ff(66),
                Term::ff(67),
                Term::tt(68),
                Term::ff(69),
                Term::tt(74),
                Term::tt(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(42), Term::tt(67)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(59),
                Term::ff(60),
                Term::ff(71),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
                Term::tt(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(61),
                Term::ff(69),
                Term::ff(71),
                Term::ff(75),
                Term::ff(76),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
                Term::ff(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(59),
                Term::ff(60),
                Term::ff(61),
                Term::ff(63),
                Term::tt(64),
                Term::ff(72),
                Term::ff(78),
                Term::ff(79),
                Term::tt(80),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(42),
                Term::ff(43),
                Term::ff(64),
                Term::ff(72),
                Term::ff(73),
                Term::ff(77),
                Term::ff(78),
                Term::tt(79),
                Term::tt(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(49), Term::ff(53), Term::tt(69), Term::tt(79), Term::tt(82)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(40),
                Term::ff(44),
                Term::ff(67),
                Term::ff(68),
                Term::ff(69),
                Term::ff(71),
                Term::ff(72),
                Term::ff(73),
                Term::ff(74),
                Term::ff(75),
                Term::ff(76),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
                Term::ff(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(49),
                Term::ff(59),
                Term::ff(60),
                Term::ff(61),
                Term::ff(68),
                Term::ff(79),
                Term::tt(80),
                Term::ff(82),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction([Term::ff(10), Term::ff(43), Term::ff(73)].into_iter());
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::ff(52),
                Term::ff(53),
                Term::ff(59),
                Term::ff(63),
                Term::tt(64),
                Term::tt(65),
                Term::ff(66),
                Term::ff(67),
                Term::ff(74),
                Term::ff(75),
                Term::ff(76),
                Term::ff(77),
                Term::ff(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(10),
                Term::ff(64),
                Term::ff(65),
                Term::tt(69),
                Term::tt(74),
                Term::ff(75),
                Term::tt(76),
                Term::ff(77),
                Term::tt(78),
                Term::ff(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(42),
                Term::ff(49),
                Term::ff(53),
                Term::tt(60),
                Term::tt(61),
                Term::ff(67),
                Term::ff(68),
                Term::tt(69),
                Term::ff(71),
                Term::ff(72),
                Term::tt(73),
                Term::ff(74),
                Term::tt(75),
                Term::ff(76),
                Term::ff(77),
                Term::ff(78),
                Term::tt(79),
            ]
            .into_iter(),
        );
        solver.and_not_conjunction(
            [
                Term::ff(40),
                Term::ff(41),
                Term::ff(42),
                Term::ff(49),
                Term::ff(50),
                Term::ff(51),
                Term::tt(59),
                Term::ff(60),
                Term::ff(61),
                Term::ff(63),
                Term::ff(64),
                Term::ff(65),
                Term::tt(69),
                Term::ff(71),
                Term::ff(72),
                Term::ff(77),
                Term::tt(78),
                Term::ff(79),
            ]
            .into_iter(),
        );

        assert_eq!(solver.solve(), SolverResult::Unsat);
    }

    #[test]
    pub fn multiple_disjunctions_with_same_terms() {
        // formula: !(!1 & !2 & !3) & !(!2 & 3 & 4) & !(2 & !3 & !4) & !(3 & !4) & !(2 & 4) & !(2 & 3)
        // = (1 | 2 | 3) & (2 | !3 | !4) & (!2 | 3 | 4) & (!3 | 4) & (!2 | !4) & (!2 | !3)
        // (unsatisfiable)
        let mut solver = SatSolver::new(5);
        solver.and_not_conjunction([Term::ff(1), Term::ff(2), Term::ff(3)].into_iter());
        solver.and_not_conjunction([Term::ff(2), Term::tt(3), Term::tt(4)].into_iter());
        solver.and_not_conjunction([Term::tt(2), Term::ff(3), Term::ff(4)].into_iter());
        solver.and_not_conjunction([Term::tt(3), Term::ff(4)].into_iter());
        solver.and_not_conjunction([Term::tt(2), Term::tt(4)].into_iter());
        solver.and_not_conjunction([Term::ff(2), Term::ff(3)].into_iter());

        assert_eq!(solver.solve(), SolverResult::Unsat);
    }
}
