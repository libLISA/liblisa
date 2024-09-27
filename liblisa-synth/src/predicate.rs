use std::collections::HashSet;
use std::fmt::{self, Display};
use std::mem::swap;

use liblisa::semantics::default::computation::{
    Arg, ArgEncoding, AsComputationRef, ExpressionComputation, OutputEncoding, SynthesizedComputation,
};
use liblisa::semantics::default::ops::Op;
use liblisa::semantics::default::{Expression, FALSE};
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::value::{AsValue, OwnedValue};

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Predicate {
        negate: bool,
        predicate: ExpressionComputation,
    },
    CaseMatch {
        negate: bool,
        input_indices: Vec<(usize, IoType)>,
        cases: Vec<Vec<OwnedValue>>,
    },
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Predicate {
                negate,
                predicate,
            } => f
                .debug_struct("Predicate")
                .field("negate", negate)
                .field("predicate", &predicate.display(ARG_NAMES).to_string())
                .finish(),
            Self::CaseMatch {
                negate,
                input_indices,
                cases,
            } => f
                .debug_struct("CaseMatch")
                .field("negate", negate)
                .field("input_indices", input_indices)
                .field("cases", cases)
                .finish(),
        }
    }
}

impl Term {
    fn fold(&self) -> SynthesizedComputation {
        match self {
            Term::Predicate {
                negate,
                predicate,
            } => {
                if *negate {
                    predicate.not()
                } else {
                    predicate.to_synthesized_computation()
                }
            },
            Term::CaseMatch {
                negate,
                input_indices,
                cases,
            } => {
                if cases.is_empty() {
                    if *negate {
                        SynthesizedComputation::always_true()
                    } else {
                        SynthesizedComputation::always_false()
                    }
                } else {
                    let args = input_indices
                        .iter()
                        .map(|&(index, ty)| Arg::Input {
                            index: index.try_into().unwrap(),
                            num_bits: ty.num_bits().try_into().unwrap(),
                            encoding: ArgEncoding::UnsignedBigEndian,
                        })
                        .collect::<Vec<_>>();
                    let consts = cases
                        .iter()
                        .flat_map(|case| {
                            case.iter().zip(input_indices.iter()).map(|(val, (_, ty))| {
                                Arg::Input {
                                    index: 0,
                                    num_bits: ty.num_bits().try_into().unwrap(),
                                    encoding: ArgEncoding::UnsignedBigEndian,
                                }
                                .interpret_inputs(&[val.clone()], &[])
                            })
                        })
                        .collect::<Vec<_>>();

                    let mut ops = Vec::new();

                    for index in 0..cases.len() {
                        let const_base_index = args.len() + index * args.len();

                        for arg_index in 0..args.len() {
                            ops.extend([
                                Op::Hole(arg_index.try_into().unwrap()),
                                Op::Hole((const_base_index + arg_index).try_into().unwrap()),
                                Op::Sub,
                                Op::IsZero,
                            ]);
                        }

                        for _ in 0..args.len() - 1 {
                            ops.push(Op::And);
                        }
                    }

                    // TODO: Can we do these ORs earlier to reduce the depth of the expression tree?
                    for _ in 0..cases.len() - 1 {
                        ops.push(Op::Or);
                    }

                    let expr = Expression::new(ops);
                    let args = args
                        .into_iter()
                        .chain((0..consts.len()).map(|index| Arg::Const(index.try_into().unwrap())))
                        .collect::<Vec<_>>();

                    let t = SynthesizedComputation::new(
                        expr,
                        args,
                        consts,
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer {
                            num_bits: 1,
                        },
                    );
                    if *negate {
                        t.not()
                    } else {
                        t
                    }
                }
            },
        }
    }

    pub fn evaluate<V: AsValue>(&self, inputs: &[V]) -> bool {
        match self {
            Term::Predicate {
                negate,
                predicate,
            } => predicate.evaluate(inputs).interpret_as_bool() ^ negate,
            Term::CaseMatch {
                negate,
                input_indices,
                cases,
            } => {
                cases.iter().any(|case| {
                    input_indices
                        .iter()
                        .zip(case.iter())
                        .all(|((input_index, _), val)| inputs[*input_index].as_value() == val.as_value())
                }) != *negate
            },
        }
    }

    pub fn used_input_indices(&self) -> Vec<usize> {
        match self {
            Term::Predicate {
                predicate, ..
            } => predicate.used_input_indices(),
            Term::CaseMatch {
                input_indices, ..
            } => input_indices.iter().map(|&(index, _)| index).collect(),
        }
    }

    pub fn remap_inputs(&mut self, map: &[Option<usize>]) {
        match self {
            Term::Predicate {
                predicate, ..
            } => predicate.remap_inputs(map),
            Term::CaseMatch {
                input_indices, ..
            } => {
                for (index, _) in input_indices.iter_mut() {
                    *index = map[*index].expect("Cannot remove input in use");
                }
            },
        }
    }

    fn negate(self) -> Term {
        match self {
            Term::Predicate {
                negate,
                predicate,
            } => Term::Predicate {
                negate: !negate,
                predicate,
            },
            Term::CaseMatch {
                negate,
                input_indices,
                cases,
            } => Term::CaseMatch {
                negate: !negate,
                input_indices,
                cases,
            },
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Predicate {
                negate,
                predicate,
            } => {
                if *negate {
                    write!(f, "![{}]", predicate.display(ARG_NAMES))
                } else {
                    write!(f, "[{}]", predicate.display(ARG_NAMES))
                }
            },
            Term::CaseMatch {
                negate,
                input_indices,
                cases,
            } => {
                if *negate {
                    write!(
                        f,
                        "not(match_inputs{:?}({cases:X?}))",
                        input_indices.iter().map(|&(index, _)| index).collect::<Vec<_>>()
                    )
                } else {
                    write!(
                        f,
                        "match_inputs{:?}({cases:X?})",
                        input_indices.iter().map(|&(index, _)| index).collect::<Vec<_>>()
                    )
                }
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Conjunction {
    terms: Vec<Term>,
}

impl std::fmt::Display for Conjunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.terms.is_empty() {
            write!(f, "true")?;
        } else {
            for (index, item) in self.terms.iter().enumerate() {
                write!(f, "{item}")?;
                if index < self.terms.len() - 1 {
                    write!(f, " & ")?;
                }
            }
        }

        Ok(())
    }
}

impl Conjunction {
    pub fn new(terms: Vec<Term>) -> Self {
        Self {
            terms,
        }
    }

    pub fn fold(&self) -> SynthesizedComputation {
        if self.terms.is_empty() {
            SynthesizedComputation::always_true()
        } else {
            let items = self
                .terms
                .iter()
                .cloned()
                .collect::<HashSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let first = items[0].fold();
            items[1..].iter().fold(first, |acc, term| acc.and(&term.fold()))
        }
    }

    pub fn evaluate<V: AsValue>(&self, inputs: &[V]) -> bool {
        self.terms.iter().all(|item| item.evaluate(inputs))
    }

    pub fn always_true() -> Conjunction {
        Conjunction::new(Vec::new())
    }

    pub fn always_false() -> Conjunction {
        Conjunction {
            terms: vec![Term::Predicate {
                predicate: ExpressionComputation::new(
                    Expression::new(vec![Op::Const(0)]),
                    Default::default(),
                    OutputEncoding::UnsignedBigEndian,
                    IoType::Integer {
                        num_bits: 1,
                    },
                ),
                negate: false,
            }],
        }
    }

    pub fn negate(self) -> Disjunction {
        Disjunction::new(
            self.terms
                .into_iter()
                .map(|term| Conjunction::new(vec![term.negate()]))
                .collect(),
        )
    }

    pub fn and_also(&mut self, con: Conjunction) {
        self.terms.extend(con.terms);
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn push(&mut self, term: Term) {
        self.terms.push(term)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Term> {
        self.terms.iter()
    }

    pub fn retain_mut(&mut self, predicate: impl FnMut(&mut Term) -> bool) {
        self.terms.retain_mut(predicate)
    }

    pub fn and_also_term(&mut self, term: Term) {
        self.terms.push(term)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Disjunction {
    conjunctions: Vec<Conjunction>,
}

impl std::fmt::Display for Disjunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.conjunctions.is_empty() {
            write!(f, "false")
        } else {
            for (index, item) in self.conjunctions.iter().enumerate() {
                write!(f, "{item}")?;
                if index < self.conjunctions.len() - 1 {
                    write!(f, " | ")?;
                }
            }

            Ok(())
        }
    }
}

impl From<Conjunction> for Disjunction {
    fn from(value: Conjunction) -> Self {
        Self::new(vec![value])
    }
}

impl Disjunction {
    pub fn new(conjunctions: Vec<Conjunction>) -> Self {
        Self {
            conjunctions,
        }
    }

    pub fn always_true() -> Self {
        Disjunction::new(vec![Conjunction::always_true()])
    }

    pub fn always_false() -> Self {
        Disjunction::new(Vec::new())
    }

    fn fold(&self) -> SynthesizedComputation {
        if self.conjunctions.is_empty() {
            SynthesizedComputation::new(
                FALSE.to_owned(),
                Vec::new(),
                Vec::new(),
                OutputEncoding::UnsignedBigEndian,
                IoType::Integer {
                    num_bits: 1,
                },
            )
        } else {
            let first = self.conjunctions[0].fold();
            self.conjunctions[1..].iter().fold(first, |acc, term| acc.or(&term.fold()))
        }
    }

    pub fn evaluate<V: AsValue>(&self, inputs: &[V]) -> bool {
        self.conjunctions.iter().any(|item| item.evaluate(inputs))
    }

    pub fn used_input_indices(&self) -> Vec<usize> {
        let mut seen = GrowingBitmap::new();
        self.conjunctions
            .iter()
            .flat_map(|item| item.terms.iter().flat_map(|term| term.used_input_indices()))
            .filter(|&n| seen.set(n))
            .collect()
    }

    pub fn remap_inputs(&mut self, map: &[Option<usize>]) {
        for conj in self.conjunctions.iter_mut() {
            for term in conj.terms.iter_mut() {
                term.remap_inputs(map);
            }
        }
    }

    pub fn display<'a, S: AsRef<str>>(&'a self, _input_names: &'a [S]) -> DisplayDisjunction<'a> {
        // TODO: Use input_names
        DisplayDisjunction(self)
    }

    pub fn and_also(&mut self, dis: &Disjunction) {
        let mut old_conjunctions = Vec::new();
        swap(&mut old_conjunctions, &mut self.conjunctions);
        for conjunction in old_conjunctions.iter() {
            for other in dis.iter() {
                let mut c = conjunction.clone();
                c.and_also(other.clone());
                self.conjunctions.push(c);
            }
        }
    }

    pub fn and_also_term(&mut self, term: &Term) {
        for conjunction in self.conjunctions.iter_mut() {
            conjunction.push(term.clone());
        }
    }

    pub fn is_always_false(&self) -> bool {
        self.conjunctions.is_empty()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Conjunction> {
        self.conjunctions.iter_mut()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Conjunction> {
        self.conjunctions.iter()
    }
}

#[derive(Debug)]
pub struct DisplayDisjunction<'a>(&'a Disjunction);

impl Display for DisplayDisjunction<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: Use argument names
        Display::fmt(self.0, f)
    }
}

impl From<Disjunction> for SynthesizedComputation {
    fn from(value: Disjunction) -> Self {
        value.fold()
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::{Computation, IoType, ARG_NAMES};
    use liblisa::value::OwnedValue;

    use super::{Conjunction, Disjunction, Term};

    #[test]
    pub fn fold_disjunction_ok() {
        let d = Disjunction::new(vec![Conjunction::new(vec![
            // IfZero(Crop[1](IsZero(ube(A) - 0x1) & (IsZero(ube(B) - 0x8000000000000000) & IsZero(ube(C) - 0x0)))
            Term::CaseMatch {
                negate: false,
                input_indices: vec![
                    (
                        0,
                        IoType::Integer {
                            num_bits: 1,
                        },
                    ),
                    (
                        1,
                        IoType::Bytes {
                            num_bytes: 8,
                        },
                    ),
                    (
                        2,
                        IoType::Integer {
                            num_bits: 32,
                        },
                    ),
                ],
                cases: vec![vec![
                    OwnedValue::Num(0x1),
                    OwnedValue::Bytes(vec![0, 0, 0, 0, 0, 0, 0, 0x80]),
                    OwnedValue::Num(0),
                ]],
            },
        ])]);

        let result = d.fold();
        println!("{}", result.display(ARG_NAMES));
        assert_eq!(
            result.evaluate(&[
                OwnedValue::Num(0x1),
                OwnedValue::Bytes(vec![0, 0, 0, 0, 0, 0, 0, 0x80]),
                OwnedValue::Num(0),
            ]),
            OwnedValue::Num(1)
        );
    }
}
