use std::iter::once;
use std::time::Instant;

use liblisa::semantics::IoType;
use liblisa::utils::Timeout;
use liblisa::value::{AsValue, OwnedValue};
use log::info;

use super::combiner::Combiner;
use crate::cond::combiner::CombinerResult;
use crate::predicate::{Conjunction, Disjunction, Term};
use crate::search::termsearcher::BoolTermSearcher;
use crate::{InputSlice, Synthesizer, SynthesizerBase};

#[derive(Clone, Debug)]
struct Avoid {
    inputs: Vec<OwnedValue>,
}

#[derive(Clone)]
struct Combined<'a> {
    combiner: Combiner<'a>,
    negated_combiner: Combiner<'a>,
    next: bool,
    mcs_limit: usize,
}

#[derive(Clone)]
enum State<'a> {
    CaseMatch,
    SingleSearcher(Box<BoolTermSearcher<'a>>),
    Combined(Box<Combined<'a>>),
}

impl std::fmt::Debug for State<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CaseMatch => write!(f, "CaseMatch"),
            Self::SingleSearcher {
                ..
            } => write!(f, "SingleSearcher"),
            Self::Combined {
                ..
            } => write!(f, "Combined"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SimplePredicateCombiner<'a> {
    state: State<'a>,
    avoid: Vec<Avoid>,
    target: Vec<Vec<OwnedValue>>,
    hypothesis: Option<Disjunction>,
    failed: bool,
    input_types: Vec<IoType>,
    input_indices: Vec<usize>,
    timeout: Timeout,
}

impl SynthesizerBase for SimplePredicateCombiner<'_> {
    type Hypothesis = Disjunction;
    type Computation = Disjunction;

    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        Self::new(input_types, (0..input_types.len()).collect(), output_type)
    }

    fn hypothesis(&self) -> Option<&Self::Hypothesis> {
        self.hypothesis.as_ref()
    }

    fn has_given_up(&self) -> bool {
        self.failed
    }

    fn needs_requester(&self) -> bool {
        false
    }

    fn into_computation(self) -> Option<Self::Computation> {
        self.hypothesis
    }

    fn set_timeout(&mut self, stop_at: Instant) {
        self.timeout.set_timeout_at(stop_at);
    }
}

impl SimplePredicateCombiner<'_> {
    pub fn new(input_types: &[IoType], input_indices: Vec<usize>, output_type: IoType) -> Self {
        assert_eq!(
            output_type,
            IoType::Integer {
                num_bits: 1
            }
        );

        SimplePredicateCombiner {
            input_types: input_types.to_vec(),
            input_indices,
            state: State::CaseMatch,
            avoid: Vec::new(),
            target: Vec::new(),
            hypothesis: Some(Disjunction::always_true()),
            failed: false,
            timeout: Timeout::default(),
        }
    }

    fn create_case_match<'a>(
        &self, negate: bool, target: impl Iterator<Item = &'a [OwnedValue]>, avoid: impl Iterator<Item = &'a [OwnedValue]>,
    ) -> Conjunction {
        let mut cases = target
            .map(|case| {
                self.input_indices
                    .iter()
                    .map(|&input_index| case[input_index].clone())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        cases.sort();
        cases.dedup();

        if cases.is_empty() {
            if negate {
                return Conjunction::always_true()
            } else {
                return Conjunction::always_false()
            }
        }

        let term = Term::CaseMatch {
            negate,
            input_indices: self
                .input_indices
                .iter()
                .map(|&index| (index, self.input_types[index]))
                .collect(),
            cases,
        };

        let corrections = avoid
            .filter(|avoid| term.evaluate(avoid) ^ negate)
            .map(|avoid| avoid.to_vec())
            .collect::<Vec<_>>();

        if !corrections.is_empty() {
            let correction = Term::CaseMatch {
                negate: !negate,
                input_indices: self.input_types.iter().copied().enumerate().collect(),
                cases: corrections,
            };

            if negate {
                panic!("Cannot apply correction when negated: {correction}")
            } else {
                Conjunction::new(vec![term, correction])
            }
        } else {
            Conjunction::new(vec![term])
        }
    }

    fn start_combiner(&mut self) {
        let combiner = Combiner::new(
            &self.input_types,
            &self.input_indices,
            self.timeout,
            self.target.iter(),
            self.avoid.iter().map(|avoid| &avoid.inputs),
        );
        let negated_combiner = Combiner::new(
            &self.input_types,
            &self.input_indices,
            self.timeout,
            self.avoid.iter().map(|avoid| &avoid.inputs),
            self.target.iter(),
        );
        self.state = State::Combined(Box::new(Combined {
            combiner,
            negated_combiner,
            next: false,
            mcs_limit: 1,
        }));
    }

    pub fn add_multiple_cases<'a, V: AsValue + 'a>(
        &mut self, cases: impl Iterator<Item = (&'a [V], bool)>, abort_on_combined: bool,
    ) -> bool {
        if self.failed {
            return false
        }

        let mut consistent = true;
        for (inputs, output) in cases {
            if output {
                if !self
                    .target
                    .iter()
                    .any(|target| target.iter().zip(inputs.iter()).all(|(a, b)| a.as_value() == b.as_value()))
                {
                    self.target.push(inputs.as_owned());
                }
            } else if !self.avoid.iter().any(|avoid| {
                avoid
                    .inputs
                    .iter()
                    .zip(inputs.iter())
                    .all(|(a, b)| a.as_value() == b.as_value())
            }) {
                self.avoid.push(Avoid {
                    inputs: inputs.iter().map(AsValue::to_owned_value).collect(),
                });
            }

            match &mut self.state {
                State::SingleSearcher(searcher) => {
                    searcher.add_case(inputs, output);
                },
                State::Combined(c) => {
                    c.combiner.add_case(inputs, output);
                    c.negated_combiner.add_case(inputs, !output);
                },
                _ => (),
            }

            if !self.is_consistent(inputs, output) {
                if self.hypothesis.is_some() {
                    info!(
                        "Hypothesis {:?} is not consistent: hypothesis gave {:?} but expected {output}",
                        self.hypothesis.as_ref().map(|hyp| hyp.to_string()),
                        self.hypothesis.as_ref().map(|hyp| hyp.evaluate(inputs))
                    );
                }

                self.hypothesis = None;
                consistent = false;
            }
        }

        if !consistent {
            info!("Generating new hypothesis...");
            match &self.state {
                State::CaseMatch => {
                    if self.target.len() > 16 {
                        info!("Switching from CaseMatch to term searcher");
                        let mut searcher = BoolTermSearcher::new(
                            &self.input_types,
                            IoType::Integer {
                                num_bits: 1,
                            },
                        );
                        for target in self.target.iter() {
                            searcher.add_case(target, true);
                            if self.timeout.is_timed_out() {
                                self.failed = true;
                                return false
                            }
                        }

                        for avoid in self.avoid.iter() {
                            searcher.add_case(&avoid.inputs, false);
                            if self.timeout.is_timed_out() {
                                self.failed = true;
                                return false
                            }
                        }

                        if searcher.has_given_up() || searcher.hypothesis().is_none() {
                            if abort_on_combined {
                                return true
                            }

                            info!("Starting combiner...");
                            self.start_combiner();
                        } else {
                            self.state = State::SingleSearcher(Box::new(searcher));
                        }
                    }
                },
                State::SingleSearcher(searcher) => {
                    if searcher.has_given_up() || searcher.hypothesis().is_none() {
                        if abort_on_combined {
                            return true
                        }

                        self.start_combiner();
                    }
                },
                State::Combined {
                    ..
                } => (),
            }

            self.hypothesis = Some(match &mut self.state {
                State::CaseMatch => {
                    if self.avoid.len() >= self.target.len()
                        || self.target.iter().any(|target| {
                            self.avoid
                                .iter()
                                .any(|avoid| self.input_indices.iter().all(|&index| avoid.inputs[index] == target[index]))
                        })
                    {
                        let result = self.create_case_match(
                            false,
                            self.target.iter().map(|t| &t[..]),
                            self.avoid.iter().map(|t| &t.inputs[..]),
                        );
                        result.into()
                    } else {
                        let result = self.create_case_match(
                            true,
                            self.avoid.iter().map(|t| &t.inputs[..]),
                            self.target.iter().map(|t| &t[..]),
                        );
                        result.into()
                    }
                },
                State::SingleSearcher(searcher) => {
                    // We can unwrap because we switch state if the searcher gives up.
                    let term = searcher.hypothesis().unwrap();
                    Conjunction::new(vec![term.clone()]).into()
                },
                State::Combined(c) => loop {
                    if abort_on_combined {
                        return true
                    }

                    let (combiner, other, negate) = if c.next {
                        (&mut c.combiner, &mut c.negated_combiner, false)
                    } else {
                        (&mut c.negated_combiner, &mut c.combiner, true)
                    };

                    info!(
                        "Finding next conjunction for negate={negate} combiner with mcs_limit={}",
                        c.mcs_limit
                    );
                    match combiner.next_conjunction(c.mcs_limit) {
                        CombinerResult::Found(conjunction) => {
                            if !other.has_failed() && other.last_mcs_size() <= combiner.last_mcs_size() {
                                c.next = !c.next;
                            }

                            break if negate {
                                conjunction.negate()
                            } else {
                                Disjunction::new(vec![conjunction])
                            }
                        },
                        CombinerResult::McsLimitReached => {
                            if other.last_mcs_size() < combiner.last_mcs_size() {
                                c.next = !c.next;
                            } else {
                                c.mcs_limit = combiner.last_mcs_size();
                            }
                        },
                        CombinerResult::Failed => {
                            if other.has_failed() {
                                self.failed = true;
                                return false
                            } else {
                                c.next = !c.next;
                            }
                        },
                    }
                },
            });
        }

        false
    }

    pub fn using_combined_solution(&self) -> bool {
        matches!(self.state, State::Combined { .. })
    }
}

impl Synthesizer<bool> for SimplePredicateCombiner<'_> {
    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: bool) -> bool {
        self.hypothesis
            .as_ref()
            .map(|hyp| hyp.evaluate(inputs) == output)
            .unwrap_or(false)
    }

    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: bool) {
        self.add_multiple_cases(once((inputs, output)), false);
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::IoType;
    use liblisa::value::{AsValue, OwnedValue, Value};
    use test_log::test;

    use super::SimplePredicateCombiner;
    use crate::{synthesize_from_fn, Synthesizer, SynthesizerBase};

    fn test_with_cases<const N: usize>(s: &mut SimplePredicateCombiner, cases: &[(bool, [Value; N])]) {
        for (output, inputs) in cases {
            println!("## Adding case: {inputs:X?} => {output}");
            s.add_case(inputs, *output);
        }
    }

    #[test]
    pub fn find_condition_1() {
        use Value::*;
        let cases = &[
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF5D56110D485E),
                    Bytes(&[0x2B, 0xE6, 0xEB, 0x5F, 0xFF, 0xFF, 0xFF, 0xEB]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF5D56110D485E),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x2B, 0xE6, 0xEB, 0x5F, 0xFF, 0xFF, 0xFF, 0xEB]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFFFFFFF),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF87FFFFFFFFFF),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [Num(0x3B), Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]), Num(0x1)],
            ),
            (
                false,
                [
                    Num(0x1A6DFF00),
                    Bytes(&[0x4C, 0x7B, 0x75, 0xCF, 0x4E, 0x13, 0xC8, 0xF1]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0x1A6DFF00),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x4C, 0x7B, 0x75, 0xCF, 0x4E, 0x13, 0xC8, 0xF1]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0x96AFFFFFFFFFFFF),
                    Bytes(&[0x0, 0x0, 0x0, 0x4F, 0x78, 0x9F, 0xEC, 0x91]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0x96AFFFFFFFFFFFF),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x0, 0x0, 0x0, 0x4F, 0x78, 0x9F, 0xEC, 0x91]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFF2E7CC6D2CA7FFF),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFA0BDDB1D),
                    Bytes(&[0xFF, 0xFF, 0x1E, 0xE7, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xFF, 0xFF, 0x1E, 0xE7, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFA0BDDB1D),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFFB5A70),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0x9F97B00),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0x14FF8970),
                    Bytes(&[0x40, 0x3D, 0xF1, 0xE2, 0x46, 0x5B, 0xCB, 0xCE]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0x14FF8970),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x40, 0x3D, 0xF1, 0xE2, 0x46, 0x5B, 0xCB, 0xCE]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFE7FFA37650569),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFF95B30),
                    Bytes(&[0xB6, 0x8F, 0x65, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF5D56110D485E),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF5D56110D485E),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFFFFFFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFFFFFFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF87FFFFFFFFFF),
                    Bytes(&[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x30, 0x27]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF87FFFFFFFFFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFF87FFFFFFFFFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x30, 0x27]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [Num(0x3B), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x0)],
            ),
            (
                false,
                [Num(0x3B), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x1)],
            ),
            (
                false,
                [Num(0x1A6DFF00), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x0)],
            ),
            (
                false,
                [Num(0x1A6DFF00), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x1)],
            ),
            (
                false,
                [
                    Num(0x96AFFFFFFFFFFFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0x96AFFFFFFFFFFFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFF2E7CC6D2CA7FFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFF2E7CC6D2CA7FFF),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFA0BDDB1D),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFA0BDDB1D),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFFB5A70),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFFB5A70),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [Num(0x9F97B00), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x0)],
            ),
            (
                false,
                [Num(0x9F97B00), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x1)],
            ),
            (
                false,
                [Num(0x14FF8970), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x0)],
            ),
            (
                false,
                [Num(0x14FF8970), Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]), Num(0x1)],
            ),
            (
                false,
                [
                    Num(0xFFFE7FFA37650569),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFE7FFA37650569),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFF95B30),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                false,
                [
                    Num(0xFFFFFFFFFFF95B30),
                    Bytes(&[0x7F, 0xF0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFF5D56110D485E),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFF5D56110D485E),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFFFFFFF),
                    Bytes(&[0x57, 0xF6, 0x89, 0x47, 0xEF, 0x1, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x57, 0xF6, 0x89, 0x47, 0xEF, 0x1, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFFFFFFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFFFFFFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFF87FFFFFFFFFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFF87FFFFFFFFFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [Num(0x3B), Bytes(&[0xCE, 0x80, 0x0, 0x0, 0xFF, 0x80, 0x0, 0x0]), Num(0x0)],
            ),
            (
                true,
                [Num(0x3B), Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]), Num(0x0)],
            ),
            (
                true,
                [Num(0x3B), Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]), Num(0x1)],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xCE, 0x80, 0x0, 0x0, 0xFF, 0x80, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0x1A6DFF00),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0x1A6DFF00),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0x96AFFFFFFFFFFFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0x96AFFFFFFFFFFFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFF2E7CC6D2CA7FFF),
                    Bytes(&[0x40, 0xD, 0xE9, 0xBD, 0x86, 0x52, 0x59, 0x49]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFF2E7CC6D2CA7FFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFF2E7CC6D2CA7FFF),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x40, 0xD, 0xE9, 0xBD, 0x86, 0x52, 0x59, 0x49]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFA0BDDB1D),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFA0BDDB1D),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFFB5A70),
                    Bytes(&[0x19, 0xA2, 0x77, 0x0, 0x70, 0xFB, 0xD4, 0x3A]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x19, 0xA2, 0x77, 0x0, 0x70, 0xFB, 0xD4, 0x3A]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFFB5A70),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFFB5A70),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [Num(0x9F97B00), Bytes(&[0xFF, 0xCF, 0xFB, 0xDF, 0x0, 0x0, 0x0, 0x8]), Num(0x1)],
            ),
            (
                true,
                [
                    Num(0x9F97B00),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0x9F97B00),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0xFF, 0xCF, 0xFB, 0xDF, 0x0, 0x0, 0x0, 0x8]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0x14FF8970),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0x14FF8970),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFE7FFA37650569),
                    Bytes(&[0x0, 0x0, 0xC0, 0xFF, 0xFF, 0xFF, 0xDF, 0x41]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFE7FFA37650569),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFE7FFA37650569),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFE2B700D9BF),
                    Bytes(&[0x0, 0x0, 0xC0, 0xFF, 0xFF, 0xFF, 0xDF, 0x41]),
                    Num(0x1),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFF95B30),
                    Bytes(&[0xFF, 0xFF, 0x80, 0x0, 0x0, 0x0, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFF95B30),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x0),
                ],
            ),
            (
                true,
                [
                    Num(0xFFFFFFFFFFF95B30),
                    Bytes(&[0xFF, 0x7F, 0xC4, 0xFF, 0x20, 0x3, 0x0, 0x0]),
                    Num(0x1),
                ],
            ),
        ];

        let mut s = SimplePredicateCombiner::new(
            &[
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Bytes {
                    num_bytes: 8,
                },
                IoType::Integer {
                    num_bits: 1,
                },
            ],
            vec![1],
            IoType::Integer {
                num_bits: 1,
            },
        );
        test_with_cases(&mut s, cases);

        println!("{}", s.hypothesis().unwrap());
    }

    #[test]
    pub fn find_combined_complex_terms2() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let (a, b) = (values[0].unwrap_num(), values[1].unwrap_num());

                a & 0x200 != 0 && b & 0x40 != 0
            })
        })
        .unwrap();
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_combined_complex_terms3() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let (a, b, c) = (values[0].unwrap_num(), values[1].unwrap_num(), values[2].unwrap_num());

                (a >> 13) & 1 != 0 && b == c
            })
        })
        .unwrap();
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_combined_simple_terms() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let (a, b, c) = (values[0].unwrap_num(), values[1].unwrap_num(), values[2].unwrap_num());

                a + b == 0 && c != 0
            })
        })
        .unwrap();
    }

    #[test]
    pub fn find_partial_xor_zf() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 24,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2, 3, 4],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let [x, _, _, c, _] = [0, 1, 2, 3, 4].map(|index| values[index].unwrap_num());

                ((x >> 16) ^ c) as u8 == 0
            })
        })
        .unwrap();
    }

    #[test]
    pub fn find_split_2byte_xor_zf() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 16,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let [x, a, b] = [0, 1, 2].map(|index| values[index].unwrap_num());

                let r1 = x ^ (a | (b << 8)) == 0;
                let r2 = (x ^ a) as u8 == 0 && ((x >> 8) ^ b) as u8 == 0;

                assert_eq!(r1, r2);

                r2
            })
        })
        .unwrap();
    }

    #[test]
    pub fn find_split_3byte_xor_zf() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 24,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2, 3],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let [x, a, b, c] = [0, 1, 2, 3].map(|index| values[index].unwrap_num());

                let r1 = x ^ (a | (b << 8) | (c << 16)) == 0;
                let r2 = (x ^ a) as u8 == 0 && ((x >> 8) ^ b) as u8 == 0 && ((x >> 16) ^ c) as u8 == 0;

                assert_eq!(r1, r2);

                r2
            })
        })
        .unwrap();
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_split_4byte_xor_zf() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 32,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2, 3, 4],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let [x, a, b, c, d] = [0, 1, 2, 3, 4].map(|index| values[index].unwrap_num());

                let r1 = x ^ (a | (b << 8) | (c << 16) | (d << 24)) == 0;
                let r2 =
                    (x ^ a) as u8 == 0 && ((x >> 8) ^ b) as u8 == 0 && ((x >> 16) ^ c) as u8 == 0 && ((x >> 24) ^ d) as u8 == 0;

                assert_eq!(r1, r2);

                r2
            })
        })
        .unwrap();
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_split_4byte_xor_nzf() {
        let mut rng = rand::thread_rng();
        let input_types = &[
            IoType::Integer {
                num_bits: 32,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0, 1, 2, 3, 4],
            IoType::Integer {
                num_bits: 1,
            },
        );
        synthesize_from_fn(&mut rng, synthesizer, input_types, |values| {
            Some({
                let [x, a, b, c, d] = [0, 1, 2, 3, 4].map(|index| values[index].unwrap_num());

                let r1 = x ^ (a | (b << 8) | (c << 16) | (d << 24)) == 0;
                let r2 =
                    (x ^ a) as u8 == 0 && ((x >> 8) ^ b) as u8 == 0 && ((x >> 16) ^ c) as u8 == 0 && ((x >> 24) ^ d) as u8 == 0;

                assert_eq!(r1, r2);

                !r2
            })
        })
        .unwrap();
    }

    // TODO: Find split and zf

    #[test]
    pub fn create_case_match_ok() {
        let input_types = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0],
            IoType::Integer {
                num_bits: 1,
            },
        );

        use OwnedValue::*;
        let case_match = synthesizer.create_case_match(false, [&[Num(3), Num(17)][..]].into_iter(), [].into_iter());

        println!("{case_match}");
        assert!(case_match.evaluate(&[Num(3), Num(17)]));

        let case_match = synthesizer.create_case_match(false, [].into_iter(), [&[Num(5), Num(13)][..]].into_iter());

        println!("{case_match}");
        assert!(!case_match.evaluate(&[Num(5), Num(13)]));

        let case_match = synthesizer.create_case_match(
            false,
            [&[Num(3), Num(17)][..], &[Num(5), Num(12)], &[Num(0), Num(0)]].into_iter(),
            [&[Num(5), Num(13)][..], &[Num(1), Num(8)]].into_iter(),
        );

        assert!(case_match.evaluate(&[Num(3), Num(17)]));
        assert!(case_match.evaluate(&[Num(5), Num(12)]));
        assert!(case_match.evaluate(&[Num(0), Num(0)]));
        assert!(!case_match.evaluate(&[Num(5), Num(13)]));
        assert!(!case_match.evaluate(&[Num(1), Num(8)]));

        let case_match = synthesizer.create_case_match(
            false,
            [&[Num(3), Num(17)][..], &[Num(5), Num(12)]].into_iter(),
            [&[Num(5), Num(13)][..], &[Num(1), Num(8)], &[Num(0), Num(0)]].into_iter(),
        );

        assert!(case_match.evaluate(&[Num(3), Num(17)]));
        assert!(case_match.evaluate(&[Num(5), Num(12)]));
        assert!(!case_match.evaluate(&[Num(5), Num(13)]));
        assert!(!case_match.evaluate(&[Num(1), Num(8)]));
        assert!(!case_match.evaluate(&[Num(0), Num(0)]));
    }

    #[test]
    #[should_panic]
    pub fn create_case_match_neg_panic() {
        let input_types = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0],
            IoType::Integer {
                num_bits: 1,
            },
        );

        use OwnedValue::*;
        let case_match = synthesizer.create_case_match(
            true,
            [&[Num(3), Num(17)][..], &[Num(5), Num(12)], &[Num(0), Num(0)]].into_iter(),
            [&[Num(5), Num(13)][..], &[Num(1), Num(8)]].into_iter(),
        );

        println!("{case_match}");

        assert!(!case_match.evaluate(&[Num(3), Num(17)]));
        assert!(!case_match.evaluate(&[Num(5), Num(12)]));
        assert!(!case_match.evaluate(&[Num(0), Num(0)]));
        assert!(case_match.evaluate(&[Num(5), Num(13)]));
        assert!(case_match.evaluate(&[Num(1), Num(8)]));

        let case_match = synthesizer.create_case_match(
            true,
            [&[Num(3), Num(17)][..], &[Num(5), Num(12)]].into_iter(),
            [&[Num(5), Num(13)][..], &[Num(1), Num(8)], &[Num(0), Num(0)]].into_iter(),
        );

        println!("{case_match}");

        assert!(!case_match.evaluate(&[Num(3), Num(17)]));
        assert!(!case_match.evaluate(&[Num(5), Num(12)]));
        assert!(case_match.evaluate(&[Num(5), Num(13)]));
        assert!(case_match.evaluate(&[Num(1), Num(8)]));
        assert!(case_match.evaluate(&[Num(0), Num(0)]));
    }

    #[test]
    pub fn create_case_match_neg_ok() {
        let input_types = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let synthesizer = SimplePredicateCombiner::new(
            input_types,
            vec![0],
            IoType::Integer {
                num_bits: 1,
            },
        );

        use OwnedValue::*;
        let case_match = synthesizer.create_case_match(true, [&[Num(3), Num(17)][..]].into_iter(), [].into_iter());

        assert!(!case_match.evaluate(&[Num(3), Num(17)]));

        let case_match = synthesizer.create_case_match(true, [].into_iter(), [&[Num(5), Num(13)][..]].into_iter());

        assert!(case_match.evaluate(&[Num(5), Num(13)]));

        let case_match = synthesizer.create_case_match(
            true,
            [&[Num(3), Num(17)][..], &[Num(5), Num(12)], &[Num(0), Num(0)]].into_iter(),
            [&[Num(6), Num(13)][..], &[Num(1), Num(8)]].into_iter(),
        );

        println!("{case_match}");

        assert!(!case_match.evaluate(&[Num(3), Num(17)]));
        assert!(!case_match.evaluate(&[Num(5), Num(12)]));
        assert!(!case_match.evaluate(&[Num(0), Num(0)]));
        assert!(case_match.evaluate(&[Num(6), Num(13)]));
        assert!(case_match.evaluate(&[Num(1), Num(8)]));

        let case_match = synthesizer.create_case_match(
            true,
            [&[Num(3), Num(17)][..], &[Num(5), Num(12)]].into_iter(),
            [&[Num(6), Num(13)][..], &[Num(1), Num(8)], &[Num(0), Num(0)]].into_iter(),
        );

        println!("{case_match}");

        assert!(!case_match.evaluate(&[Num(3), Num(17)]));
        assert!(!case_match.evaluate(&[Num(5), Num(12)]));
        assert!(case_match.evaluate(&[Num(6), Num(13)]));
        assert!(case_match.evaluate(&[Num(1), Num(8)]));
        assert!(case_match.evaluate(&[Num(0), Num(0)]));
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_and_with_imm() {
        use Value::Num;
        let cases = &[
            (true, [Num(0xFD693E8D), Num(0x15), Num(0xE)]),
            (true, [Num(0xFD693E8D), Num(0x15), Num(0xE)]),
            (true, [Num(0x1BD00000), Num(0x15), Num(0xE)]),
            (true, [Num(0x1BD00000), Num(0x15), Num(0xE)]),
            (true, [Num(0xDC22388C), Num(0x15), Num(0xE)]),
            (true, [Num(0xDC22388C), Num(0x15), Num(0xE)]),
            (true, [Num(0x16D7F216), Num(0x15), Num(0xE)]),
            (true, [Num(0x16D7F216), Num(0x15), Num(0xE)]),
            (true, [Num(0xA72B4A50), Num(0x15), Num(0xE)]),
            (true, [Num(0xA72B4A50), Num(0x15), Num(0xE)]),
            (true, [Num(0x88DD5FFF), Num(0x15), Num(0xE)]),
            (true, [Num(0x88DD5FFF), Num(0x15), Num(0xE)]),
            (true, [Num(0x80988), Num(0x15), Num(0xE)]),
            (true, [Num(0x80988), Num(0x15), Num(0xE)]),
            (true, [Num(0xFFFEC0F1), Num(0x15), Num(0xE)]),
            (true, [Num(0xFFFEC0F1), Num(0x15), Num(0xE)]),
            (true, [Num(0xFFFFFFFF), Num(0x15), Num(0xE)]),
            (true, [Num(0xFFFFFFFF), Num(0x15), Num(0xE)]),
            (true, [Num(0xB5C1ACC9), Num(0x15), Num(0xE)]),
            (true, [Num(0xB5C1ACC9), Num(0x15), Num(0xE)]),
            (true, [Num(0x38000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x38000000), Num(0x15), Num(0xE)]),
            (true, [Num(0xF20000), Num(0x15), Num(0xE)]),
            (true, [Num(0xF20000), Num(0x15), Num(0xE)]),
            (true, [Num(0x2C216800), Num(0x15), Num(0xE)]),
            (true, [Num(0x2C216800), Num(0x15), Num(0xE)]),
            (true, [Num(0x6BDD85), Num(0x15), Num(0xE)]),
            (true, [Num(0x6BDD85), Num(0x15), Num(0xE)]),
            (true, [Num(0xFFFE4D65), Num(0x15), Num(0xE)]),
            (true, [Num(0xFFFE4D65), Num(0x15), Num(0xE)]),
            (true, [Num(0x328F2), Num(0x15), Num(0xE)]),
            (true, [Num(0x328F2), Num(0x15), Num(0xE)]),
            (true, [Num(0xB5258F6C), Num(0x15), Num(0xE)]),
            (true, [Num(0xB5258F6C), Num(0x15), Num(0xE)]),
            (true, [Num(0xD0000000), Num(0x15), Num(0xE)]),
            (true, [Num(0xD0000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x3F007FFF), Num(0x15), Num(0xE)]),
            (true, [Num(0x3F007FFF), Num(0x15), Num(0xE)]),
            (true, [Num(0x1517C28), Num(0x15), Num(0xE)]),
            (true, [Num(0x1517C28), Num(0x15), Num(0xE)]),
            (true, [Num(0xE2463640), Num(0x15), Num(0xE)]),
            (true, [Num(0xE2463640), Num(0x15), Num(0xE)]),
            (true, [Num(0xEB5E06B7), Num(0x15), Num(0xE)]),
            (true, [Num(0xEB5E06B7), Num(0x15), Num(0xE)]),
            (true, [Num(0x5C11296F), Num(0x15), Num(0xE)]),
            (true, [Num(0x5C11296F), Num(0x15), Num(0xE)]),
            (true, [Num(0x6D91C0CB), Num(0x15), Num(0xE)]),
            (true, [Num(0x6D91C0CB), Num(0x15), Num(0xE)]),
            (true, [Num(0x2B001000), Num(0x15), Num(0xE)]),
            (true, [Num(0x2B001000), Num(0x15), Num(0xE)]),
            (true, [Num(0xE0000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFD693E8D), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFD693E8D), Num(0x2B), Num(0xE)]),
            (true, [Num(0x9), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x800), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x4B5C), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1CFC5), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x80988), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x60A4E8), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6BDD85), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xA00000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xF20000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1BD00000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x28400000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x2B001000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x2C216800), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x38000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x3F007FFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x4050FFFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x5C11296F), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6A000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6D91C0CB), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xA72B4A50), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xB5258F6C), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xB5C1ACC9), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE0000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE0000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE2463640), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xEB5E06B7), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFD693E8D), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFFFEC0F1), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFFFFFFFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xD0000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x2B), Num(0xE)]),
            (true, [Num(0x328F2), Num(0x2B), Num(0xE)]),
            (true, [Num(0x80988), Num(0x2B), Num(0xE)]),
            (true, [Num(0x80988), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6BDD85), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6BDD85), Num(0x2B), Num(0xE)]),
            (true, [Num(0xF20000), Num(0x2B), Num(0xE)]),
            (true, [Num(0xF20000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x1517C28), Num(0x2B), Num(0xE)]),
            (true, [Num(0x1517C28), Num(0x2B), Num(0xE)]),
            (true, [Num(0x16D7F216), Num(0x2B), Num(0xE)]),
            (true, [Num(0x16D7F216), Num(0x2B), Num(0xE)]),
            (true, [Num(0x1BD00000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x1BD00000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x28400000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x28400000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2B001000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2B001000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2C216800), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2C216800), Num(0x2B), Num(0xE)]),
            (true, [Num(0x38000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x38000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x3F007FFF), Num(0x2B), Num(0xE)]),
            (true, [Num(0x3F007FFF), Num(0x2B), Num(0xE)]),
            (true, [Num(0x5C11296F), Num(0x2B), Num(0xE)]),
            (true, [Num(0x5C11296F), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6A000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6A000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6D91C0CB), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6D91C0CB), Num(0x2B), Num(0xE)]),
            (true, [Num(0x88DD5FFF), Num(0x2B), Num(0xE)]),
            (true, [Num(0x88DD5FFF), Num(0x2B), Num(0xE)]),
            (true, [Num(0xA72B4A50), Num(0x2B), Num(0xE)]),
            (true, [Num(0xA72B4A50), Num(0x2B), Num(0xE)]),
            (true, [Num(0xB5258F6C), Num(0x2B), Num(0xE)]),
            (true, [Num(0xB5258F6C), Num(0x2B), Num(0xE)]),
            (true, [Num(0xB5C1ACC9), Num(0x2B), Num(0xE)]),
            (true, [Num(0xB5C1ACC9), Num(0x2B), Num(0xE)]),
            (true, [Num(0xDC22388C), Num(0x2B), Num(0xE)]),
            (true, [Num(0xDC22388C), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE0000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE2463640), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE2463640), Num(0x2B), Num(0xE)]),
            (true, [Num(0xEB5E06B7), Num(0x2B), Num(0xE)]),
            (true, [Num(0xEB5E06B7), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFD693E8D), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFFFE4D65), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFFFE4D65), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFFFEC0F1), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFFFEC0F1), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFFFFFFFF), Num(0x2B), Num(0xE)]),
            (true, [Num(0xFFFFFFFF), Num(0x2B), Num(0xE)]),
            (true, [Num(0x9), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x9), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x9), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x800), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x800), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x4B5C), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x4B5C), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1CFC5), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1CFC5), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x80988), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x80988), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x60A4E8), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x60A4E8), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x6BDD85), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x6BDD85), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xA00000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xA00000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xF20000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xF20000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1BD00000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1BD00000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x28400000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x28400000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x2B001000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x2B001000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x2C216800), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x2C216800), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x38000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x38000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x3F007FFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x3F007FFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x4050FFFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x4050FFFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x5C11296F), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x5C11296F), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x6D91C0CB), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x6D91C0CB), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xA72B4A50), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xA72B4A50), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xB5258F6C), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xB5258F6C), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xB5C1ACC9), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xB5C1ACC9), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xD0000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xE2463640), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xE2463640), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xEB5E06B7), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xEB5E06B7), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFD693E8D), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFFFEC0F1), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFFFEC0F1), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFFFFFFFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xFFFFFFFF), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x3034F4), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x3034F4), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x3034F4), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1E), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1E), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x1E), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x8), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x8), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x8), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x68000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x68000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x68000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x68000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x78), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x78), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x78), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x78), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x94000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x94000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x94000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x94000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x18D), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x18D), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x18D), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x50000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x50000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x50000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x50000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x10000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x10000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x10000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x10000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x749), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x749), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x749), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x749), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE8000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE8000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE8000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x5E00), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x5E00), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x5E00), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xF40F), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xF40F), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xF40F), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0xF40F), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x4000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x4000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x4000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x4000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x2A000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x2A000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2A000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2A000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x10000001), Num(0x15), Num(0xE)]),
            (true, [Num(0x10000001), Num(0x15), Num(0xE)]),
            (true, [Num(0x10000001), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x10000001), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x8000001), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x8000001), Num(0x2B), Num(0xE)]),
            (true, [Num(0x8000001), Num(0x2B), Num(0xE)]),
            (true, [Num(0x4000001), Num(0x15), Num(0xE)]),
            (true, [Num(0x4000001), Num(0x15), Num(0xE)]),
            (true, [Num(0x4000001), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x4000001), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x80007F00), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x80007F00), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x80007F00), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x2000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x2000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2000000), Num(0x2B), Num(0xE)]),
            (true, [Num(0x2000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6A000020), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6A000020), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6A000020), Num(0x2B), Num(0xE)]),
            (true, [Num(0x6A000020), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE0000040), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE0000040), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE0000040), Num(0x2B), Num(0xE)]),
            (true, [Num(0xE0000040), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x10), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x10), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x10), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x10), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x14000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x9), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x4D), Num(0x0)]),
            (true, [Num(0x4000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x4000001), Num(0x4D), Num(0x0)]),
            (true, [Num(0x8000001), Num(0x4D), Num(0x0)]),
            (true, [Num(0x14000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x14000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x14000000), Num(0x15), Num(0xE)]),
            (true, [Num(0x14000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x14000000), Num(0x15), Num(0x189E6F)]),
            (true, [Num(0x14000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x14000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x14000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x4D), Num(0x0)]),
            (true, [Num(0x1BD00000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x28400000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x2A000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x2B001000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x2C216800), Num(0x4D), Num(0x0)]),
            (true, [Num(0x38000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x3F007FFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x4050FFFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x50000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x5C11296F), Num(0x4D), Num(0x0)]),
            (true, [Num(0x68000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x6A000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x6A000020), Num(0x4D), Num(0x0)]),
            (true, [Num(0x6D91C0CB), Num(0x4D), Num(0x0)]),
            (true, [Num(0x88DD5FFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x94000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xA72B4A50), Num(0x4D), Num(0x0)]),
            (true, [Num(0xB5258F6C), Num(0x4D), Num(0x0)]),
            (true, [Num(0xB5C1ACC9), Num(0x4D), Num(0x0)]),
            (true, [Num(0xC0000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xD0000000), Num(0x15), Num(0x0)]),
            (true, [Num(0xD0000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xD0000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xD0000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE0000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE0000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE0000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE0000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE0000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE0000040), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE2463640), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE8000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xEB5E06B7), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x15), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFD693E8D), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFFFEC0F1), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFFFFFFFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x8), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x9), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x10), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1E), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x78), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x18D), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x749), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x800), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4B5C), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x5E00), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xF40F), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1CFC5), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x80988), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x3034F4), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x60A4E8), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6BDD85), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xA00000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xF20000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x2B), Num(0x0)]),
            (true, [Num(0x1517C28), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x4000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4000001), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x8000001), Num(0x2B), Num(0x0)]),
            (true, [Num(0x8000001), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x14000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x2B), Num(0x0)]),
            (true, [Num(0x16D7F216), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1BD00000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x1BD00000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x28400000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x28400000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2A000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x2A000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2B001000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x2B001000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2C216800), Num(0x2B), Num(0x0)]),
            (true, [Num(0x2C216800), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x38000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x38000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x3F007FFF), Num(0x2B), Num(0x0)]),
            (true, [Num(0x3F007FFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4050FFFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x50000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x5C11296F), Num(0x2B), Num(0x0)]),
            (true, [Num(0x5C11296F), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x68000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x68000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6A000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x6A000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6A000020), Num(0x2B), Num(0x0)]),
            (true, [Num(0x6A000020), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6D91C0CB), Num(0x2B), Num(0x0)]),
            (true, [Num(0x6D91C0CB), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x80007F00), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x2B), Num(0x0)]),
            (true, [Num(0x88DD5FFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x94000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xA72B4A50), Num(0x2B), Num(0x0)]),
            (true, [Num(0xA72B4A50), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xB5258F6C), Num(0x2B), Num(0x0)]),
            (true, [Num(0xB5258F6C), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xB5C1ACC9), Num(0x2B), Num(0x0)]),
            (true, [Num(0xB5C1ACC9), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xC0000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xC0000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xC0000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x2B), Num(0x0)]),
            (true, [Num(0xDC22388C), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE0000040), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE0000040), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE2463640), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE2463640), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE8000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE8000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xEB5E06B7), Num(0x2B), Num(0x0)]),
            (true, [Num(0xEB5E06B7), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFFFE4D65), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFEC0F1), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFFFEC0F1), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFFFFFF), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFFFFFFFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x15), Num(0x0)]),
            (true, [Num(0x4000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x4000001), Num(0x15), Num(0x0)]),
            (true, [Num(0x10000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x10000001), Num(0x15), Num(0x0)]),
            (true, [Num(0x16D7F216), Num(0x15), Num(0x0)]),
            (true, [Num(0x1BD00000), Num(0x15), Num(0x0)]),
            (true, [Num(0x2B001000), Num(0x15), Num(0x0)]),
            (true, [Num(0x2C216800), Num(0x15), Num(0x0)]),
            (true, [Num(0x38000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x3F007FFF), Num(0x15), Num(0x0)]),
            (true, [Num(0x50000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x5C11296F), Num(0x15), Num(0x0)]),
            (true, [Num(0x6D91C0CB), Num(0x15), Num(0x0)]),
            (true, [Num(0x94000000), Num(0x15), Num(0x0)]),
            (true, [Num(0xA72B4A50), Num(0x15), Num(0x0)]),
            (true, [Num(0xB5258F6C), Num(0x15), Num(0x0)]),
            (true, [Num(0xB5C1ACC9), Num(0x15), Num(0x0)]),
            (true, [Num(0xC0000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x15), Num(0x0)]),
            (true, [Num(0xEB5E06B7), Num(0x15), Num(0x0)]),
            (true, [Num(0xFFFE4D65), Num(0x15), Num(0x0)]),
            (true, [Num(0xFFFEC0F1), Num(0x15), Num(0x0)]),
            (true, [Num(0xFFFFFFFF), Num(0x15), Num(0x0)]),
            (true, [Num(0x1517C28), Num(0x15), Num(0x0)]),
            (true, [Num(0x4000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x4000001), Num(0x15), Num(0x0)]),
            (true, [Num(0x10000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x10000001), Num(0x15), Num(0x0)]),
            (true, [Num(0x14000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x16D7F216), Num(0x15), Num(0x0)]),
            (true, [Num(0x1BD00000), Num(0x15), Num(0x0)]),
            (true, [Num(0x2B001000), Num(0x15), Num(0x0)]),
            (true, [Num(0x2C216800), Num(0x15), Num(0x0)]),
            (true, [Num(0x38000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x3F007FFF), Num(0x15), Num(0x0)]),
            (true, [Num(0x50000000), Num(0x15), Num(0x0)]),
            (true, [Num(0x5C11296F), Num(0x15), Num(0x0)]),
            (true, [Num(0x6D91C0CB), Num(0x15), Num(0x0)]),
            (true, [Num(0x94000000), Num(0x15), Num(0x0)]),
            (true, [Num(0xA72B4A50), Num(0x15), Num(0x0)]),
            (true, [Num(0xB5258F6C), Num(0x15), Num(0x0)]),
            (true, [Num(0xB5C1ACC9), Num(0x15), Num(0x0)]),
            (true, [Num(0xD0000000), Num(0x15), Num(0x0)]),
            (true, [Num(0xDC22388C), Num(0x15), Num(0x0)]),
            (true, [Num(0xEB5E06B7), Num(0x15), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x15), Num(0x0)]),
            (true, [Num(0xFFFE4D65), Num(0x15), Num(0x0)]),
            (true, [Num(0xFFFEC0F1), Num(0x15), Num(0x0)]),
            (true, [Num(0xFFFFFFFF), Num(0x15), Num(0x0)]),
            (true, [Num(0x8), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x10), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1E), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x78), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x18D), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x749), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x800), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4B5C), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x5E00), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xF40F), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1CFC5), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x4D), Num(0xE)]),
            (true, [Num(0x328F2), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x80988), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x3034F4), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x60A4E8), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6BDD85), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xA00000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xF20000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x4D), Num(0x0)]),
            (true, [Num(0x1517C28), Num(0x4D), Num(0xE)]),
            (true, [Num(0x1517C28), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4000001), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x8000001), Num(0x4D), Num(0x0)]),
            (true, [Num(0x8000001), Num(0x4D), Num(0xE)]),
            (true, [Num(0x8000001), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x1BD00000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x28400000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2A000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2B001000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x2C216800), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x38000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x3F007FFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x4050FFFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x50000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x5C11296F), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x68000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6A000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6A000020), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x6D91C0CB), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x80007F00), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x94000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xA72B4A50), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xB5258F6C), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xB5C1ACC9), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xD0000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE0000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE0000040), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE2463640), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xE8000000), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xEB5E06B7), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFD693E8D), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFEC0F1), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0xFFFFFFFF), Num(0x4D), Num(0x189E6F)]),
            (true, [Num(0x328F2), Num(0x4D), Num(0xE)]),
            (true, [Num(0x80988), Num(0x4D), Num(0xE)]),
            (true, [Num(0x80988), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6BDD85), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6BDD85), Num(0x4D), Num(0xE)]),
            (true, [Num(0xF20000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xF20000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x1517C28), Num(0x2B), Num(0x0)]),
            (true, [Num(0x1517C28), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x4000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x4000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x4000001), Num(0x4D), Num(0xE)]),
            (true, [Num(0x4000001), Num(0x4D), Num(0xE)]),
            (true, [Num(0x8000001), Num(0x2B), Num(0x0)]),
            (true, [Num(0x8000001), Num(0x4D), Num(0xE)]),
            (true, [Num(0x14000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x16D7F216), Num(0x2B), Num(0x0)]),
            (true, [Num(0x16D7F216), Num(0x4D), Num(0xE)]),
            (true, [Num(0x16D7F216), Num(0x4D), Num(0xE)]),
            (true, [Num(0x1BD00000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x1BD00000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x1BD00000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x28400000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x28400000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x28400000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2A000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x2A000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2A000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2B001000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x2B001000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2B001000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2C216800), Num(0x2B), Num(0x0)]),
            (true, [Num(0x2C216800), Num(0x4D), Num(0xE)]),
            (true, [Num(0x2C216800), Num(0x4D), Num(0xE)]),
            (true, [Num(0x38000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x38000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x38000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x3F007FFF), Num(0x2B), Num(0x0)]),
            (true, [Num(0x3F007FFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x3F007FFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x4050FFFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x4050FFFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x50000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x50000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x5C11296F), Num(0x2B), Num(0x0)]),
            (true, [Num(0x5C11296F), Num(0x4D), Num(0xE)]),
            (true, [Num(0x5C11296F), Num(0x4D), Num(0xE)]),
            (true, [Num(0x68000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x68000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x68000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6A000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0x6A000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6A000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6A000020), Num(0x2B), Num(0x0)]),
            (true, [Num(0x6A000020), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6A000020), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6D91C0CB), Num(0x2B), Num(0x0)]),
            (true, [Num(0x6D91C0CB), Num(0x4D), Num(0xE)]),
            (true, [Num(0x6D91C0CB), Num(0x4D), Num(0xE)]),
            (true, [Num(0x88DD5FFF), Num(0x2B), Num(0x0)]),
            (true, [Num(0x88DD5FFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x88DD5FFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x94000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0x94000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xA72B4A50), Num(0x2B), Num(0x0)]),
            (true, [Num(0xA72B4A50), Num(0x4D), Num(0xE)]),
            (true, [Num(0xA72B4A50), Num(0x4D), Num(0xE)]),
            (true, [Num(0xB5258F6C), Num(0x2B), Num(0x0)]),
            (true, [Num(0xB5258F6C), Num(0x4D), Num(0xE)]),
            (true, [Num(0xB5258F6C), Num(0x4D), Num(0xE)]),
            (true, [Num(0xB5C1ACC9), Num(0x2B), Num(0x0)]),
            (true, [Num(0xB5C1ACC9), Num(0x4D), Num(0xE)]),
            (true, [Num(0xB5C1ACC9), Num(0x4D), Num(0xE)]),
            (true, [Num(0xC0000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xD0000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xDC22388C), Num(0x2B), Num(0x0)]),
            (true, [Num(0xDC22388C), Num(0x4D), Num(0xE)]),
            (true, [Num(0xDC22388C), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE0000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE0000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE0000040), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE0000040), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE0000040), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE2463640), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE2463640), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE2463640), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE8000000), Num(0x2B), Num(0x0)]),
            (true, [Num(0xE8000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xE8000000), Num(0x4D), Num(0xE)]),
            (true, [Num(0xEB5E06B7), Num(0x2B), Num(0x0)]),
            (true, [Num(0xEB5E06B7), Num(0x4D), Num(0xE)]),
            (true, [Num(0xEB5E06B7), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFD693E8D), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFFFE4D65), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFFFE4D65), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFFFE4D65), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFFFEC0F1), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFFFEC0F1), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFFFEC0F1), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFFFFFFFF), Num(0x2B), Num(0x0)]),
            (true, [Num(0xFFFFFFFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0xFFFFFFFF), Num(0x4D), Num(0xE)]),
            (true, [Num(0x8), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1E), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x18D), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x800), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x4B5C), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x5E00), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1CFC5), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x80988), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x3034F4), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x60A4E8), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6BDD85), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xA00000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xF20000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1517C28), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x4000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x4000001), Num(0x4D), Num(0x0)]),
            (true, [Num(0x8000001), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x16D7F216), Num(0x4D), Num(0x0)]),
            (true, [Num(0x1BD00000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x1BD00000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x28400000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x28400000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x2A000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x2B001000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x2B001000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x2C216800), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x2C216800), Num(0x4D), Num(0x0)]),
            (true, [Num(0x38000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x38000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x3F007FFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x3F007FFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x4050FFFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x4050FFFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x50000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x5C11296F), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x5C11296F), Num(0x4D), Num(0x0)]),
            (true, [Num(0x68000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x6A000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6A000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0x6A000020), Num(0x4D), Num(0x0)]),
            (true, [Num(0x6D91C0CB), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x6D91C0CB), Num(0x4D), Num(0x0)]),
            (true, [Num(0x80007F00), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0x88DD5FFF), Num(0x4D), Num(0x0)]),
            (true, [Num(0x94000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xA72B4A50), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xA72B4A50), Num(0x4D), Num(0x0)]),
            (true, [Num(0xB5258F6C), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xB5258F6C), Num(0x4D), Num(0x0)]),
            (true, [Num(0xB5C1ACC9), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xB5C1ACC9), Num(0x4D), Num(0x0)]),
            (true, [Num(0xD0000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xDC22388C), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xDC22388C), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE0000040), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE2463640), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE2463640), Num(0x4D), Num(0x0)]),
            (true, [Num(0xE8000000), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xE8000000), Num(0x4D), Num(0x0)]),
            (true, [Num(0xEB5E06B7), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xEB5E06B7), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFD693E8D), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFD693E8D), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFFFE4D65), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFFFE4D65), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFFFEC0F1), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFFFEC0F1), Num(0x4D), Num(0x0)]),
            (true, [Num(0xFFFFFFFF), Num(0x2B), Num(0x189E6F)]),
            (true, [Num(0xFFFFFFFF), Num(0x4D), Num(0x0)]),
            (false, [Num(0x0), Num(0x15), Num(0xE)]),
            (false, [Num(0x0), Num(0x15), Num(0xE)]),
            (false, [Num(0xE0000000), Num(0x15), Num(0xE)]),
            (false, [Num(0xE0000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x9), Num(0x15), Num(0xE)]),
            (false, [Num(0x9), Num(0x15), Num(0xE)]),
            (false, [Num(0x28400000), Num(0x15), Num(0xE)]),
            (false, [Num(0x28400000), Num(0x15), Num(0xE)]),
            (false, [Num(0x3), Num(0x15), Num(0xE)]),
            (false, [Num(0x3), Num(0x15), Num(0xE)]),
            (false, [Num(0xC0000000), Num(0x15), Num(0xE)]),
            (false, [Num(0xC0000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x20), Num(0x15), Num(0xE)]),
            (false, [Num(0x20), Num(0x15), Num(0xE)]),
            (false, [Num(0x4B5C), Num(0x15), Num(0xE)]),
            (false, [Num(0x4B5C), Num(0x15), Num(0xE)]),
            (false, [Num(0x1CFC5), Num(0x15), Num(0xE)]),
            (false, [Num(0x1CFC5), Num(0x15), Num(0xE)]),
            (false, [Num(0x60A4E8), Num(0x15), Num(0xE)]),
            (false, [Num(0x60A4E8), Num(0x15), Num(0xE)]),
            (false, [Num(0x800), Num(0x15), Num(0xE)]),
            (false, [Num(0x800), Num(0x15), Num(0xE)]),
            (false, [Num(0x4050FFFF), Num(0x15), Num(0xE)]),
            (false, [Num(0x4050FFFF), Num(0x15), Num(0xE)]),
            (false, [Num(0x6A000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x6A000000), Num(0x15), Num(0xE)]),
            (false, [Num(0xA00000), Num(0x15), Num(0xE)]),
            (false, [Num(0xA00000), Num(0x15), Num(0xE)]),
            (false, [Num(0x0), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x0), Num(0x2B), Num(0xE)]),
            (false, [Num(0x0), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x20), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0xC0000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0xD0000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0xE0000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0xD0000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0xD0000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x0), Num(0x2B), Num(0xE)]),
            (false, [Num(0x0), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x2B), Num(0xE)]),
            (false, [Num(0x3), Num(0x2B), Num(0xE)]),
            (false, [Num(0x9), Num(0x2B), Num(0xE)]),
            (false, [Num(0x9), Num(0x2B), Num(0xE)]),
            (false, [Num(0x20), Num(0x2B), Num(0xE)]),
            (false, [Num(0x20), Num(0x2B), Num(0xE)]),
            (false, [Num(0x800), Num(0x2B), Num(0xE)]),
            (false, [Num(0x800), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4B5C), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4B5C), Num(0x2B), Num(0xE)]),
            (false, [Num(0x1CFC5), Num(0x2B), Num(0xE)]),
            (false, [Num(0x1CFC5), Num(0x2B), Num(0xE)]),
            (false, [Num(0x60A4E8), Num(0x2B), Num(0xE)]),
            (false, [Num(0x60A4E8), Num(0x2B), Num(0xE)]),
            (false, [Num(0xA00000), Num(0x2B), Num(0xE)]),
            (false, [Num(0xA00000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4050FFFF), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4050FFFF), Num(0x2B), Num(0xE)]),
            (false, [Num(0xC0000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0xC0000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0xD0000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0xE0000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x0), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x20), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x20), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x6A000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x6A000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0xC0000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0xC0000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x3034F4), Num(0x15), Num(0xE)]),
            (false, [Num(0x3034F4), Num(0x15), Num(0xE)]),
            (false, [Num(0x3034F4), Num(0x2B), Num(0xE)]),
            (false, [Num(0x3034F4), Num(0x2B), Num(0xE)]),
            (false, [Num(0x1E), Num(0x15), Num(0xE)]),
            (false, [Num(0x1E), Num(0x15), Num(0xE)]),
            (false, [Num(0x1E), Num(0x2B), Num(0xE)]),
            (false, [Num(0x1E), Num(0x2B), Num(0xE)]),
            (false, [Num(0x8), Num(0x15), Num(0xE)]),
            (false, [Num(0x8), Num(0x15), Num(0xE)]),
            (false, [Num(0x8), Num(0x2B), Num(0xE)]),
            (false, [Num(0x8), Num(0x2B), Num(0xE)]),
            (false, [Num(0x68000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x68000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x68000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x68000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x78), Num(0x15), Num(0xE)]),
            (false, [Num(0x78), Num(0x15), Num(0xE)]),
            (false, [Num(0x78), Num(0x2B), Num(0xE)]),
            (false, [Num(0x78), Num(0x2B), Num(0xE)]),
            (false, [Num(0x94000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x94000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x94000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x94000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x18D), Num(0x15), Num(0xE)]),
            (false, [Num(0x18D), Num(0x15), Num(0xE)]),
            (false, [Num(0x18D), Num(0x2B), Num(0xE)]),
            (false, [Num(0x18D), Num(0x2B), Num(0xE)]),
            (false, [Num(0x50000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x50000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x50000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x50000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x10000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x10000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x10000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x10000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x749), Num(0x15), Num(0xE)]),
            (false, [Num(0x749), Num(0x15), Num(0xE)]),
            (false, [Num(0x749), Num(0x2B), Num(0xE)]),
            (false, [Num(0x749), Num(0x2B), Num(0xE)]),
            (false, [Num(0xE8000000), Num(0x15), Num(0xE)]),
            (false, [Num(0xE8000000), Num(0x15), Num(0xE)]),
            (false, [Num(0xE8000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0xE8000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x5E00), Num(0x15), Num(0xE)]),
            (false, [Num(0x5E00), Num(0x15), Num(0xE)]),
            (false, [Num(0x5E00), Num(0x2B), Num(0xE)]),
            (false, [Num(0x5E00), Num(0x2B), Num(0xE)]),
            (false, [Num(0xF40F), Num(0x15), Num(0xE)]),
            (false, [Num(0xF40F), Num(0x15), Num(0xE)]),
            (false, [Num(0xF40F), Num(0x2B), Num(0xE)]),
            (false, [Num(0xF40F), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x4000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x2A000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x2A000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x2A000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x2A000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x10000001), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x10000001), Num(0x2B), Num(0xE)]),
            (false, [Num(0x10000001), Num(0x2B), Num(0xE)]),
            (false, [Num(0x8000001), Num(0x15), Num(0xE)]),
            (false, [Num(0x8000001), Num(0x15), Num(0xE)]),
            (false, [Num(0x8000001), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x8000001), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x4000001), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x4000001), Num(0x2B), Num(0xE)]),
            (false, [Num(0x4000001), Num(0x2B), Num(0xE)]),
            (false, [Num(0x80007F00), Num(0x15), Num(0xE)]),
            (false, [Num(0x80007F00), Num(0x15), Num(0xE)]),
            (false, [Num(0x80007F00), Num(0x2B), Num(0xE)]),
            (false, [Num(0x80007F00), Num(0x2B), Num(0xE)]),
            (false, [Num(0x2000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x2000000), Num(0x15), Num(0xE)]),
            (false, [Num(0x2000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x2000000), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x6A000020), Num(0x15), Num(0xE)]),
            (false, [Num(0x6A000020), Num(0x15), Num(0xE)]),
            (false, [Num(0x6A000020), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x6A000020), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0xE0000040), Num(0x15), Num(0xE)]),
            (false, [Num(0xE0000040), Num(0x15), Num(0xE)]),
            (false, [Num(0xE0000040), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0xE0000040), Num(0x15), Num(0x189E6F)]),
            (false, [Num(0x10), Num(0x15), Num(0xE)]),
            (false, [Num(0x10), Num(0x15), Num(0xE)]),
            (false, [Num(0x10), Num(0x2B), Num(0xE)]),
            (false, [Num(0x10), Num(0x2B), Num(0xE)]),
            (false, [Num(0x0), Num(0x15), Num(0x0)]),
            (false, [Num(0x0), Num(0x2B), Num(0x0)]),
            (false, [Num(0x0), Num(0x2B), Num(0x0)]),
            (false, [Num(0x0), Num(0x4D), Num(0x0)]),
            (false, [Num(0x0), Num(0x4D), Num(0xE)]),
            (false, [Num(0x0), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x0), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x4D), Num(0x0)]),
            (false, [Num(0x8), Num(0x4D), Num(0x0)]),
            (false, [Num(0x9), Num(0x15), Num(0x0)]),
            (false, [Num(0x9), Num(0x2B), Num(0x0)]),
            (false, [Num(0x9), Num(0x4D), Num(0x0)]),
            (false, [Num(0x9), Num(0x4D), Num(0xE)]),
            (false, [Num(0x10), Num(0x4D), Num(0x0)]),
            (false, [Num(0x1E), Num(0x4D), Num(0x0)]),
            (false, [Num(0x20), Num(0x4D), Num(0x0)]),
            (false, [Num(0x78), Num(0x4D), Num(0x0)]),
            (false, [Num(0x18D), Num(0x4D), Num(0x0)]),
            (false, [Num(0x749), Num(0x4D), Num(0x0)]),
            (false, [Num(0x800), Num(0x4D), Num(0x0)]),
            (false, [Num(0x4B5C), Num(0x4D), Num(0x0)]),
            (false, [Num(0x5E00), Num(0x4D), Num(0x0)]),
            (false, [Num(0xF40F), Num(0x4D), Num(0x0)]),
            (false, [Num(0x1CFC5), Num(0x4D), Num(0x0)]),
            (false, [Num(0x328F2), Num(0x2B), Num(0x0)]),
            (false, [Num(0x328F2), Num(0x4D), Num(0x0)]),
            (false, [Num(0x80988), Num(0x4D), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x4D), Num(0x0)]),
            (false, [Num(0x60A4E8), Num(0x4D), Num(0x0)]),
            (false, [Num(0x6BDD85), Num(0x4D), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x4D), Num(0x0)]),
            (false, [Num(0xF20000), Num(0x4D), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x4D), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x4D), Num(0x0)]),
            (false, [Num(0x10000001), Num(0x4D), Num(0x0)]),
            (false, [Num(0x14000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x14000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x14000000), Num(0x2B), Num(0xE)]),
            (false, [Num(0x14000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x80007F00), Num(0x4D), Num(0x0)]),
            (false, [Num(0xD0000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0xE0000000), Num(0x15), Num(0x0)]),
            (false, [Num(0xE0000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x3), Num(0x2B), Num(0x0)]),
            (false, [Num(0x3), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x8), Num(0x2B), Num(0x0)]),
            (false, [Num(0x9), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10), Num(0x2B), Num(0x0)]),
            (false, [Num(0x1E), Num(0x2B), Num(0x0)]),
            (false, [Num(0x20), Num(0x2B), Num(0x0)]),
            (false, [Num(0x20), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x78), Num(0x2B), Num(0x0)]),
            (false, [Num(0x18D), Num(0x2B), Num(0x0)]),
            (false, [Num(0x749), Num(0x2B), Num(0x0)]),
            (false, [Num(0x800), Num(0x2B), Num(0x0)]),
            (false, [Num(0x4B5C), Num(0x2B), Num(0x0)]),
            (false, [Num(0x5E00), Num(0x2B), Num(0x0)]),
            (false, [Num(0xF40F), Num(0x2B), Num(0x0)]),
            (false, [Num(0x1CFC5), Num(0x2B), Num(0x0)]),
            (false, [Num(0x328F2), Num(0x15), Num(0x0)]),
            (false, [Num(0x328F2), Num(0x2B), Num(0x0)]),
            (false, [Num(0x80988), Num(0x2B), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x2B), Num(0x0)]),
            (false, [Num(0x60A4E8), Num(0x2B), Num(0x0)]),
            (false, [Num(0x6BDD85), Num(0x2B), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x2B), Num(0x0)]),
            (false, [Num(0xF20000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x4000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x4000001), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x10000001), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10000001), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x4050FFFF), Num(0x2B), Num(0x0)]),
            (false, [Num(0x50000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x80007F00), Num(0x2B), Num(0x0)]),
            (false, [Num(0x94000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0xC0000000), Num(0x15), Num(0x0)]),
            (false, [Num(0xC0000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x0), Num(0x15), Num(0x0)]),
            (false, [Num(0x3), Num(0x15), Num(0x0)]),
            (false, [Num(0x8), Num(0x15), Num(0x0)]),
            (false, [Num(0x9), Num(0x15), Num(0x0)]),
            (false, [Num(0x10), Num(0x15), Num(0x0)]),
            (false, [Num(0x1E), Num(0x15), Num(0x0)]),
            (false, [Num(0x20), Num(0x15), Num(0x0)]),
            (false, [Num(0x78), Num(0x15), Num(0x0)]),
            (false, [Num(0x18D), Num(0x15), Num(0x0)]),
            (false, [Num(0x749), Num(0x15), Num(0x0)]),
            (false, [Num(0x800), Num(0x15), Num(0x0)]),
            (false, [Num(0x4B5C), Num(0x15), Num(0x0)]),
            (false, [Num(0x5E00), Num(0x15), Num(0x0)]),
            (false, [Num(0xF40F), Num(0x15), Num(0x0)]),
            (false, [Num(0x1CFC5), Num(0x15), Num(0x0)]),
            (false, [Num(0x328F2), Num(0x15), Num(0x0)]),
            (false, [Num(0x80988), Num(0x15), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x15), Num(0x0)]),
            (false, [Num(0x60A4E8), Num(0x15), Num(0x0)]),
            (false, [Num(0x6BDD85), Num(0x15), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x15), Num(0x0)]),
            (false, [Num(0xF20000), Num(0x15), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x4D), Num(0xE)]),
            (false, [Num(0x2000000), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x8000001), Num(0x15), Num(0x0)]),
            (false, [Num(0x28400000), Num(0x15), Num(0x0)]),
            (false, [Num(0x2A000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x4050FFFF), Num(0x15), Num(0x0)]),
            (false, [Num(0x68000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x6A000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x6A000020), Num(0x15), Num(0x0)]),
            (false, [Num(0x80007F00), Num(0x15), Num(0x0)]),
            (false, [Num(0x88DD5FFF), Num(0x15), Num(0x0)]),
            (false, [Num(0xE0000040), Num(0x15), Num(0x0)]),
            (false, [Num(0xE2463640), Num(0x15), Num(0x0)]),
            (false, [Num(0xE8000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x0), Num(0x4D), Num(0x0)]),
            (false, [Num(0x3), Num(0x15), Num(0x0)]),
            (false, [Num(0x8), Num(0x15), Num(0x0)]),
            (false, [Num(0x9), Num(0x4D), Num(0x0)]),
            (false, [Num(0x10), Num(0x15), Num(0x0)]),
            (false, [Num(0x1E), Num(0x15), Num(0x0)]),
            (false, [Num(0x20), Num(0x15), Num(0x0)]),
            (false, [Num(0x78), Num(0x15), Num(0x0)]),
            (false, [Num(0x18D), Num(0x15), Num(0x0)]),
            (false, [Num(0x749), Num(0x15), Num(0x0)]),
            (false, [Num(0x800), Num(0x15), Num(0x0)]),
            (false, [Num(0x4B5C), Num(0x15), Num(0x0)]),
            (false, [Num(0x5E00), Num(0x15), Num(0x0)]),
            (false, [Num(0xF40F), Num(0x15), Num(0x0)]),
            (false, [Num(0x1CFC5), Num(0x15), Num(0x0)]),
            (false, [Num(0x80988), Num(0x15), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x15), Num(0x0)]),
            (false, [Num(0x60A4E8), Num(0x15), Num(0x0)]),
            (false, [Num(0x6BDD85), Num(0x15), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x15), Num(0x0)]),
            (false, [Num(0xF20000), Num(0x15), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x8000001), Num(0x15), Num(0x0)]),
            (false, [Num(0x28400000), Num(0x15), Num(0x0)]),
            (false, [Num(0x2A000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x4050FFFF), Num(0x15), Num(0x0)]),
            (false, [Num(0x68000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x6A000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x6A000020), Num(0x15), Num(0x0)]),
            (false, [Num(0x80007F00), Num(0x15), Num(0x0)]),
            (false, [Num(0x88DD5FFF), Num(0x15), Num(0x0)]),
            (false, [Num(0xC0000000), Num(0x15), Num(0x0)]),
            (false, [Num(0xE0000040), Num(0x15), Num(0x0)]),
            (false, [Num(0xE2463640), Num(0x15), Num(0x0)]),
            (false, [Num(0xE8000000), Num(0x15), Num(0x0)]),
            (false, [Num(0x0), Num(0x4D), Num(0xE)]),
            (false, [Num(0x3), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x8), Num(0x4D), Num(0x0)]),
            (false, [Num(0x8), Num(0x4D), Num(0xE)]),
            (false, [Num(0x20), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x328F2), Num(0x4D), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x4D), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x4D), Num(0xE)]),
            (false, [Num(0x10000000), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x10000001), Num(0x4D), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x2B), Num(0x0)]),
            (false, [Num(0x3), Num(0x4D), Num(0xE)]),
            (false, [Num(0x3), Num(0x4D), Num(0xE)]),
            (false, [Num(0x8), Num(0x2B), Num(0x0)]),
            (false, [Num(0x8), Num(0x4D), Num(0xE)]),
            (false, [Num(0x9), Num(0x4D), Num(0xE)]),
            (false, [Num(0x10), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10), Num(0x4D), Num(0xE)]),
            (false, [Num(0x10), Num(0x4D), Num(0xE)]),
            (false, [Num(0x1E), Num(0x2B), Num(0x0)]),
            (false, [Num(0x1E), Num(0x4D), Num(0xE)]),
            (false, [Num(0x1E), Num(0x4D), Num(0xE)]),
            (false, [Num(0x20), Num(0x2B), Num(0x0)]),
            (false, [Num(0x20), Num(0x4D), Num(0xE)]),
            (false, [Num(0x20), Num(0x4D), Num(0xE)]),
            (false, [Num(0x78), Num(0x2B), Num(0x0)]),
            (false, [Num(0x78), Num(0x4D), Num(0xE)]),
            (false, [Num(0x78), Num(0x4D), Num(0xE)]),
            (false, [Num(0x18D), Num(0x2B), Num(0x0)]),
            (false, [Num(0x18D), Num(0x4D), Num(0xE)]),
            (false, [Num(0x18D), Num(0x4D), Num(0xE)]),
            (false, [Num(0x749), Num(0x2B), Num(0x0)]),
            (false, [Num(0x749), Num(0x4D), Num(0xE)]),
            (false, [Num(0x749), Num(0x4D), Num(0xE)]),
            (false, [Num(0x800), Num(0x2B), Num(0x0)]),
            (false, [Num(0x800), Num(0x4D), Num(0xE)]),
            (false, [Num(0x800), Num(0x4D), Num(0xE)]),
            (false, [Num(0x4B5C), Num(0x2B), Num(0x0)]),
            (false, [Num(0x4B5C), Num(0x4D), Num(0xE)]),
            (false, [Num(0x4B5C), Num(0x4D), Num(0xE)]),
            (false, [Num(0x5E00), Num(0x2B), Num(0x0)]),
            (false, [Num(0x5E00), Num(0x4D), Num(0xE)]),
            (false, [Num(0x5E00), Num(0x4D), Num(0xE)]),
            (false, [Num(0xF40F), Num(0x2B), Num(0x0)]),
            (false, [Num(0xF40F), Num(0x4D), Num(0xE)]),
            (false, [Num(0xF40F), Num(0x4D), Num(0xE)]),
            (false, [Num(0x1CFC5), Num(0x2B), Num(0x0)]),
            (false, [Num(0x1CFC5), Num(0x4D), Num(0xE)]),
            (false, [Num(0x1CFC5), Num(0x4D), Num(0xE)]),
            (false, [Num(0x80988), Num(0x2B), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x2B), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x4D), Num(0xE)]),
            (false, [Num(0x3034F4), Num(0x4D), Num(0xE)]),
            (false, [Num(0x60A4E8), Num(0x2B), Num(0x0)]),
            (false, [Num(0x60A4E8), Num(0x4D), Num(0xE)]),
            (false, [Num(0x60A4E8), Num(0x4D), Num(0xE)]),
            (false, [Num(0x6BDD85), Num(0x2B), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x2B), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x4D), Num(0xE)]),
            (false, [Num(0xA00000), Num(0x4D), Num(0xE)]),
            (false, [Num(0xF20000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x4D), Num(0xE)]),
            (false, [Num(0x4000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x4000001), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10000000), Num(0x4D), Num(0xE)]),
            (false, [Num(0x10000001), Num(0x2B), Num(0x0)]),
            (false, [Num(0x10000001), Num(0x4D), Num(0xE)]),
            (false, [Num(0x10000001), Num(0x4D), Num(0xE)]),
            (false, [Num(0x14000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x4050FFFF), Num(0x2B), Num(0x0)]),
            (false, [Num(0x50000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x80007F00), Num(0x2B), Num(0x0)]),
            (false, [Num(0x80007F00), Num(0x4D), Num(0xE)]),
            (false, [Num(0x80007F00), Num(0x4D), Num(0xE)]),
            (false, [Num(0x94000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0xC0000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0xD0000000), Num(0x2B), Num(0x0)]),
            (false, [Num(0x3), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x3), Num(0x4D), Num(0x0)]),
            (false, [Num(0x10), Num(0x4D), Num(0x0)]),
            (false, [Num(0x1E), Num(0x4D), Num(0x0)]),
            (false, [Num(0x20), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x20), Num(0x4D), Num(0x0)]),
            (false, [Num(0x78), Num(0x4D), Num(0x0)]),
            (false, [Num(0x18D), Num(0x4D), Num(0x0)]),
            (false, [Num(0x749), Num(0x4D), Num(0x0)]),
            (false, [Num(0x800), Num(0x4D), Num(0x0)]),
            (false, [Num(0x4B5C), Num(0x4D), Num(0x0)]),
            (false, [Num(0x5E00), Num(0x4D), Num(0x0)]),
            (false, [Num(0xF40F), Num(0x4D), Num(0x0)]),
            (false, [Num(0x1CFC5), Num(0x4D), Num(0x0)]),
            (false, [Num(0x80988), Num(0x4D), Num(0x0)]),
            (false, [Num(0x3034F4), Num(0x4D), Num(0x0)]),
            (false, [Num(0x60A4E8), Num(0x4D), Num(0x0)]),
            (false, [Num(0x6BDD85), Num(0x4D), Num(0x0)]),
            (false, [Num(0xA00000), Num(0x4D), Num(0x0)]),
            (false, [Num(0xF20000), Num(0x4D), Num(0x0)]),
            (false, [Num(0x2000000), Num(0x4D), Num(0x0)]),
            (false, [Num(0x4000001), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x10000001), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x10000001), Num(0x4D), Num(0x0)]),
            (false, [Num(0x14000000), Num(0x2B), Num(0x189E6F)]),
            (false, [Num(0x80007F00), Num(0x4D), Num(0x0)]),
            (false, [Num(0xC0000000), Num(0x2B), Num(0x189E6F)]),
        ];

        let mut s = SimplePredicateCombiner::new(
            &[
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 7,
                },
                IoType::Integer {
                    num_bits: 24,
                },
            ],
            vec![0, 1, 2],
            IoType::Integer {
                num_bits: 1,
            },
        );
        test_with_cases(&mut s, cases);

        println!("{}", s.hypothesis().unwrap());
    }
}
