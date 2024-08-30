use liblisa::semantics::default::computation::OutputEncoding;
use liblisa::semantics::IoType;
use liblisa::value::AsValue;
use log::{debug, info};

use super::searcher::{CheckFlippableBoolResult, Searcher};
use crate::predicate::Term;
use crate::templates::preprocess::PreprocessedTemplate;
use crate::templates::SIMPLE_BOOLEAN_TEMPLATES;
use crate::{Synthesizer, SynthesizerBase};

#[derive(Clone)]
pub struct BoolTermSearcher<'a> {
    searcher: Searcher<'a, CheckFlippableBoolResult>,
    hypothesis: Option<Term>,
}

impl std::fmt::Debug for BoolTermSearcher<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoolTermSearcher")
            .field("hypothesis", &self.hypothesis)
            .finish()
    }
}

impl SynthesizerBase for BoolTermSearcher<'_> {
    type Hypothesis = Term;
    type Computation = Term;

    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        Self::new_with_custom_templates(&SIMPLE_BOOLEAN_TEMPLATES, input_types, output_type)
    }

    fn hypothesis(&self) -> Option<&Self::Hypothesis> {
        self.hypothesis.as_ref()
    }

    fn has_given_up(&self) -> bool {
        false
    }

    fn needs_requester(&self) -> bool {
        false
    }

    fn into_computation(self) -> Option<Self::Computation> {
        self.hypothesis
    }
}

impl Synthesizer<bool> for BoolTermSearcher<'_> {
    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: bool) -> bool {
        self.hypothesis
            .as_ref()
            .map(|hyp| hyp.evaluate(inputs) == output)
            .unwrap_or(false)
    }

    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: bool) {
        info!("Added: {inputs:X?} -> {output}");

        self.searcher.add_case(inputs, output);

        if !self.is_consistent(inputs, output) {
            debug!(
                "Not consistent: hypothesis expected {:X?}",
                self.hypothesis.as_ref().map(|hyp| hyp.evaluate(inputs))
            );
            self.step_next();
        }
    }
}

impl BoolTermSearcher<'_> {
    pub fn new_with_custom_templates(
        templates: &'static [PreprocessedTemplate], input_types: &[IoType], output_type: IoType,
    ) -> Self {
        assert_eq!(
            output_type,
            IoType::Integer {
                num_bits: 1
            }
        );
        Self {
            searcher: Searcher::new_with_custom_templates(templates, input_types, output_type),
            hypothesis: None,
        }
    }

    pub fn step_next(&mut self) {
        self.hypothesis = self.searcher.next_expr().map(|(computation, check)| Term::Predicate {
            negate: check.flip(),
            predicate: computation.to_template_computation(OutputEncoding::UnsignedBigEndian),
        });
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::IoType;
    use liblisa::value::{AsValue, Value};
    use test_log::test;

    use crate::search::termsearcher::BoolTermSearcher;
    use crate::{synthesize_from_fn, SynthesizerBase};

    #[test]
    pub fn find_lt() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = BoolTermSearcher::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[0].unwrap_num() < inputs[1].unwrap_num());
        let term = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f).unwrap();
        println!("{term}");
    }

    #[test]
    pub fn find_leq_int() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = BoolTermSearcher::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[0].unwrap_num() <= inputs[1].unwrap_num());
        let term = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f).unwrap();
        println!("{term}");
    }

    #[test]
    pub fn find_leq_bytes() {
        let inputs = &[
            IoType::Bytes {
                num_bytes: 1,
            },
            IoType::Bytes {
                num_bytes: 1,
            },
        ];
        let s = BoolTermSearcher::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[0].unwrap_bytes()[0] <= inputs[1].unwrap_bytes()[0]);
        let term = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f).unwrap();
        println!("{term}");
    }

    #[test]
    pub fn find_gt() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = BoolTermSearcher::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[0].unwrap_num() > inputs[1].unwrap_num());
        let term = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f).unwrap();
        println!("{term}");
    }
    #[test]
    pub fn find_geq() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = BoolTermSearcher::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[0].unwrap_num() >= inputs[1].unwrap_num());
        let term = synthesize_from_fn(&mut rand::thread_rng(), s, inputs, f).unwrap();
        println!("{term}");
    }
}
