use std::fmt::{self, Debug, Display};
use std::iter::once;
use std::marker::PhantomData;
use std::time::Instant;

use itertools::Itertools;
use liblisa::semantics::default::builder::hole;
use liblisa::semantics::default::computation::{
    Arg, AsComputationRef, ExpressionComputation, OutputEncoding, SynthesizedComputation,
};
use liblisa::semantics::default::{expr, Expr};
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::Timeout;
use liblisa::value::{AsValue, OwnedValue, Value, ValueArrayEquality};
use log::{debug, info, trace};

use super::expr_finder::bitmap_mcs::BitmapMcsExpressionFinder;
use super::expr_finder::ExpressionFinder;
use super::Case;
use crate::cond::casemap::CaseMap;
use crate::cond::switch::Switch;
use crate::cond::synthesizer::ConditionSynthesizer;
use crate::normalizer::ComputationNormalizer;
use crate::{InputSlice, Requester, Synthesizer, SynthesizerBase, SynthesizerOutput};

/// The default synthesizer, using templates and decision trees.
pub type DefaultTreeTemplateSynthesizer = TreeTemplateSynthesizer<BitmapMcsExpressionFinder>;

#[derive(Clone)]
pub struct TreeTemplateSynthesizer<F: ExpressionFinder> {
    expression_finder: F,
    condition_synthesizer: ConditionSynthesizer,
    mcs: Vec<ExpressionComputation>,
    cases: Vec<Case>,

    input_types: Vec<IoType>,
    hypothesis: Option<Hypothesis>,
    failed: bool,
    timeout: Timeout,
    oks: usize,
    choices_ok: usize,
    cases_seen: usize,
    wait_for_new_info: bool,
    waiting_for_new_choices: usize,
    can_build: bool,
}

#[derive(Clone, Debug)]
pub struct Hypothesis {
    switch: Switch,
    outputs: Vec<SynthesizedComputation>,
}

#[derive(Debug)]
pub struct DisplayHypothesis<'a>(&'a Hypothesis);

impl std::fmt::Display for DisplayHypothesis<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "index {} into {:?}",
            self.0.switch.display(ARG_NAMES),
            self.0
                .outputs
                .iter()
                .map(|c| c.display(ARG_NAMES).to_string())
                .collect::<Vec<_>>()
        )
    }
}

impl Computation for Hypothesis {
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue {
        let index = self.switch.evaluate(inputs);
        self.outputs[index].evaluate(inputs)
    }

    fn compare_eq<V: AsValue>(&self, inputs: &[V], expected: Value) -> bool {
        let index = self.switch.evaluate(inputs);
        self.outputs[index].compare_eq(inputs, expected)
    }

    fn display<'a, S: AsRef<str>>(&'a self, _input_names: &'a [S]) -> impl Display + Debug + 'a {
        DisplayHypothesis(self)
    }

    fn used_input_indices(&self) -> Vec<usize> {
        let mut seen = GrowingBitmap::new();
        self.switch
            .used_input_indices()
            .into_iter()
            .chain(self.outputs.iter().flat_map(|expr| expr.used_input_indices()))
            .filter(|&n| seen.set(n))
            .collect()
    }

    fn remap_inputs(&mut self, map: &[Option<usize>]) {
        self.switch.remap_inputs(map);
        for output in self.outputs.iter_mut() {
            output.remap_inputs(map);
        }
    }

    fn is_identity(&self) -> bool {
        self.outputs.len() == 1 && self.outputs[0].is_identity()
    }
}

struct CaseMapRequester<'a, R, Output> {
    choices: &'a [ExpressionComputation],
    requester: &'a mut R,
    missing_choices: &'a mut Vec<(Vec<OwnedValue>, OwnedValue)>,
    timeout: Timeout,
    _phantom: PhantomData<fn() -> Output>,
}

impl<Output: SynthesizerOutput, R: Requester<Output>> Requester<CaseMap> for CaseMapRequester<'_, R, Output>
where
    Output: AsValue,
{
    fn request<V: AsValue>(&mut self, inputs: &[V]) -> Option<CaseMap> {
        if self.timeout.is_timed_out() {
            Some(CaseMap::new_from_u64(1))
        } else {
            let result = self.requester.request(inputs);

            trace!("Requester: [{:X?}] => {:X?}", inputs, result);

            result.map(|output| {
                let result = CaseMap::new(
                    self.choices
                        .iter()
                        .map(|choice| choice.as_internal().compare_eq(inputs, output.as_value())),
                );
                if result.is_none() {
                    debug!("Missing choice for: {:X?} -> {:X?} in {:X?}", inputs, output, self.choices);
                    self.missing_choices.push((inputs.as_owned(), output.to_owned_value()));
                }

                result
            })
        }
    }

    fn request_debug<V: AsValue>(&mut self, inputs: &[V]) -> Option<CaseMap> {
        let output = self.requester.request_debug(inputs);

        println!("Requester: [{inputs:X?}] => {output:X?}");

        output.map(|output| {
            let result = CaseMap::new(
                self.choices
                    .iter()
                    .map(|choice| choice.as_internal().compare_eq(inputs, output.as_value())),
            );
            println!("Mapping {output:X?} to output {result:?}"); // TODO: result.as_ref().map(|result| choices[result.as_integer() as usize].expr.display(ARG_NAMES).to_string()).unwrap_or_default()

            println!("Other choices:");
            for choice in self.choices.iter() {
                println!(" - {} = {:X?}", choice.display(ARG_NAMES), choice.evaluate(inputs));
            }

            result
        })
    }
}

const CONDITION_SYNTHESIZER_ACTIVATION_THRESHOLD: usize = 5000;

impl<F: ExpressionFinder> TreeTemplateSynthesizer<F> {
    pub fn input_types(&self) -> &[IoType] {
        &self.input_types
    }

    fn add_new_choice<V: AsValue>(&mut self, inputs: &[V], output: Value<'_>) {
        if self.timeout.is_timed_out() {
            return
        }

        self.cases.push(Case {
            inputs: inputs.as_owned(),
            output: output.to_owned_value(),
        });

        self.choices_ok = 0;
        self.expression_finder.add_case(inputs, output);

        loop {
            if self.expression_finder.has_given_up() || self.timeout.is_timed_out() {
                self.failed = true;
                self.mcs.clear();
                return
            } else {
                info!("Constructing new condition synthesizer");
                self.condition_synthesizer = ConditionSynthesizer::new(
                    &self.input_types,
                    IoType::Integer {
                        num_bits: 8,
                    },
                );
                self.mcs = self.expression_finder.find_expressions();
                info!("Mcs = {}", self.mcs.iter().map(|e| e.display(ARG_NAMES)).format(", "));

                if self.expression_finder.has_given_up() {
                    self.failed = true;
                    return
                }

                if let Some(missed) = self
                    .cases
                    .iter()
                    .find(|case| !self.mcs.iter().any(|expr| expr.compare_eq(case.inputs(), case.output())))
                {
                    debug!("MCS has missed {:X?} -> {:X?}", missed.inputs(), missed.output());
                    self.expression_finder.add_case(missed.inputs(), missed.output());
                } else {
                    break
                }
            }
        }
    }

    /// Returns true if the new case adds any new information
    fn check<V: AsValue, O: SynthesizerOutput + AsValue + for<'v> From<Value<'v>>>(
        &mut self, inputs: &[V], output: O, requester: &mut impl Requester<O>, add_to_condition_synthesizer: bool,
    ) -> bool {
        debug!("Checking: {inputs:X?} => {output:X?}");
        if self.failed {
            debug!("self.failed=true, so we abort early...");
            return false
        }

        self.cases_seen += 1;

        let casemap = CaseMap::new(self.mcs.iter().map(|expr| expr.compare_eq(inputs, output.as_value())));
        debug!("Casemap: {casemap:?}");
        if let Some(hypothesis) = &self.hypothesis {
            if hypothesis.compare_eq(inputs, output.as_value()) {
                let increases_variety = self.condition_synthesizer.increases_variety(inputs);
                let group_conditions_are_consistent = self
                    .condition_synthesizer
                    .group_conditions_are_consistent(
                        inputs,
                        &casemap,
                        &mut CaseMapRequester {
                            choices: &self.mcs,
                            requester,
                            missing_choices: &mut Vec::new(),
                            timeout: self.timeout,
                            _phantom: Default::default(),
                        },
                    )
                    .unwrap_or(false);

                if !increases_variety && group_conditions_are_consistent {
                    self.choices_ok += 1;
                    self.oks += 1;

                    return false;
                }
            } else {
                info!(
                    "Hypothesis {} was wrong: found {:X?} but expected {:X?}",
                    hypothesis.display(ARG_NAMES),
                    hypothesis.evaluate(inputs),
                    output
                );

                self.wait_for_new_info = false;
                self.oks = 0;
                self.hypothesis = None;
            }
        }

        if !casemap.is_empty() {
            self.choices_ok += 1;

            if add_to_condition_synthesizer
                && self.condition_synthesizer.has_given_up()
                && self.choices_ok >= CONDITION_SYNTHESIZER_ACTIVATION_THRESHOLD + 2000
            {
                self.waiting_for_new_choices += 1;
                if self.waiting_for_new_choices >= 100_000 {
                    self.failed = true;
                }

                return false
            }

            if let Some(existing) = self.cases.iter().find(|case| case.inputs.value_eq(inputs)) {
                debug!("Case {:X?} already exists", existing.inputs);
                if existing.output.as_value() != output.as_value() {
                    self.failed = true;
                    return false
                }
            } else {
                self.cases.push(Case {
                    inputs: inputs.as_owned(),
                    output: output.to_owned_value(),
                });

                self.wait_for_new_info = false;

                debug!(
                    "Adding new case (choices_ok={}, add_to_condition_synthesizer={add_to_condition_synthesizer}, given_up={}",
                    self.choices_ok,
                    self.condition_synthesizer.has_given_up()
                );
                if self.choices_ok >= CONDITION_SYNTHESIZER_ACTIVATION_THRESHOLD
                    && add_to_condition_synthesizer
                    && !self.condition_synthesizer.has_given_up()
                {
                    info!("Adding case to condition synthesizer {inputs:X?} -> {output:X?}");
                    self.add_condition_synthesizer_case(inputs, casemap, requester);
                }
            }
        } else {
            self.choices_ok = 0;

            self.waiting_for_new_choices = 0;

            self.add_new_choice(inputs, output.as_value());
            self.verify_choices(requester);
        }

        self.choices_ok >= CONDITION_SYNTHESIZER_ACTIVATION_THRESHOLD + 1000
    }

    fn add_condition_synthesizer_case<V: AsValue, O: SynthesizerOutput + AsValue + for<'v> From<Value<'v>>>(
        &mut self, inputs: &[V], casemap: CaseMap, requester: &mut impl Requester<O>,
    ) {
        let mut missing_choices = Vec::new();
        if let Some(timeout_at) = self.timeout.get() {
            self.condition_synthesizer.set_timeout(timeout_at);
        }

        self.condition_synthesizer.add_case_with_requests(
            inputs,
            casemap,
            &mut CaseMapRequester {
                choices: &self.mcs,
                requester,
                missing_choices: &mut missing_choices,
                timeout: self.timeout,
                _phantom: Default::default(),
            },
        );

        if !missing_choices.is_empty() {
            info!(
                "{} missing choices, adding choices and resetting condition synthesizer...",
                missing_choices.len()
            );
            for (inputs, output) in missing_choices.drain(..) {
                self.check(&inputs, O::from(output.as_value()), requester, false);
            }

            self.condition_synthesizer = ConditionSynthesizer::new(
                &self.input_types,
                IoType::Integer {
                    num_bits: 8,
                },
            );
        }

        if self.condition_synthesizer.has_given_up() {
            info!("Condition synthesizer has given up!");

            if self.condition_synthesizer.permanent_fail() {
                self.failed = true;
            }
        }
    }

    fn try_build_tree<O: AsValue + SynthesizerOutput + for<'v> From<Value<'v>>>(&mut self, requester: &mut impl Requester<O>) {
        debug!(
            "wait_for_new_info={}, choices_ok={}, oks={}, hypothesis={}",
            self.wait_for_new_info,
            self.choices_ok,
            self.oks,
            self.hypothesis.is_some()
        );

        if self.hypothesis.is_none() {
            if !self.condition_synthesizer.has_given_up() {
                info!("Making sure the condition matches all cases we know of");
                // Make sure the condition is fully consistent with all cases we have
                'outer: loop {
                    if self.condition_synthesizer.has_given_up() || self.timeout.is_timed_out() {
                        self.hypothesis = None;
                        break
                    }

                    for case in self.cases.iter() {
                        let hyp = self.condition_synthesizer.hypothesis();
                        let hyp_result = hyp.map(|hyp| hyp.evaluate(&case.inputs));

                        let expected = CaseMap::new(
                            self.mcs
                                .iter()
                                .map(|expr| expr.evaluate(&case.inputs) == case.output.as_value()),
                        );

                        if expected.is_empty() {
                            panic!("We should have added a new choice for: {case:X?}");
                        }

                        let add = hyp_result
                            .map(|hyp_result| {
                                assert!(
                                    hyp_result < self.mcs.len(),
                                    "Hypothesis is outdated; Condition synthesizer should have been reset when updating self.mcs."
                                );

                                !expected.matches(hyp_result)
                            })
                            .unwrap_or_else(|| !self.condition_synthesizer.contains_case(&case.inputs));

                        if add {
                            info!(
                                "Case {case:X?} returned {hyp_result:?}, but it should return {expected:?}; Adding case to condition synthesizer"
                            );
                            let inputs = case.inputs.as_owned();
                            self.add_condition_synthesizer_case(&inputs, expected, requester);
                            continue 'outer
                        }
                    }

                    break
                }
            }

            self.can_build = false;

            if !self.find_hypothesis() {
                self.oks = 0;
                self.wait_for_new_info = true;
                debug!(
                    "Learning the decision tree failed (MCS: {})",
                    self.mcs.iter().map(|expr| expr.display(ARG_NAMES)).format(", ")
                );
            } else {
                let hyp = self.hypothesis.as_ref().unwrap();

                info!("Found: {}", hyp.display(ARG_NAMES));
            }
        }
    }

    #[cfg(not(debug_assertions))]
    fn verify_choices<O: AsValue + SynthesizerOutput>(&mut self, _requester: &mut impl Requester<O>) {}

    #[cfg(debug_assertions)]
    fn verify_choices<O: AsValue + SynthesizerOutput>(&mut self, _requester: &mut impl Requester<O>) {
        // for choice in self.choices.iter() {
        //     for case in choice.cases.iter() {
        //         let expected_output = choice.expr.evaluate(case);
        //         let real_output = requester.request(case);

        //         if real_output.as_ref().map(|o| expected_output.as_value() != o.as_value()).unwrap_or(false) {
        //             panic!("Case {case:X?} has been misclassified; Expected output {expected_output:X?}, but real output is {real_output:X?}");
        //         }
        //     }
        // }
    }

    pub fn find_hypothesis(&mut self) -> bool {
        if self.mcs.len() == 1 {
            self.hypothesis = Some(Hypothesis {
                switch: Switch::default(),
                outputs: vec![self.mcs[0].to_synthesized_computation()],
            });

            true
        } else if let Some(hypothesis) = self.condition_synthesizer.hypothesis() {
            self.hypothesis = Some(Hypothesis {
                switch: hypothesis.clone(),
                outputs: self.mcs.iter().map(|expr| expr.to_synthesized_computation()).collect(),
            });

            true
        } else {
            false
        }
    }

    /// Get a reference to the synthesis table's oks.
    pub fn oks(&self) -> usize {
        self.oks
    }
}

struct NoRequester;

impl<Output: SynthesizerOutput> Requester<Output> for NoRequester {
    fn request<V: AsValue>(&mut self, _inputs: &[V]) -> Option<Output> {
        panic!("No requester is available")
    }
}

impl<F: ExpressionFinder> SynthesizerBase for TreeTemplateSynthesizer<F> {
    type Hypothesis = Hypothesis;
    type Computation = SynthesizedComputation;

    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        let (mcs, choices_ok) = if output_type.num_bits() <= 3 {
            let num_bits = output_type.num_bits();
            const TEMPLATE: Expr = expr!(hole::<0>());
            let v = (0..1 << num_bits)
                .map(|n| {
                    ExpressionComputation::new(
                        TEMPLATE.to_owned(),
                        once(Arg::TinyConst(n)).collect(),
                        OutputEncoding::UnsignedBigEndian,
                        IoType::Integer {
                            num_bits,
                        },
                    )
                })
                .collect();

            (v, 1_000_000)
        } else {
            (Vec::new(), 0)
        };

        TreeTemplateSynthesizer {
            expression_finder: F::new(input_types, output_type),
            cases: Vec::new(),
            mcs,
            condition_synthesizer: ConditionSynthesizer::new(
                input_types,
                IoType::Integer {
                    num_bits: 8,
                },
            ),
            input_types: input_types.to_vec(),
            hypothesis: None,
            failed: false,
            oks: 0,
            choices_ok,
            cases_seen: 0,
            wait_for_new_info: false,
            can_build: false,
            timeout: Timeout::default(),
            waiting_for_new_choices: 0,
        }
    }

    fn hypothesis(&self) -> Option<&Self::Hypothesis> {
        self.hypothesis.as_ref()
    }

    fn has_given_up(&self) -> bool {
        self.failed || (self.cases_seen > 500_000 && self.hypothesis().is_none())
    }

    fn needs_requester(&self) -> bool {
        // TODO: self.choices_ok >= 800
        true
    }

    fn needs_requester_for_consistency(&self) -> bool {
        self.mcs.len() > 1 && self.choices_ok >= CONDITION_SYNTHESIZER_ACTIVATION_THRESHOLD
    }

    fn set_timeout(&mut self, stop_at: Instant) {
        self.timeout.set_timeout_at(stop_at);
        self.expression_finder.set_timeout(stop_at);
    }

    fn into_computation(self) -> Option<Self::Computation> {
        if let Some(hyp) = self.hypothesis {
            let computation = hyp.switch.instantiate_with_outputs(&hyp.outputs);
            let mut normalizer = ComputationNormalizer::new(computation.clone());

            let normalized_computation = normalizer.normalize();

            // Verify normalized hypothesis on all cases and panic if it differs
            for case in self.cases.iter() {
                let actual_output = &case.output;
                let computation_expected = computation.evaluate(&case.inputs);

                if computation_expected != *actual_output {
                    // let hyp_expected_without_fast_eval = SynthesizedComputation::new(
                    //     expr.expr.expr().without_fast_eval().to_owned(),
                    //     expr.expr.arg_interpretation().to_vec(),
                    //     Vec::new(),
                    //     expr.expr.as_internal().output_encoding(),
                    //     expr.expr.as_internal().output_type(),
                    // ).evaluate(case);
                    let hyp_expected_without_fast_eval = "";

                    assert_eq!(
                        &computation_expected,
                        actual_output,
                        "Building a single SynthesizedComputation from Switch broke the computation: {} => {} (normalized -- but previous was already wrong: => {})\n\nwith case {case:X?} => {actual_output:X?};\n hyp_expected_without_fast_eval={hyp_expected_without_fast_eval:X?} \nComputation: {computation:?}; \n\nChoices: {:X?}",
                        hyp.display(ARG_NAMES),
                        computation.display(ARG_NAMES),
                        normalized_computation.display(ARG_NAMES),
                        self.mcs
                    );
                }

                let eval_result = normalized_computation.evaluate(&case.inputs);
                if eval_result != computation_expected {
                    ComputationNormalizer::new(computation.clone()).debug_breakage(&case.inputs);
                    panic!(
                        "Normalizer broke the computation: {} => {} with case {case:X?} => {computation_expected:X?} (normalized produced: {eval_result:X?})",
                        computation.display(ARG_NAMES),
                        normalized_computation.display(ARG_NAMES)
                    );
                }
            }

            Some(normalized_computation)
        } else {
            None
        }
    }
}

impl<F: ExpressionFinder, Output: SynthesizerOutput + AsValue> Synthesizer<Output> for TreeTemplateSynthesizer<F>
where
    for<'v> Output: From<Value<'v>>,
    for<'o> Output::Borrowed<'o>: AsValue,
{
    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: Output::Borrowed<'_>) -> bool {
        self.hypothesis
            .as_ref()
            .map(|hyp| hyp.compare_eq(inputs, output.as_value()))
            .unwrap_or(false)
    }

    fn is_consistent_with_requests<V: AsValue>(
        &self, inputs: &[V], output: <Output as SynthesizerOutput>::Borrowed<'_>, requester: &mut impl Requester<Output>,
    ) -> bool {
        if !<Self as Synthesizer<Output>>::is_consistent(self, inputs, output) {
            return false
        }

        if self.mcs.len() <= 1 {
            return true
        }

        let casemap = CaseMap::new(self.mcs.iter().map(|expr| expr.compare_eq(inputs, output.as_value())));
        let mut missing_choices = Vec::new();

        let increases_variety = self.condition_synthesizer.increases_variety(inputs);
        let group_conditions_are_consistent = self.condition_synthesizer.group_conditions_are_consistent(
            inputs,
            &casemap,
            &mut CaseMapRequester {
                choices: &self.mcs,
                requester,
                missing_choices: &mut missing_choices,
                timeout: self.timeout,
                _phantom: Default::default(),
            },
        );

        // is_consistent_with_requests must start returning only true at some point.
        //
        //
        // This is needed for, for example, 0F96C2.

        // Previous (broken) condition: !increases_variety && !group_conditions_are_consistent.unwrap_or(false)
        // Previous (reduces synthesized %) condition: (!increases_variety || self.choices_ok >= 1000) && group_conditions_are_consistent.unwrap_or(false)
        (!increases_variety || self.choices_ok >= 10_000) && group_conditions_are_consistent.unwrap_or(false)
    }

    fn add_case_with_requests<V: AsValue>(&mut self, inputs: &[V], output: Output, requester: &mut impl Requester<Output>) {
        self.can_build |= self.check(inputs, output, requester, true);
        if self.can_build {
            self.try_build_tree(requester);
        }
    }

    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: Output) {
        self.can_build |= self.check(inputs, output, &mut NoRequester, true);
        if self.can_build {
            panic!("Needs requester");
        }
    }
}

impl<F: ExpressionFinder> fmt::Display for TreeTemplateSynthesizer<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(computation) = &self.hypothesis() {
            write!(f, "{}", computation.display(ARG_NAMES))
        } else {
            write!(
                f,
                "<incomplete with exprs: {:?}>",
                self.mcs.iter().map(|c| c.display(ARG_NAMES)).format(", ")
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::default::computation::SynthesizedComputation;
    use liblisa::semantics::{Computation, IoType, ARG_NAMES};
    use liblisa::value::{AsValue, OwnedValue, Value};
    use rand::{Rng, SeedableRng};
    use rand_xoshiro::Xoshiro256PlusPlus;
    use test_log::test;

    use super::TreeTemplateSynthesizer;
    use crate::tree::expr_finder::mcs::McsExpressionFinder;
    use crate::{synthesize_from_fn, SynthesizerBase};

    type TestFinder = McsExpressionFinder;

    fn parity(n: u64) -> u64 {
        ((n as u8).count_ones() as u64 + 1) % 2
    }

    #[test]
    pub fn find_jump_with_condition_be() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 9,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let rip = inputs[0].unwrap_num();
                let offset = inputs[1].unwrap_num() as u8 as i8;
                let invert = (inputs[1].unwrap_num() >> 8) & 1;
                let condition = inputs[2].unwrap_num();

                let result = condition ^ invert;

                OwnedValue::Num(rip.wrapping_add(if result == 1 { (offset as i64 + 2) as u64 } else { 2 }))
            })
        };
        let result = synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f);
        println!("Result: {result:?}");
        assert!(result.is_some());
    }

    #[test]
    pub fn find_jump_with_condition_le() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 33,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let rip = inputs[0].unwrap_num();
                let offset = (inputs[1].unwrap_num() as u32).swap_bytes() as i32;
                let invert = (inputs[1].unwrap_num() >> 32) & 1;
                let condition = inputs[2].unwrap_num();

                let result = condition ^ invert;

                OwnedValue::Num(rip.wrapping_add(if result == 1 { (offset as i64 + 6) as u64 } else { 6 }))
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_jump_with_complex_condition() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 9,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let rip = inputs[0].unwrap_num();
                let offset = inputs[1].unwrap_num() as u8 as i8;
                let invert = (inputs[1].unwrap_num() >> 8) & 1 != 0;
                let condition = inputs[2].unwrap_num() == 0 && (inputs[3].unwrap_num() == inputs[4].unwrap_num());

                let result = condition ^ invert;

                OwnedValue::Num(rip.wrapping_add(if result { (offset as i64 + 2) as u64 } else { 2 }))
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    // ================ Addition ================
    fn find_binary_operation(
        op1_size: usize, op2_size: usize, output_size: usize, op: impl Fn(u64, u64) -> u64,
    ) -> Option<SynthesizedComputation> {
        find_int_operation::<2, _>(&mut rand::thread_rng(), [op1_size, op2_size], output_size, |[a, b]| op(a, b))
    }

    fn find_int_operation<const N: usize, R: Rng>(
        rng: &mut R, op_sizes: [usize; N], output_size: usize, op: impl Fn([u64; N]) -> u64,
    ) -> Option<SynthesizedComputation> {
        let inputs = &op_sizes.map(|num_bits| IoType::Integer {
            num_bits,
        });
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: output_size,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let mut args = [0; N];
                for (index, v) in args.iter_mut().enumerate() {
                    *v = inputs[index].unwrap_num();
                }

                OwnedValue::Num(op(args))
            })
        };
        let result = synthesize_from_fn::<OwnedValue, _>(rng, s, inputs, f);

        if let Some(result) = result.as_ref() {
            println!("RESULT: {}", result.display(ARG_NAMES));
        }

        result
    }

    #[test]
    pub fn find_lea_output() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 3, 8], 64, |[a, b, c, d]| a
                .wrapping_add(b.wrapping_shl(c as u32).wrapping_add(d)))
            .is_some()
        );
    }

    // #[test]
    // pub fn find_rol_output() {
    //     assert!(find_int_operation(&mut rand::thread_rng(), [64, 8], 64, |[a, b]| a.rotate_left(b as u32 & 0x3f)).is_some());
    // }

    #[test]
    pub fn find_bsf_output() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64], 64, |[a]| if a == 0 {
                0
            } else {
                a.trailing_zeros() as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_bsf_id_output() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64], 64, |[a]| if a == 0 {
                a
            } else {
                a.trailing_zeros() as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_mul_output1() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64], 64, |[a, b]| {
                (a as i128).wrapping_mul(b as i128) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_mul_output2() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64], 64, |[a, b]| {
                ((a as i128).wrapping_mul(b as i128) >> 64) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_mul_ofcf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64], 64, |[a, b]| {
                (((a as u128).wrapping_mul(b as u128) >> 64) as u64 != 0) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_idiv128_output1() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 64], 64, |[a, b, c]| {
                let n = a as i128 | ((b as i128) << 64);
                (n.checked_div(c as i64 as i128).unwrap_or(0)) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_idiv128_output2() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 64], 64, |[a, b, c]| {
                let n = a as i128 | ((b as i128) << 64);
                (n.checked_rem(c as i64 as i128).unwrap_or(0)) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_add_output() {
        assert!(find_binary_operation(64, 64, 64, |a, b| a.wrapping_add(b)).is_some());
    }

    #[test]
    pub fn find_add_of() {
        assert!(
            find_binary_operation(64, 64, 1, |a, b| {
                let carry_64 = a.checked_add(b).is_none();
                let carry_63 = ((a & !0x8000_0000_0000_0000) + (b & !0x8000_0000_0000_0000)) & 0x8000_0000_0000_0000 != 0;

                (carry_64 ^ carry_63) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_add_inv_of() {
        assert!(
            find_binary_operation(64, 64, 1, |a, b| {
                let carry_64 = a.checked_add(b).is_some();
                let carry_63 = ((a & !0x8000_0000_0000_0000) + (b & !0x8000_0000_0000_0000)) & 0x8000_0000_0000_0000 != 0;

                (carry_64 ^ carry_63) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_add_sf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| a.wrapping_add(b) >> 63).is_some());
    }

    #[test]
    pub fn find_add_zf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| (a.wrapping_add(b) == 0) as u64).is_some());
    }

    #[test]
    pub fn find_add_af() {
        assert!(find_binary_operation(64, 64, 1, |a, b| ((a & 0xF) + (b & 0xF) > 0xF) as u64).is_some());
    }

    #[test]
    pub fn find_add_cf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| a.checked_add(b).is_none() as u64).is_some());
    }

    #[test]
    pub fn find_add_pf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| (a.wrapping_add(b) as u8).count_ones() as u64 & 1).is_some());
    }

    #[test]
    pub fn find_adc_sf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 1], 1, |[a, b, c]| a
                .wrapping_add(b.wrapping_add(c))
                >> 63)
            .is_some()
        );
    }

    #[test]
    pub fn find_and_output() {
        assert!(find_binary_operation(32, 32, 32, |a, b| a & b).is_some());
    }

    #[test]
    pub fn find_and_shift_output() {
        assert!(find_binary_operation(8, 24, 8, |a, b| a & (b >> 8)).is_some());
        assert!(find_binary_operation(8, 24, 8, |a, b| a & (b >> 16)).is_some());
    }

    #[test]
    pub fn find_and_sf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| (a & b) >> 63).is_some());
    }

    #[test]
    pub fn find_and_zf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| (a & b == 0) as u64).is_some());
    }

    #[test]
    pub fn find_and_pf() {
        assert!(find_binary_operation(64, 64, 1, |a, b| ((a & b) as u8).count_ones() as u64 & 1).is_some());
    }

    #[test]
    pub fn seed3_find_and_pf() {
        let seed = 3;
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
        println!("Seed = {seed}");
        find_int_operation::<2, _>(&mut rng, [64, 64], 1, |[a, b]| ((a & b) as u8).count_ones() as u64 & 1).unwrap();
    }

    #[test]
    pub fn find_bytes_add_cf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Bytes {
                num_bytes: 8,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num();
                let b = u64::from_le_bytes(inputs[1].unwrap_bytes().try_into().unwrap());

                OwnedValue::Num(a.checked_add(b).is_none() as u64)
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_bytes_add_output() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Bytes {
                num_bytes: 8,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Bytes {
                num_bytes: 8,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num();
                let b = u64::from_le_bytes(inputs[1].unwrap_bytes().try_into().unwrap());

                OwnedValue::Bytes(u64::to_le_bytes(a.wrapping_add(b)).to_vec())
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_shr64_of() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[a, b, c]| if (b & 0x3f) == 0 {
                c
            } else if (b & 0x3f) == 1 {
                (a >> 63) & 1
            } else {
                0
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shr32_of() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
        assert!(
            find_int_operation(&mut rng, [32, 8, 1], 1, |[a, b, c]| if (b & 0x1f) == 0 {
                c
            } else if (b & 0x1f) == 1 {
                (a >> 31) & 1
            } else {
                0
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sar_cf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[a, b, c]| {
                if let Some(b) = (b & 0x3f).checked_sub(1) {
                    a.wrapping_shr(b as u32) & 1
                } else {
                    c
                }
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sar_zf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[a, b, c]| if (b & 0x3f) == 0 {
                c
            } else {
                (a.wrapping_shr(b as u32) == 0) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sar_sf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[a, b, c]| if (b & 0x3f) == 0 {
                c
            } else {
                (a.wrapping_shr(b as u32) >> 63) & 1
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sar_of() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[_, b, c]| if (b & 0x3f) == 0 {
                c
            } else {
                0
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sar_af() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[_, b, c]| if (b & 0x3f) == 0 {
                c
            } else {
                1
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sar_pf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 8, 1], 1, |[a, b, c]| if (b & 0x3f) == 0 {
                c
            } else {
                parity(a.wrapping_shr(b as u32))
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shl32_cf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 8, 1], 1, |[a, b, c]| {
                let b = b & 0x1f;
                if b != 0 { (a.wrapping_shl(b as u32) >> 32) & 1 } else { c }
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shl32_zf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 8, 1], 1, |[a, b, c]| if (b & 0x1f) == 0 {
                c
            } else {
                ((a as u32).wrapping_shl(b as u32) == 0) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shl32_sf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 8, 1], 1, |[a, b, c]| if (b & 0x1f) == 0 {
                c
            } else {
                ((a as u32).wrapping_shl(b as u32) >> 31) as u64 & 1
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shl32_of() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 8, 1], 1, |[a, b, c]| if b & 0x1f != 0 {
                let result = a << (b & 0x1f);
                if (result >> 32) & 1 == (result >> 31) & 1 { 0 } else { 1 }
            } else {
                c
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shl32_af() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 8, 1], 1, |[_, b, c]| if (b & 0x1f) == 0 {
                c
            } else {
                1
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_shl32_pf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 8, 1], 1, |[a, b, c]| if (b & 0x1f) == 0 {
                c
            } else {
                parity((a as u32).wrapping_shl(b as u32) as u64)
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sub_output() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num();
                let b = inputs[1].unwrap_num();

                OwnedValue::Num(a.wrapping_sub(b))
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sub_zf() {
        assert!(find_int_operation(&mut rand::thread_rng(), [64, 64], 1, |[a, b]| (a.wrapping_sub(b) == 0) as u64).is_some());
    }

    #[test]
    pub fn find_sub32_zf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [32, 32], 1, |[a, b]| (a.wrapping_sub(b) as u32 == 0)
                as u64)
            .is_some()
        );
    }

    #[test]
    pub fn find_sub_inv_zf() {
        assert!(find_int_operation(&mut rand::thread_rng(), [64, 64], 1, |[a, b]| (a.wrapping_sub(b) != 0) as u64).is_some());
    }

    #[test]
    pub fn find_sub_cf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num();
                let b = inputs[1].unwrap_num();

                OwnedValue::Num(a.checked_add((b as i64).wrapping_neg() as u64).is_some() as u64)
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sub_sf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num();
                let b = inputs[1].unwrap_num();

                OwnedValue::Num(a.wrapping_sub(b) >> 63)
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sub_pf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num();
                let b = inputs[1].unwrap_num();
                let r = a.wrapping_sub(b);

                OwnedValue::Num((((r as u8).count_zeros() + 1) % 2) as u64)
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sub_af() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let a = inputs[0].unwrap_num() & 0xf;
                let b = inputs[1].unwrap_num() & 0xf;

                OwnedValue::Num((a.wrapping_sub(b) >> 4) & 1)
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sbb_output() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 1], 64, |[a, b, c]| a
                .wrapping_sub(b.wrapping_add(c)))
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_id_output() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 1], 64, |[_, _, c]| if c != 0 {
                u64::MAX
            } else {
                0
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_zf() {
        assert!(
            find_int_operation(
                &mut rand::thread_rng(),
                [64, 64, 1],
                1,
                |[a, b, c]| (a.wrapping_sub(b.wrapping_add(c)) == 0) as u64
            )
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb32_zf() {
        assert!(
            find_int_operation(
                &mut rand::thread_rng(),
                [32, 32, 1],
                1,
                |[a, b, c]| (a.wrapping_sub(b.wrapping_add(c)) as u32 == 0) as u64
            )
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_inv_zf() {
        assert!(
            find_int_operation(
                &mut rand::thread_rng(),
                [64, 64, 1],
                1,
                |[a, b, c]| (a.wrapping_sub(b.wrapping_add(c)) != 0) as u64
            )
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_cf() {
        assert!(
            find_int_operation(
                &mut rand::thread_rng(),
                [64, 64, 1],
                1,
                |[a, b, c]| (a < b || (a == b && c == 1)) as u64
            )
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_sf() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 1], 1, |[a, b, c]| a
                .wrapping_sub(b.wrapping_add(c))
                >> 63)
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_pf() {
        assert!(
            find_int_operation(
                &mut rand::thread_rng(),
                [64, 64, 1],
                1,
                |[a, b, c]| (((a.wrapping_sub(b.wrapping_add(c)) as u8).count_zeros() + 1) % 2) as u64
            )
            .is_some()
        );
    }

    #[test]
    pub fn find_sbb_af() {
        assert!(
            find_int_operation(
                &mut rand::thread_rng(),
                [64, 64, 1],
                1,
                |[a, b, c]| ((a & 0xf) < ((b & 0xf).wrapping_add(c))) as u64
            )
            .is_some()
        );
    }

    #[test]
    #[ignore = "slow"]
    pub fn find_sbb_of() {
        assert!(
            find_int_operation(&mut rand::thread_rng(), [64, 64, 1], 1, |[a, b, c]| {
                let b = (b.wrapping_add(c) ^ 0xffff_ffff_ffff_ffff).wrapping_add(1);

                let carry_64 = a.checked_add(b).is_some();
                let carry_63 = ((a & !0x8000_0000_0000_0000) + (b & !0x8000_0000_0000_0000)) & 0x8000_0000_0000_0000 != 0;

                (carry_64 ^ carry_63) as u64
            })
            .is_some()
        );
    }

    #[test]
    pub fn find_or_output() {
        let inputs = &[
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 8,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(inputs[0].unwrap_num() | inputs[1].unwrap_num()));
        println!(
            "{}",
            synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f)
                .unwrap()
                .display(ARG_NAMES)
        );
    }

    #[test]
    pub fn find_or_u8_zf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(if inputs[0].unwrap_num() | inputs[1].unwrap_num() == 0 {
                1
            } else {
                0
            }))
        };
        println!(
            "{}",
            synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f)
                .unwrap()
                .display(ARG_NAMES)
        );
    }

    #[test]
    pub fn find_or_u64_zf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(if inputs[0].unwrap_num() | inputs[1].unwrap_num() == 0 {
                1
            } else {
                0
            }))
        };
        println!(
            "{}",
            synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f)
                .unwrap()
                .display(ARG_NAMES)
        );
    }

    #[test]
    pub fn find_or_sf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num((inputs[0].unwrap_num() | inputs[1].unwrap_num()) >> 63));
        println!(
            "{}",
            synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f)
                .unwrap()
                .display(ARG_NAMES)
        );
    }

    #[test]
    pub fn find_or_pf() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(parity(inputs[0].unwrap_num() | inputs[1].unwrap_num())));
        println!(
            "{}",
            synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f)
                .unwrap()
                .display(ARG_NAMES)
        );
    }

    #[test]
    pub fn find_mux() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
        ];
        let s = TreeTemplateSynthesizer::<TestFinder>::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[inputs[2].unwrap_num() as usize].to_owned_value());
        println!(
            "{}",
            synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f)
                .unwrap()
                .display(ARG_NAMES)
        );
    }
}
