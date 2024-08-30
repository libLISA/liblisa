use std::time::Instant;

use itertools::Itertools;
use liblisa::semantics::default::computation::ExpressionComputation;
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::value::{AsValue, OwnedValue, Value};
use log::info;

use crate::{Synthesizer, SynthesizerBase};

pub mod bitmap_mcs;
pub mod greedy;
pub mod mcs;

pub trait ExpressionFinder {
    fn new(input_types: &[IoType], output_type: IoType) -> Self;

    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: Value);

    fn find_expressions(&mut self) -> Vec<ExpressionComputation>;

    fn set_timeout(&mut self, stop_at: Instant);

    fn has_given_up(&self) -> bool;
}

struct TestSynthesizer<F: ExpressionFinder> {
    mcs: Vec<ExpressionComputation>,
    f: F,
}

impl<F: ExpressionFinder> SynthesizerBase for TestSynthesizer<F> {
    type Hypothesis = Vec<ExpressionComputation>;
    type Computation = Vec<ExpressionComputation>;

    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        Self {
            mcs: Vec::new(),
            f: F::new(input_types, output_type),
        }
    }

    fn hypothesis(&self) -> Option<&Self::Hypothesis> {
        Some(&self.mcs)
    }

    fn has_given_up(&self) -> bool {
        self.f.has_given_up()
    }

    fn needs_requester(&self) -> bool {
        false
    }

    fn into_computation(self) -> Option<Self::Computation> {
        Some(self.mcs)
    }
}

impl<F: ExpressionFinder> Synthesizer<OwnedValue> for TestSynthesizer<F> {
    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: OwnedValue) {
        self.f.add_case(inputs, output.as_value());
        self.mcs = self.f.find_expressions();
        info!("Mcs = {}", self.mcs.iter().map(|expr| expr.display(ARG_NAMES)).format(", "));
    }

    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: Value<'_>) -> bool {
        self.mcs.iter().any(|expr| expr.compare_eq(inputs, output))
    }
}
