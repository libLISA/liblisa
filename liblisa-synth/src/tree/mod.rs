use liblisa::semantics::default::computation::PreparedComparison;
use liblisa::semantics::InputValues;
use liblisa::value::{AsValue, OwnedValue, Value};

use crate::search::{ComputationEnumerator, InterpretedArgs};
use crate::InputSlice;

pub mod expr_finder;
pub mod mapping;
pub mod synthesizer;

#[derive(Debug, Clone)]
pub struct Case {
    inputs: Vec<OwnedValue>,
    output: OwnedValue,
}

impl Case {
    pub fn new<V: AsValue>(inputs: &[V], output: Value) -> Self {
        Case {
            inputs: inputs.as_owned(),
            output: output.to_owned_value(),
        }
    }

    pub fn inputs(&self) -> &[OwnedValue] {
        self.inputs.as_ref()
    }

    pub fn output(&self) -> Value {
        self.output.as_value()
    }
}

#[derive(Debug, Clone)]
pub struct PreparedCase {
    args: InterpretedArgs,
    comparison: PreparedComparison,
}

impl PreparedCase {
    pub fn new<V: AsValue>(inputs: &[V], output: Value, enumerator: &ComputationEnumerator) -> Self {
        PreparedCase {
            args: enumerator.prepare_interpreted_args(inputs),
            comparison: PreparedComparison::from(&output),
        }
    }

    pub fn arg_slice(&self) -> &[i128] {
        self.args.as_slice()
    }
}

#[derive(Debug, Clone)]
pub struct PreparedInputs {
    inputs: InputValues,
    args: InterpretedArgs,
}

impl PreparedInputs {
    pub fn new<V: AsValue>(inputs: &[V], enumerator: &ComputationEnumerator) -> Self {
        PreparedInputs {
            inputs: InputValues::from(inputs),
            args: enumerator.prepare_interpreted_args(inputs),
        }
    }

    pub fn arg_slice(&self) -> &[i128] {
        self.args.as_slice()
    }

    pub fn inputs(&self) -> &InputValues {
        &self.inputs
    }
}
