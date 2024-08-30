use std::fmt;

use liblisa::semantics::default::computation::{AsComputationRef, SynthesizedComputation};
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::value::AsValue;

use crate::predicate::Disjunction;

#[derive(Clone, Debug)]
pub struct SwitchCase {
    condition: Disjunction,
    index: usize,
}

impl SwitchCase {
    pub fn new(condition: Disjunction, index: usize) -> Self {
        Self {
            condition,
            index,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Switch {
    cases: Vec<SwitchCase>,
}

impl Switch {
    pub fn new() -> Self {
        Self {
            cases: Vec::new(),
        }
    }

    pub fn instantiate_with_outputs(&self, outputs: &[SynthesizedComputation]) -> SynthesizedComputation {
        let mut result = outputs[self.cases[self.cases.len() - 1].index].clone();

        for group in self.cases.iter().rev().skip(1) {
            let condition = SynthesizedComputation::from(group.condition.clone());
            let output = &outputs[group.index];
            result = condition.if_zero(&result, output);
        }

        result
    }

    pub fn used_input_indices(&self) -> Vec<usize> {
        let mut seen = GrowingBitmap::new();
        self.cases
            .iter()
            .flat_map(|group| group.condition.used_input_indices())
            .filter(|&n| seen.set(n))
            .collect()
    }

    pub fn remap_inputs(&mut self, map: &[Option<usize>]) {
        for case in self.cases.iter_mut() {
            case.condition.remap_inputs(map);
        }
    }

    pub fn add_case(&mut self, case: SwitchCase) {
        self.cases.push(case);
    }

    pub fn conditions(&self) -> impl Iterator<Item = &Disjunction> {
        self.cases.iter().map(|case| &case.condition)
    }
}

impl Default for Switch {
    fn default() -> Self {
        Self {
            cases: vec![SwitchCase {
                condition: Disjunction::always_true(),
                index: 0,
            }],
        }
    }
}

impl Switch {
    pub fn evaluate<V: AsValue>(&self, inputs: &[V]) -> usize {
        for group in self.cases.iter() {
            if group.condition.evaluate(inputs) {
                return group.index;
            }
        }

        panic!("This should not happen!")
    }

    pub fn display<'a, S: AsRef<str>>(&'a self, input_names: &'a [S]) -> DisplaySwitch<'a> {
        DisplaySwitch(self, input_names.iter().map(|s| s.as_ref().to_string()).collect::<Vec<_>>())
    }
}

#[derive(Debug)]
pub struct DisplaySwitch<'a>(&'a Switch, Vec<String>);

impl fmt::Display for DisplaySwitch<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "match {{ ")?;

        for case in self.0.cases.iter() {
            write!(f, "{} => {:X?}, ", case.condition.display(&self.1), case.index)?;
        }

        write!(f, "}}")
    }
}
