use std::collections::HashSet;

use arrayvec::ArrayVec;
use liblisa::semantics::default::ops::Op;
use liblisa::semantics::default::{Expr, MAX_TEMPLATE_ARGS};
use liblisa::semantics::ARG_NAMES;
use liblisa::utils::bitmask_u128;
use log::{debug, trace};

use super::{AnyTemplate, Template};
use crate::search::TemplateIterator;
use crate::templates::symexec::{SymbolicExecution, SymbolicExecutionResult};

#[derive(Clone)]
pub struct PreprocessedTemplate<'a> {
    expr: Expr<'a>,

    /// If 0, an argument should be filled in. If > 0, a constant value should be used.
    arg_indices: Vec<u16>,
    num_holes: usize,
    const_values: &'a [i128],
    ordering_indexes: Vec<Option<usize>>,
    active_indices: u64,
    const_output: Option<i128>,
}

impl std::fmt::Debug for PreprocessedTemplate<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.expr.display(
                self.arg_indices
                    .iter()
                    .enumerate()
                    .map(
                        |(hole_index, const_index)| if let Some(const_index) = const_index.checked_sub(1) {
                            self.const_values[const_index as usize].to_string()
                        } else {
                            ARG_NAMES[hole_index].to_owned()
                        }
                    )
                    .collect::<Vec<_>>()
            )
        )
    }
}

impl<'a> PreprocessedTemplate<'a> {
    pub fn new(template: &Template<'a>, arg_indices: Vec<u16>, const_values: &'a [i128], const_output: Option<i128>) -> Self {
        assert!(arg_indices.len() < 64);

        let num_holes = arg_indices.iter().filter(|&&index| index == 0).count();

        debug_assert_eq!(arg_indices.len(), template.num_holes);

        let active_indices = arg_indices
            .iter()
            .enumerate()
            .map(|(index, &const_index)| if const_index == 0 { 1 << index } else { 0 })
            .fold(0, |a, b| a | b);

        Self {
            expr: *template.expr(),
            num_holes,
            ordering_indexes: template.ordering_indexes().to_vec(),
            arg_indices,
            const_values,
            active_indices,
            const_output,
        }
    }

    pub fn expr(&self) -> &Expr<'a> {
        &self.expr
    }

    pub fn const_output(&self) -> Option<i128> {
        self.const_output
    }

    pub fn raw_arg_indices(&self) -> &[u16] {
        &self.arg_indices
    }
}

impl<'a> AnyTemplate for PreprocessedTemplate<'a> {
    fn num_unfilled_holes(&self) -> usize {
        self.num_holes
    }

    fn ordering_indexes(&self) -> &[Option<usize>] {
        &self.ordering_indexes
    }

    fn num_total_holes(&self) -> usize {
        self.arg_indices.len()
    }

    type IterActiveIndices<'me> = ActiveIndicesIter
        where Self: 'me;

    fn active_indices(&self) -> Self::IterActiveIndices<'_> {
        ActiveIndicesIter {
            active_indices: self.active_indices,
        }
    }

    fn start_value(&self) -> usize {
        self.const_values.len()
    }

    fn new_counter(&self) -> ArrayVec<u16, MAX_TEMPLATE_ARGS> {
        self.arg_indices
            .iter()
            .map(move |&const_index| {
                if let Some(n) = const_index.checked_sub(1) {
                    n
                } else {
                    self.const_values.len() as u16
                }
            })
            .collect()
    }
}

pub struct ActiveIndicesIter {
    active_indices: u64,
}

impl Iterator for ActiveIndicesIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.active_indices == 0 {
            None
        } else {
            let result = self.active_indices.trailing_zeros();
            self.active_indices &= u64::MAX << (result + 1);

            Some(result as usize)
        }
    }
}

pub struct TemplatePreprocessor<'r, 'a> {
    template: &'r Template<'a>,
    const_values: &'a [i128],
    iter: TemplateIterator<'r, Template<'a>>,
    seen: HashSet<Vec<(usize, i128)>>,
    output_bits: usize,
}

impl<'r, 'a> TemplatePreprocessor<'r, 'a> {
    pub fn new(template: &'r Template<'a>, const_values: &'a [i128], output_bits: usize) -> Self {
        debug!("Preprocessing {:?}", template);
        Self {
            template,
            const_values,
            iter: TemplateIterator::new(template),
            seen: HashSet::new(),
            output_bits,
        }
    }

    fn current_template(&self, const_output: Option<i128>) -> PreprocessedTemplate<'a> {
        // Remap indices such that
        //  - 0     = unfilled;
        //  - N + 1 = filled with constant N.
        let arg_indices = self
            .iter
            .arg_indices()
            .iter()
            .map(|&index| {
                if index >= self.const_values.len() as u16 {
                    0
                } else {
                    index + 1
                }
            })
            .collect();
        PreprocessedTemplate::new(self.template, arg_indices, self.const_values, const_output)
    }

    fn compute_key(ops: &[Op], counter: &[u16], const_values: &[i128], output_mask: i128) -> (Vec<(usize, i128)>, Option<i128>) {
        let mut key = Vec::new();
        let mut value_stack = ArrayVec::<_, 32>::new();
        value_stack.push(0);

        let mut const_stack = Vec::new();

        for (index, op) in ops.iter().enumerate() {
            let input_constness = const_stack.drain(const_stack.len() - op.num_args()..).collect::<Vec<_>>();
            let input_values = &value_stack[value_stack.len() - op.num_args()..];

            let all_const = if let Op::Hole(hole_index) = op {
                counter[*hole_index as usize] != const_values.len() as u16
            } else {
                input_constness.iter().all(|&(b, _)| b)
            };

            if !all_const {
                for (&(is_const, index), &value) in input_constness.iter().zip(input_values.iter()) {
                    if is_const {
                        key.push((index, value));
                    }
                }
            }

            let top_of_stack = value_stack.pop().unwrap();
            let top_of_stack = op.eval_from_stack(
                &|hole_index| {
                    let item = counter[hole_index];
                    const_values.get(item as usize).copied().unwrap_or(0)
                },
                top_of_stack,
                &mut value_stack,
            );

            value_stack.push(top_of_stack);
            const_stack.push((all_const, index));
        }

        if let Some((true, index)) = const_stack.pop() {
            let const_output = value_stack.pop().unwrap();
            key.push((index, const_output & output_mask));

            (key, Some(const_output & output_mask))
        } else {
            (key, None)
        }
    }

    pub fn preprocess_templates(&mut self) -> Vec<PreprocessedTemplate<'a>> {
        let output_mask = bitmask_u128(self.output_bits as u32);
        let mut result = Vec::new();
        loop {
            let s = SymbolicExecution::new(
                self.template.expr().ops(),
                self.iter.arg_indices(),
                self.const_values,
                output_mask,
            );
            let SymbolicExecutionResult {
                leaf_consts,
                const_output,
            } = s.run();
            trace!("Checking {:?} with key {leaf_consts:?}", self.current_template(const_output));

            let (mut old_leaf_consts, old_const_output) = Self::compute_key(
                self.template.expr().ops(),
                self.iter.arg_indices(),
                self.const_values,
                output_mask as i128,
            );
            if old_const_output.is_some() && old_const_output != const_output {
                panic!(
                    "Expected constant output changed: {:?}; Const output: {old_const_output:?} => {const_output:?}; Ops: {:?}; Arg indices: {:?}",
                    self.current_template(const_output),
                    self.template.expr().ops(),
                    self.iter.arg_indices()
                )
            }

            old_leaf_consts.sort();
            if old_leaf_consts != leaf_consts {
                debug!(
                    "Leaf consts changed: {:?}; Leaf consts: {old_leaf_consts:X?} => {leaf_consts:X?}; Const output: {old_const_output:?} => {const_output:?}",
                    self.current_template(const_output)
                );
            }

            // TODO: Check if possible given the ordering_indexes

            if self.seen.insert(leaf_consts) {
                trace!("Check result: push");
                result.push(self.current_template(const_output));
            } else {
                trace!("Check result: ignore");
            }

            if !self.iter.next(self.const_values.len() + 1) {
                break
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::default::builder::*;
    use liblisa::semantics::default::expr;
    use test_log::test;

    use super::TemplatePreprocessor;
    use crate::templates::Template;

    #[test]
    pub fn no_duplicates1() {
        let t = Template::new(expr!(or(hole::<0>(), add(hole::<1>(), hole::<2>()))));
        let mut p = TemplatePreprocessor::new(&t, &[0, 1, 2], 128);
        let result = p.preprocess_templates();

        println!("{result:#?}");

        // 40 without preprocessing, 28 with preprocessing
        assert_eq!(result.len(), 28);

        // 0 | (0 + 0)
        assert!(result.iter().any(|r| r.arg_indices == [1, 1, 1]));

        // A | (B + C)
        assert!(result.iter().any(|r| r.arg_indices == [0, 0, 0]))
    }

    #[test]
    pub fn no_duplicates2() {
        let t = Template::new(expr!(or(
            shl(hole::<0>(), or(hole::<2>(), shl(hole::<1>(), c::<4>()))),
            shr(shl(hole::<1>(), or(hole::<2>(), shl(hole::<3>(), c::<4>()))), hole::<3>())
        )));
        let mut p = TemplatePreprocessor::new(&t, &[0, 1, 2], 128);
        let result = p.preprocess_templates();

        println!("{result:#?}");

        // 1024 without preprocessing, 193 with preprocessing
        assert_eq!(result.len(), 193);
    }

    #[test]
    pub fn no_duplicates3() {
        let t = Template::new(expr!(or(hole::<0>(), add(hole::<1>(), hole::<2>()))));
        let mut p = TemplatePreprocessor::new(&t, &[0, 1, 2, 3, 4, 5, 6, 7, 128, 8, 9, 10, 11, 12, 13, 14, 15], 128);
        let result = p.preprocess_templates();

        // 2601 without preprocessing, 452 with preprocessing
        assert_eq!(result.len(), 452);
    }
}
