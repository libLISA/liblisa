use std::fmt::Debug;
use std::marker::PhantomData;
use std::mem::swap;

use liblisa::semantics::default::computation::{OutputEncoding, PreparedComparison};
use liblisa::semantics::IoType;
use liblisa::value::AsValue;
use log::{debug, info};

use super::{ComputationEnumerator, InterpretedArgs, IterItemComputation};
use crate::templates::preprocess::PreprocessedTemplate;

pub trait CheckResult {
    type Output: Debug + Clone;

    fn start_check() -> Self;

    fn compare_eq_first(&mut self, instance: &IterItemComputation, all_args: &[i128], expected: &Self::Output) -> bool {
        self.compare_eq(instance, all_args, expected)
    }

    fn compare_eq(&mut self, instance: &IterItemComputation, all_args: &[i128], expected: &Self::Output) -> bool;
}

pub struct CheckFlippableBoolResult {
    flip: bool,
}

impl CheckResult for CheckFlippableBoolResult {
    type Output = bool;

    #[inline(always)]
    fn start_check() -> Self {
        CheckFlippableBoolResult {
            flip: false,
        }
    }

    #[inline(always)]
    fn compare_eq_first(&mut self, instance: &IterItemComputation, all_args: &[i128], expected: &Self::Output) -> bool {
        let result = self.compare_eq(instance, all_args, expected);

        if !result {
            self.flip = true;
        }

        true
    }

    #[inline(always)]
    fn compare_eq(&mut self, instance: &IterItemComputation, all_args: &[i128], expected: &Self::Output) -> bool {
        let result = instance
            .expr_computation(OutputEncoding::UnsignedBigEndian)
            .evaluate_as_bool_with_args_indirect(all_args, instance.arg_indexes())
            == *expected;

        result ^ self.flip
    }
}

impl CheckFlippableBoolResult {
    pub fn flip(&self) -> bool {
        self.flip
    }
}

pub struct CheckValueResult {
    pub big_endian: bool,
    pub little_endian: bool,
}

impl CheckResult for CheckValueResult {
    type Output = PreparedComparison;

    #[inline(always)]
    fn start_check() -> Self {
        CheckValueResult {
            big_endian: true,
            little_endian: true,
        }
    }

    #[inline(always)]
    fn compare_eq(&mut self, instance: &IterItemComputation, all_args: &[i128], expected: &Self::Output) -> bool {
        let r = instance.prepared_compare_eq_with_args_indirect(all_args, expected);

        self.big_endian &= r.big_endian;
        self.little_endian &= r.little_endian;

        self.big_endian || self.little_endian
    }
}

struct Case<C: CheckResult> {
    num_uses: u32,
    interpreted_args: InterpretedArgs,
    expected_output: C::Output,
}

impl<C: CheckResult> Clone for Case<C> {
    fn clone(&self) -> Self {
        Self {
            num_uses: self.num_uses,
            interpreted_args: self.interpreted_args.clone(),
            expected_output: self.expected_output.clone(),
        }
    }
}

impl<C: CheckResult> Debug for Case<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Case")
            .field("num_uses", &self.num_uses)
            .field("interpreted_args", &self.interpreted_args)
            .field("output", &self.expected_output)
            .finish()
    }
}

pub struct Searcher<'a, C: CheckResult> {
    iter: ComputationEnumerator<'a>,
    cases: Vec<Case<C>>,
    _phantom: PhantomData<fn() -> C>,
}

impl<'a, C: CheckResult> Clone for Searcher<'a, C> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            cases: self.cases.clone(),
            _phantom: PhantomData,
        }
    }
}

enum Match<C> {
    NonMatchingIndex(usize),
    Check(C),
}

impl<'a, C: CheckResult> Searcher<'a, C> {
    pub fn new_from_enumerator(iter: ComputationEnumerator<'a>) -> Self {
        Searcher {
            iter,
            cases: Vec::new(),
            _phantom: PhantomData,
        }
    }

    pub fn new_with_custom_templates(templates: &'a [PreprocessedTemplate], input_types: &[IoType], output_type: IoType) -> Self {
        info!("Created synthesizer for {:?} => {:?}", input_types, output_type);

        Searcher {
            iter: ComputationEnumerator::new(templates, input_types, output_type),
            cases: Vec::new(),
            _phantom: PhantomData,
        }
    }

    /// Searches for a new computation *unconditionally*.
    /// Regardless of whether the last returned computation still matches all cases,
    /// this will continue searching at the next *unseen* computation.
    ///
    /// You must manually check if the previous computation still satisfies all cases if you wish to reuse it.
    pub fn next_expr(&mut self) -> Option<(IterItemComputation, C)> {
        let mut n = 0;
        let mut weight = 1;

        let mut total_checked = 0;
        while let Some(inst) = self.iter.find_next() {
            n += 1;

            match Self::check_cases(&self.cases, inst) {
                Match::NonMatchingIndex(non_matching_index) => {
                    self.cases[non_matching_index].num_uses += weight;

                    total_checked += non_matching_index + 1;

                    // A very fast "bubble sort" that only moves cases one step at a time
                    // This works well enough, and is more performant than doing a full sort every now and then
                    if non_matching_index > 0
                        && self.cases[non_matching_index - 1].num_uses < self.cases[non_matching_index].num_uses
                    {
                        let (lhs, rhs) = self.cases.split_at_mut(non_matching_index);
                        swap(&mut lhs[non_matching_index - 1], &mut rhs[0]);
                    }

                    if n & 0x3ff == 0 {
                        // By increasing the weight we can avoid shifting num_uses much longer,
                        // while still taking more recent cases into account more strongly.
                        weight <<= 1;
                        if weight & (1 << 16) != 0 {
                            weight >>= 16;
                            for case in self.cases.iter_mut() {
                                case.num_uses >>= 16;
                            }
                        }

                        // Self::resort_cases(&mut self.cases);
                        debug!(
                            "Average number of checks per expression: {:.2} (computations checked: {n})",
                            total_checked as f64 / n as f64
                        );
                    }
                },
                Match::Check(c) => return Some((self.iter.current(), c)),
            }
        }

        None
    }

    fn check_cases(cases: &[Case<C>], instance: IterItemComputation) -> Match<C> {
        let mut c = C::start_check();
        for (index, case) in cases.iter().enumerate() {
            let eq = if index == 0 {
                c.compare_eq_first(&instance, case.interpreted_args.as_slice(), &case.expected_output)
            } else {
                c.compare_eq(&instance, case.interpreted_args.as_slice(), &case.expected_output)
            };

            if !eq {
                return Match::NonMatchingIndex(index)
            }
        }

        Match::Check(c)
    }

    pub fn has_given_up(&self) -> bool {
        self.iter.is_empty()
    }

    pub fn add_case<V: AsValue>(&mut self, inputs: &[V], expected_output: C::Output) {
        let interpreted_args = self.iter.prepare_interpreted_args(inputs);
        self.cases.push(Case {
            num_uses: 0,
            interpreted_args,
            expected_output,
        });
    }

    pub fn enumerator(&self) -> &ComputationEnumerator {
        &self.iter
    }
}
