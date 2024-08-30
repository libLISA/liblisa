use std::collections::HashSet;

use liblisa::semantics::default::computation::{
    Arg, ArgEncoding, AsComputationRef, ComputationRef, ExprComputation, OutputEncoding,
};
use liblisa::semantics::default::ops::Op;
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use log::{debug, info, trace};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use super::preprocess::PreprocessedTemplate;
use super::CONST_VALUES;
use crate::normalizer::ComputationNormalizer;

pub struct PreprocessedTemplateNormalizationFilter<'a> {
    templates: Vec<PreprocessedTemplate<'a>>,
    output_bits: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OptimizedPreparedTemplate {
    ops: Vec<Op>,
    consts: Vec<i128>,
}

impl<'a> PreprocessedTemplateNormalizationFilter<'a> {
    pub fn new(templates: Vec<PreprocessedTemplate<'a>>, output_bits: usize) -> Self {
        Self {
            templates,
            output_bits,
        }
    }

    fn template_as_computation<T>(
        template: &PreprocessedTemplate, output_bits: usize, f: impl FnOnce(&ComputationRef) -> T,
    ) -> T {
        let output_type = if output_bits > 64 {
            IoType::Bytes {
                num_bytes: (output_bits + 7) / 8,
            }
        } else {
            IoType::Integer {
                num_bits: output_bits,
            }
        };

        let computation = ExprComputation::new(*template.expr(), OutputEncoding::UnsignedBigEndian, output_type);
        let mut n = 0;
        let arg_interpretation = template
            .raw_arg_indices()
            .iter()
            .map(|index| {
                if let Some(index) = index.checked_sub(1) {
                    Arg::TinyConst(CONST_VALUES[index as usize].try_into().unwrap())
                } else {
                    let result = Arg::Input {
                        index: n,
                        num_bits: 128,
                        encoding: ArgEncoding::SignedBigEndian,
                    };
                    n += 1;
                    result
                }
            })
            .collect::<Vec<_>>();

        let computation = ComputationRef::new(computation, &arg_interpretation);
        f(&computation)
    }

    pub fn run(mut self) -> Vec<PreprocessedTemplate<'a>> {
        info!("Normalizing {} preprocessed templates", self.templates.len());
        let optimized_templates = self
            .templates
            .par_iter()
            .map(|template| {
                let template = Self::template_as_computation(template, self.output_bits, |c| c.to_synthesized_computation());
                let mut optimizer = ComputationNormalizer::new(template.clone());
                let optimized_template = optimizer.normalize();
                let expr = optimized_template.expr();
                let ops = expr.ops();
                let args = optimized_template.arg_interpretation();
                let mut consts = optimized_template.consts().iter().copied().collect::<HashSet<_>>();

                let mut adapted_args = template.arg_interpretation().to_vec();
                let new_args = optimized_template
                    .arg_interpretation()
                    .iter()
                    .filter(|arg| !adapted_args.contains(arg))
                    .collect::<Vec<_>>();

                for arg in new_args.iter() {
                    if let Arg::TinyConst(c) = arg {
                        consts.insert(*c as i128);
                    }
                }

                let consts = {
                    let mut v = consts.into_iter().collect::<Vec<_>>();
                    v.sort();
                    v
                };

                adapted_args.extend(new_args.into_iter().map(|arg| {
                    match arg {
                        Arg::Input {
                            ..
                        } => unreachable!(
                            "Found: {arg:?}, which we did not expect from initial args {:?}",
                            template.arg_interpretation()
                        ),
                        Arg::Const(index) => Arg::Const(
                            consts
                                .iter()
                                .position(|&v| v == optimized_template.consts()[*index as usize])
                                .unwrap()
                                .try_into()
                                .unwrap(),
                        ),
                        Arg::TinyConst(c) => {
                            Arg::Const(consts.iter().position(|&v| v == *c as i128).unwrap().try_into().unwrap())
                        },
                    }
                }));
                let ops = ops
                    .iter()
                    .copied()
                    .map(|op| match op {
                        Op::Hole(index) => {
                            let to_find = match args[index as usize] {
                                Arg::TinyConst(c) => {
                                    Arg::Const(consts.iter().position(|&v| v == c as i128).unwrap().try_into().unwrap())
                                },
                                Arg::Const(c) => Arg::Const(
                                    consts
                                        .iter()
                                        .position(|&v| v == optimized_template.consts()[c as usize])
                                        .unwrap()
                                        .try_into()
                                        .unwrap(),
                                ),
                                arg => arg,
                            };

                            Op::Hole(
                                adapted_args
                                    .iter()
                                    .position(|arg| arg == &to_find)
                                    .unwrap()
                                    .try_into()
                                    .unwrap(),
                            )
                        },
                        op => op,
                    })
                    .collect();
                trace!(
                    "New ops for: {} => {}: {ops:?} with consts: {consts:?}",
                    template.display(ARG_NAMES),
                    optimized_template.display(ARG_NAMES)
                );
                OptimizedPreparedTemplate {
                    ops,
                    consts,
                }
            })
            .collect::<Vec<_>>();

        let mut seen = HashSet::new();
        let result = self
            .templates
            .drain(..)
            .zip(optimized_templates.iter())
            .filter(|(template, optimized_template)| {
                let result = seen.insert(*optimized_template);

                Self::template_as_computation(template, self.output_bits, |c| {
                    debug!("Keep {optimized_template:?} = {result} | {}", c.display(ARG_NAMES))
                });

                result
            })
            .map(|(template, _)| template)
            .collect::<Vec<_>>();

        info!("Remaining: {} templates", result.len());

        // not yet implemented: Template
        // (0xD >> (0x40 - sbe(A))) ^ (0xD >> ((0x40 - sbe(A)) + 0x7)
        // =>
        // (13 >> (64 - sbe(A))) ^ (13 >> ((64 - sbe(A)) + 7))

        // [Const(13), Const(64), Hole(0), Sub, Shr, Const(13), Const(64), Hole(1), Sub, Const(7), Add, Shr, Xor]: ', rust_begin_unwindliblisa-synth/src/templates/optimizer.rs

        result
    }
}
