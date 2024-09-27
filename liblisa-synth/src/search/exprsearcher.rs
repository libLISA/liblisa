use std::fmt::Debug;

use liblisa::semantics::default::computation::{AsComputationRef, ExpressionComputation, OutputEncoding, PreparedComparison};
use liblisa::semantics::{Computation, IoType};
use liblisa::value::AsValue;
use log::info;

use super::searcher::{CheckValueResult, Searcher};
use crate::templates::preprocess::PreprocessedTemplate;
use crate::templates::EXPR_TEMPLATES;
use crate::{Synthesizer, SynthesizerBase, SynthesizerOutput};

#[derive(Clone)]
pub struct TemplateSynthesizer<'a> {
    searcher: Searcher<'a, CheckValueResult>,
    hypothesis: Option<ExpressionComputation>,
    output_type: IoType,
    can_do_little_endian: bool,
}

impl Debug for TemplateSynthesizer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TemplateSynthesizer")
            .field("hypothesis", &self.hypothesis)
            .field("output_type", &self.output_type)
            .finish()
    }
}

impl<'a> TemplateSynthesizer<'a> {
    pub fn new_with_custom_templates(templates: &'a [PreprocessedTemplate], input_types: &[IoType], output_type: IoType) -> Self {
        info!("Created synthesizer for {:?} => {:?}", input_types, output_type);

        TemplateSynthesizer {
            searcher: Searcher::new_with_custom_templates(templates, input_types, output_type),
            hypothesis: None,
            output_type,
            can_do_little_endian: false,
        }
    }
}

impl SynthesizerBase for TemplateSynthesizer<'_> {
    type Hypothesis = ExpressionComputation;
    type Computation = ExpressionComputation;

    fn new(input_types: &[IoType], output_type: IoType) -> Self {
        assert!(input_types.len() <= 16);

        Self::new_with_custom_templates(&EXPR_TEMPLATES, input_types, output_type)
    }

    fn hypothesis(&self) -> Option<&Self::Hypothesis> {
        self.hypothesis.as_ref()
    }

    fn has_given_up(&self) -> bool {
        self.searcher.has_given_up()
    }

    fn needs_requester(&self) -> bool {
        false
    }

    fn into_computation(self) -> Option<Self::Computation> {
        self.hypothesis
    }
}

impl<Output: SynthesizerOutput + AsValue> Synthesizer<Output> for TemplateSynthesizer<'_>
where
    for<'o> Output::Borrowed<'o>: AsValue,
{
    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: Output::Borrowed<'_>) -> bool {
        self.hypothesis
            .as_ref()
            .map(|hyp| hyp.as_internal().compare_eq(inputs, output.as_value()))
            .unwrap_or(false)
    }

    fn add_case<V: AsValue>(&mut self, inputs: &[V], expected_output: Output) {
        self.searcher
            .add_case(inputs, PreparedComparison::from(&expected_output.as_value()));

        // If the current hypothesis is consistent we shouldn't search for a new hypothesis
        if !<Self as Synthesizer<Output>>::is_consistent(self, inputs, expected_output.borrow()) {
            if let Some(hyp) = self.hypothesis.as_mut()
                && self.can_do_little_endian
            {
                info!("Trying little-endian output variant of hypothesis...");
                hyp.set_output_encoding(OutputEncoding::UnsignedLittleEndian);

                if <Self as Synthesizer<Output>>::is_consistent(self, inputs, expected_output.borrow()) {
                    return;
                }
            }

            info!(
                "Hypothesis is inconsistent, finding next expression matching all cases (new case added: {inputs:X?} -> {expected_output:?})"
            );
            self.hypothesis = self.searcher.next_expr().map(|(next, c)| {
                next.to_template_computation(if c.big_endian {
                    self.can_do_little_endian = c.little_endian;
                    OutputEncoding::UnsignedBigEndian
                } else if c.little_endian {
                    self.can_do_little_endian = false;
                    OutputEncoding::UnsignedLittleEndian
                } else {
                    unreachable!()
                })
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::default::expr;
    use liblisa::semantics::default::ops::HoleOp;
    use liblisa::semantics::{Computation, IoType, ARG_NAMES};
    use liblisa::utils::sign_extend;
    use liblisa::value::{AsValue, OwnedValue, Value};
    use test_log::test;

    use crate::search::exprsearcher::TemplateSynthesizer;
    use crate::templates::{Template, EXPR_TEMPLATES};
    use crate::{synthesize_from_fn, Synthesizer, SynthesizerBase, SynthesizerOutput};

    #[test]
    pub fn find_identity() {
        let inputs = &[IoType::Integer {
            num_bits: 64,
        }];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(inputs[0].to_owned_value());
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_plus_3() {
        let inputs = &[IoType::Integer {
            num_bits: 64,
        }];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(inputs[0].unwrap_num().wrapping_add(3)));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sum_x_3_sign_extend_y() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 1,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0]
                    .unwrap_num()
                    .wrapping_add(3)
                    .wrapping_add(inputs[3].unwrap_num() as u8 as i8 as i64 as u64),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_le_bytes() {
        let inputs = &[IoType::Integer {
            num_bits: 64,
        }];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Bytes {
                num_bytes: 8,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Bytes(inputs[0].unwrap_num().to_le_bytes().to_vec()));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_be_bytes() {
        let inputs = &[IoType::Integer {
            num_bits: 64,
        }];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Bytes {
                num_bytes: 8,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Bytes(inputs[0].unwrap_num().to_be_bytes().to_vec()));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sign_extend() {
        let inputs = &[IoType::Integer {
            num_bits: 8,
        }];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(sign_extend(inputs[0].unwrap_num() as i128, 8) as u64));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_add() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(inputs[0].unwrap_num().wrapping_add(inputs[1].unwrap_num())));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_sub() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(inputs[0].unwrap_num().wrapping_sub(inputs[1].unwrap_num())));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_adc() {
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
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0]
                    .unwrap_num()
                    .wrapping_add(inputs[1].unwrap_num())
                    .wrapping_add(inputs[2].unwrap_num()),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test]
    pub fn find_and() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(inputs[0].unwrap_num() & inputs[1].unwrap_num()));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test_log::test]
    pub fn find_bit_set() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0].unwrap_num() | (1 << (inputs[1].unwrap_num() & 0b111)),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());

        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0].unwrap_num() | (1 << (inputs[1].unwrap_num() & 0b1111)),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());

        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0].unwrap_num() | (1 << (inputs[1].unwrap_num() & 0b11111)),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test_log::test]
    pub fn find_bit_reset() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0].unwrap_num() & !(1 << (inputs[1].unwrap_num() & 0b111)),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());

        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0].unwrap_num() & !(1 << (inputs[1].unwrap_num() & 0b1111)),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());

        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some(OwnedValue::Num(
                inputs[0].unwrap_num() & !(1 << (inputs[1].unwrap_num() & 0b11111)),
            ))
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test_log::test]
    pub fn find_and_with_bit_set() {
        let inputs = &[
            IoType::Integer {
                num_bits: 8,
            },
            IoType::Integer {
                num_bits: 7,
            },
        ];
        let s = TemplateSynthesizer::new(
            inputs,
            IoType::Integer {
                num_bits: 8,
            },
        );
        let f = |inputs: &[Value]| Some(OwnedValue::Num(inputs[0].unwrap_num() & (inputs[1].unwrap_num() | 0x80)));
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    #[test_log::test]
    pub fn find_jump_offset() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 33,
            },
        ];
        let s = TemplateSynthesizer::new_with_custom_templates(
            &EXPR_TEMPLATES,
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );
        let f = |inputs: &[Value]| {
            Some({
                let rip = inputs[0].unwrap_num();
                let offset = (inputs[1].unwrap_num() as u32).swap_bytes() as i32;

                OwnedValue::Num((rip as i64).wrapping_add(offset as i64 + 6) as u64)
            })
        };
        assert!(synthesize_from_fn::<OwnedValue, _>(&mut rand::thread_rng(), s, inputs, f).is_some());
    }

    fn add_case<O: SynthesizerOutput, S: Synthesizer<O>>(s: &mut S, inputs: &[impl AsValue], output: O) {
        s.add_case(inputs, output)
    }

    #[test_log::test]
    pub fn find_shl_of_condition()
    where
        for<'o> <OwnedValue as SynthesizerOutput>::Borrowed<'o>: AsValue,
    {
        use liblisa::semantics::default::builder::*;
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
            IoType::Integer {
                num_bits: 1,
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
            IoType::Integer {
                num_bits: 1,
            },
        ];

        const A: ExprBuilder<1, HoleOp<0>> = hole::<0>();
        const B: ExprBuilder<1, HoleOp<1>> = hole::<1>();
        const C: ExprBuilder<1, HoleOp<2>> = hole::<2>();

        let custom = crate::templates::templates!(
            128,
            &[expr!(B.crop::<5>().if_zero(
                C,
                xor(
                    select::<32, 1, _, _>(shl(A, B.crop::<5>())),
                    select::<31, 1, _, _>(shl(A, B.crop::<5>()))
                )
            )),]
        );

        let mut s = TemplateSynthesizer::new_with_custom_templates(
            &custom,
            inputs,
            IoType::Integer {
                num_bits: 1,
            },
        );

        use Value::*;
        // shl OF:
        // num = num & 0x1f
        // if num == 0 then OF else
        // if num == 1 then
        let cases = [
            (
                &[
                    Num(0xE9),
                    Num(0x5420640),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0x21),
                    Num(0x5EFEBAD5),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                    Num(0x01),
                    Num(0x00),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0x02),
                    Num(0x3AA10A17),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0x00),
                    Num(0xCFC9FFFF),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x01),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0x00),
                    Num(0xEE992A71),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                    Num(0x01),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0xFF),
                    Num(0x3E435D76),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0x80),
                    Num(0x6C6FD5BD),
                    Num(0x00),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                ],
                OwnedValue::Num(1),
            ),
            (
                &[
                    Num(0x00),
                    Num(0x3BA00000),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                    Num(0x01),
                    Num(0x00),
                    Num(0x01),
                ],
                OwnedValue::Num(1),
            ),
            // Choice: #1: 0x0 with cases (6)
            // if OF=0 and shifting by 0
            (
                &[
                    Num(0x00),
                    Num(0xCEFF7950),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                ],
                OwnedValue::Num(0),
            ),
            (
                &[
                    Num(0x00),
                    Num(0x3EDBEE6A),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                ],
                OwnedValue::Num(0),
            ),
            // last bit shifted out = sign bit
            (
                &[
                    Num(0x3F),
                    Num(0x3837FFFF),
                    Num(0x01),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                ],
                OwnedValue::Num(0),
            ),
            (
                &[
                    Num(0xFE),
                    Num(0x76FFFFFF),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                ],
                OwnedValue::Num(0),
            ),
            (
                &[
                    Num(0x65),
                    Num(0x362D0),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x01),
                    Num(0x00),
                ],
                OwnedValue::Num(0),
            ),
            (
                &[
                    Num(0x03),
                    Num(0x3CE70000),
                    Num(0x00),
                    Num(0x01),
                    Num(0x01),
                    Num(0x00),
                    Num(0x00),
                    Num(0x00),
                ],
                OwnedValue::Num(0),
            ),
        ];

        for (inputs, expected) in cases.iter() {
            {
                let shift = inputs[0].unwrap_num();
                let n = inputs[1].unwrap_num();
                let of = inputs[7].unwrap_num();

                let output = if shift & 0x1f != 0 {
                    let result = n << (shift & 0x1f);
                    if (result >> 32) & 1 == (result >> 31) & 1 {
                        0
                    } else {
                        1
                    }
                } else {
                    of
                };

                assert_eq!(
                    &OwnedValue::Num(output),
                    expected,
                    "Written formula does not correspond with real CPU for {inputs:X?} -> {expected:X?}"
                );
            }

            add_case::<OwnedValue, _>(&mut s, inputs.as_ref(), expected.clone());
        }

        println!("Result: {}", s.hypothesis().unwrap().display(ARG_NAMES));
    }

    #[test_log::test]
    pub fn find_bytemask() {
        let inputs = &[IoType::Integer {
            num_bits: 64,
        }];
        let mut s = TemplateSynthesizer::new_with_custom_templates(
            &EXPR_TEMPLATES,
            inputs,
            IoType::Integer {
                num_bits: 8,
            },
        );

        use Value::*;

        // Category of computations producing one result
        add_case::<OwnedValue, _>(&mut s, &[Num(0x00_00_00_00_80_42_75_82)], OwnedValue::Num(0b0000_1001));
        add_case::<OwnedValue, _>(&mut s, &[Num(0xff_ff_ff_ff_80_42_75_82)], OwnedValue::Num(0b1111_1001));
        add_case::<OwnedValue, _>(&mut s, &[Num(0xff_7f_ff_ff_80_42_75_82)], OwnedValue::Num(0b1011_1001));
        add_case::<OwnedValue, _>(&mut s, &[Num(0xff_8f_ff_ff_80_42_75_82)], OwnedValue::Num(0b1111_1001));

        let hypothesis = s.hypothesis().unwrap();
        println!("Hypothesis: {}", hypothesis.display(ARG_NAMES));
    }

    #[test_log::test]
    pub fn find_id() {
        let inputs = &[
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 64,
            },
            IoType::Integer {
                num_bits: 8,
            },
        ];
        let mut s = TemplateSynthesizer::new_with_custom_templates(
            &EXPR_TEMPLATES,
            inputs,
            IoType::Integer {
                num_bits: 64,
            },
        );

        use Value::*;

        // Category of computations producing one result
        add_case::<OwnedValue, _>(
            &mut s,
            &[
                Num(0x17D8000000000000),
                Num(0x792C1),
                Num(0x66A10DC54BC00000),
                Num(0xFFFE1B22A70E3BFF),
                Num(0x3FFFFAAFFFFF),
                Num(0xEE95F5FFA1EFFFFF),
                Num(0x3FFFFFFFF0AD),
                Num(0x1F),
                Num(0x2),
            ],
            OwnedValue::Num(0x66A10DC54BC00000),
        );

        let hypothesis = s.hypothesis().unwrap();
        println!("Hypothesis: {}", hypothesis.display(ARG_NAMES));
    }
}
