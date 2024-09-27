use std::ops::Range;

use arrayvec::ArrayVec;
use liblisa::semantics::default::builder::*;
use liblisa::semantics::default::{expr, Expr, MAX_TEMPLATE_ARGS};
use liblisa::utils::bitmap::BitmapSlice;

use self::ordering::Ordering;
use crate::templates::preprocess::PreprocessedTemplate;

pub mod normalize_filter;
mod ordering;
pub mod preprocess;
mod symexec;

pub const CONST_VALUES: &[i128] = &[
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 23, 24, 31, 32, 39, 40, 47, 48, 55, 56, 63, 64,
];

pub trait AnyTemplate: std::fmt::Debug {
    fn num_unfilled_holes(&self) -> usize;

    fn num_total_holes(&self) -> usize {
        self.num_unfilled_holes()
    }

    /// If `ordering_index[index] = Some(reset_value_index)`, then `counter[index] < counter[reset_value_index]`.
    /// This limits the duplicate expressions we generate.
    /// `ordering_indexes[n]` returns values `[x_0, x_1, ..]` where `x_i > n`.
    fn ordering_indexes(&self) -> &[Option<usize>];

    type IterActiveIndices<'me>: Iterator<Item = usize>
    where
        Self: 'me;

    fn active_indices(&self) -> Self::IterActiveIndices<'_>;

    fn start_value(&self) -> usize {
        0
    }

    fn new_counter(&self) -> ArrayVec<u16, MAX_TEMPLATE_ARGS> {
        (0..self.num_total_holes()).map(|_| 0).collect()
    }
}

#[derive(Debug)]
pub struct Template<'a> {
    expr: Expr<'a>,
    ordering_indexes: Vec<Option<usize>>,
    num_holes: usize,
}

impl<'a> Template<'a> {
    pub fn new(expr: Expr<'a>) -> Self {
        let num_holes = expr.count_holes();
        let ordering = Ordering::of(&expr);
        let ordering_indexes: Vec<Option<usize>> = (0..num_holes)
            .map(|hole_index| {
                let group = ordering
                    .iter()
                    .find(|group| group.get(hole_index))
                    .expect("Ordering should have assigned a group to every hole");

                let pos = group.iter_one_indices().find(|&item| item > hole_index);
                pos
            })
            .collect::<Vec<_>>();

        for (index, ordering_indexes) in ordering_indexes.iter().enumerate() {
            assert!(ordering_indexes.iter().all(|&ordering_index| ordering_index > index));
        }

        Self {
            expr,
            ordering_indexes,
            num_holes,
        }
    }

    pub fn expr(&self) -> &Expr<'a> {
        &self.expr
    }
}

impl<'a> AnyTemplate for Template<'a> {
    fn num_unfilled_holes(&self) -> usize {
        self.num_holes
    }

    fn ordering_indexes(&self) -> &[Option<usize>] {
        &self.ordering_indexes
    }

    type IterActiveIndices<'me>
        = Range<usize>
    where
        Self: 'me;

    fn active_indices(&self) -> Self::IterActiveIndices<'_> {
        0..self.num_holes
    }
}

macro_rules! concat_many {
    ($a:expr) => { $a };
    ($a:expr, $($rest:expr),* $(,)*) => {
        $crate::utils::concat_exprs($a, concat_many!($($rest),*))
    }
}

macro_rules! templates {
    ($output_bits:expr, $templates:expr) => {{
        use rayon::prelude::*;
        let mut consts = std::collections::HashSet::new();
        let preprocessed_templates = $templates
            .par_iter()
            .flat_map(|t| {
                $crate::templates::preprocess::TemplatePreprocessor::new(
                    &Template::new(*t),
                    $crate::templates::CONST_VALUES,
                    $output_bits,
                )
                .preprocess_templates()
            })
            .collect::<Vec<_>>()
            .into_iter()
            .filter(|t| {
                t.const_output()
                    .map(|const_output| consts.insert(const_output))
                    .unwrap_or(true)
            })
            .collect::<Vec<_>>();

        let optimizer = $crate::templates::normalize_filter::PreprocessedTemplateNormalizationFilter::new(
            preprocessed_templates,
            $output_bits,
        );
        optimizer.run()
    }};
}
pub(crate) use templates;

macro_rules! generate_zf_sf_pf_from {
    ($rule:expr) => {{
        [
            // Zero flag
            expr!(is_zero($rule.crop::<64>())),
            expr!(is_zero($rule.crop::<32>())),
            expr!(is_zero($rule.crop::<16>())),
            expr!(is_zero($rule.crop::<8>())),
            // Sign flag
            expr!(select::<7, 1, _, _>($rule)),
            expr!(select::<15, 1, _, _>($rule)),
            expr!(select::<31, 1, _, _>($rule)),
            expr!(select::<63, 1, _, _>($rule)),
            // Parity flag
            expr!(parity($rule)),
        ]
    }};
}

macro_rules! sum {
    ($a:expr, $($b:expr),+ $(,)*) => {
        add($a, sum! { $($b),+ })
    };
    ($a:expr) => {
        $a
    }
}

macro_rules! or_all {
    ($a:expr, $($b:expr),+ $(,)*) => {
        or($a, or_all! { $($b),+ })
    };
    ($a:expr) => {
        $a
    }
}

macro_rules! xor_top2 {
    ($n:literal, $e:expr) => {
        xor(select::<{ $n - 1 }, 1, _, _>($e), select::<{ $n - 2 }, 1, _, _>($e))
    };
}

const A: ExprBuilder<1, liblisa::semantics::default::ops::HoleOp<0>> = hole();
const B: ExprBuilder<1, liblisa::semantics::default::ops::HoleOp<1>> = hole();
const C: ExprBuilder<1, liblisa::semantics::default::ops::HoleOp<2>> = hole();
const D: ExprBuilder<1, liblisa::semantics::default::ops::HoleOp<3>> = hole();

pub static INTERNAL_EXPR_TEMPLATES: &[Expr] = &concat_many! {
    [
        // unary
        expr!(A),
        expr!(not(A)),
        expr!(bit_mask(A)),

        // binary
        expr!(add(A, B)),
        expr!(sub(A, B)),
        expr!(mul(A, B)),

        // phadd[wd]
        expr!(add(select::<0, 16, _, _>(A), select::<16, 16, _, _>(B))),
        expr!(add(select::<0, 32, _, _>(A), select::<32, 32, _, _>(B))),

        // phsub[wd]
        expr!(sub(select::<0, 16, _, _>(A), select::<16, 16, _, _>(B))),
        expr!(sub(select::<0, 32, _, _>(A), select::<32, 32, _, _>(B))),

        // pmulhrsw
        expr!(shr(add(shr(mul(A, B), C), c::<1>()), c::<1>())),
        expr!(shr(add(add(A, B), C), D)),
        expr!(shr(A, mul(B, C))),

        // mul higher order bits
        expr!(select::<64, 64, _, _>(mul(A, B))),
        expr!(select::<32, 32, _, _>(mul(A, B))),
        expr!(select::<16, 16, _, _>(mul(A, B))),
        expr!(select::<8, 8, _, _>(mul(A, B))),

        expr!(div(or(A, shl(B, c::<8>())), C)),
        expr!(div(or(A, shl(B, c::<16>())), C)),
        expr!(div(or(A, shl(B, c::<32>())), C)),
        expr!(div(or(A, shl(B, c::<64>())), C)),
        expr!(or(div(A, B.sign_extend::<8>()).crop::<8>(), shl(rem(A, B.sign_extend::<8>()), c::<8>()))),

        expr!(udiv(or(A, shl(B, c::<8>())), C)),
        expr!(udiv(or(A, shl(B, c::<16>())), C)),
        expr!(udiv(or(A, shl(B, c::<32>())), C)),
        expr!(udiv(or(A, shl(B, c::<64>())), C)),
        expr!(or(udiv(A, B.crop::<8>()).crop::<8>(), shl(urem(A, B.crop::<8>()), c::<8>()))),

        expr!(rem(or(A, shl(B, c::<8>())), C)),
        expr!(rem(or(A, shl(B, c::<16>())), C)),
        expr!(rem(or(A, shl(B, c::<32>())), C)),
        expr!(rem(or(A, shl(B, c::<64>())), C)),

        expr!(urem(or(A, shl(B, c::<8>())), C)),
        expr!(urem(or(A, shl(B, c::<16>())), C)),
        expr!(urem(or(A, shl(B, c::<32>())), C)),
        expr!(urem(or(A, shl(B, c::<64>())), C)),

        expr!(shl(A, B)),

        // Bit setting (for example BTS)
        expr!(or(A, shl(C, sub(B, D).crop::<3>()))),
        expr!(or(A, shl(C, sub(B, D).crop::<4>()))),
        expr!(or(A, shl(C, sub(B, D).crop::<5>()))),
        expr!(or(A, shl(C, sub(B, D).crop::<6>()))),

        // Bit flipping (for example BTC)
        expr!(xor(A, shl(C, sub(B, D).crop::<3>()))),
        expr!(xor(A, shl(C, sub(B, D).crop::<4>()))),
        expr!(xor(A, shl(C, sub(B, D).crop::<5>()))),
        expr!(xor(A, shl(C, sub(B, D).crop::<6>()))),

        // Resetting bits (for example BTR)
        expr!(and(A, not(shl(C, sub(B, D).crop::<3>())))),
        expr!(and(A, not(shl(C, sub(B, D).crop::<4>())))),
        expr!(and(A, not(shl(C, sub(B, D).crop::<5>())))),
        expr!(and(A, not(shl(C, sub(B, D).crop::<6>())))),

        expr!(shr(A, B)),
        expr!(shr(A, B.crop::<3>())),
        expr!(shr(A, B.crop::<4>())),
        expr!(shr(A, B.crop::<5>())),
        expr!(shr(A, B.crop::<6>())),
        expr!(and(shr(A, B), bit_mask(C))),

        expr!(and(A, B)),
        expr!(and(A, select::<8, 8, _, _>(B))),
        expr!(and(A, select::<16, 8, _, _>(B))),
        expr!(and(A, select::<24, 8, _, _>(B))),
        // To handle the case where a small imm value is sign-extended, where libLISA has a tendency to see different sign bits as different instructions
        expr!(and(A, or(B, shl(c::<1>(), c::<7>())).sign_extend::<8>())),

        expr!(or(A, B)),
        expr!(or(A, or(B, shl(C, D)))),
        expr!(xor(A, B)),
        expr!(xor(A, or(B, shl(C, D)))),

        expr!(A.byte_mask()),

        // Leading / trailing zeros
        expr!(add(A.trailing_zeros(), B)),
        expr!(sub(A.leading_zeros(), add(B, C))),

        // Index of most significant nonzero bit (index of least significant bit == trailing zeros)
        expr!(sub(add(c::<127>(), B), and(A, bit_mask(C)).leading_zeros())),

        expr!(and(A, bit_mask(sub(B, and(C, bit_mask(D)))))),
        expr!(and(A, shr(bit_mask(B), C))),

        // An aid for generating constant expressions close to u[8,16,32,64]::MIN/MAX
        expr!(add(bit_mask(A), B)),

        expr!(add(A, mul(B, C))),
        expr!(sub(add(A, B), C)),
        expr!(sub(sub(A, sub(c::<0>(), B).crop::<16>()), C)),
        expr!(add(A, shl(B, C))),
        expr!(add(A, add(shl(B, C), D))),
        expr!(add(shl(add(A.crop::<8>(), select::<8, 8, _, _>(A)).crop::<8>(), B), shl(A.crop::<8>(), C))),

        // ROL
        expr!(A.rol::<8, _, _>(B.crop::<3>())),
        expr!(A.rol::<16, _, _>(B.crop::<4>())),
        expr!(A.rol::<32, _, _>(B.crop::<5>())),
        expr!(A.rol::<64, _, _>(B.crop::<6>())),

        // ROR
        expr!(A.rol::<8, _, _>(sub(c::<8>(), B.crop::<3>()))),
        expr!(A.rol::<16, _, _>(sub(c::<16>(), B.crop::<4>()))),
        expr!(A.rol::<32, _, _>(sub(c::<32>(), B.crop::<5>()))),
        expr!(A.rol::<64, _, _>(sub(c::<64>(), B.crop::<6>()))),

        // RCL
        expr!(or(A, shl(B, c::<8>())).rol::<9, _, _>(and(C, bit_mask(D)))),
        expr!(or(A, shl(B, c::<16>())).rol::<17, _, _>(and(C, bit_mask(D)))),
        expr!(or(A, shl(B, c::<32>())).rol::<33, _, _>(and(C, bit_mask(D)))),
        expr!(or(A, shl(B, c::<64>())).rol::<65, _, _>(and(C, bit_mask(D)))),

        // RCR
        expr!(or(A, shl(B, c::<8>())).rol::<9, _, _>(sub(c::<{9 * 10}>(), and(C, bit_mask(D))))),
        expr!(or(A, shl(B, c::<16>())).rol::<17, _, _>(sub(c::<{17 * 7}>(), and(C, bit_mask(D))))),
        expr!(or(A, shl(B, c::<32>())).rol::<33, _, _>(sub(c::<{33 * 3}>(), and(C, bit_mask(D))))),
        expr!(or(A, shl(B, c::<64>())).rol::<65, _, _>(sub(c::<65>(), and(C, bit_mask(D))))),

        // adc & sbb
        expr!(add(add(A, B), C)),
        expr!(sub(sub(A, B), C)),

        // little-endian jumps
        expr!(add(add(A, B), select::<8, 8, _, _>(C).sign_extend::<8>())),
        expr!(add(add(A, B), select::<8, 16, _, _>(C).sign_extend::<16>())),
        expr!(add(add(A, B), select::<8, 32, _, _>(C).sign_extend::<32>())),

        // big-endian jumps
        expr!(add(add(A, B), C.sign_extend::<8>())),
        expr!(add(add(A, B), C.sign_extend::<16>())),
        expr!(add(add(A, B), C.sign_extend::<32>())),

        // SHLD
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<8>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<16>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<24>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<32>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<40>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<48>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<56>()))),
        expr!(or(shl(A, or(C, shl(D, c::<4>()))), shr(shl(B, or(C, shl(D, c::<4>()))), c::<64>()))),

        // SHRD
        expr!(shr(or(A, shl(B, shl(c::<1>(), D))), and(C, bit_mask(D)))),
        expr!(shr(or(A, shl(B, shl(c::<1>(), D))), or(C, shl(D, c::<4>())))),

        // sha1msg1
        expr!(
            // W5 XOR W3
            or(xor(select::<64, 32, _, _>(shl(B, C)), A.crop::<32>()),
            // W4 XOR W2
            or(shl(xor(select::<96, 32, _, _>(shl(B, C)), select::<32, 32, _, _>(A)), c::<32>()),
            // W3 XOR W1
            or(shl(xor(A.crop::<32>(), select::<64, 32, _, _>(A)), c::<64>()),
            // W2 XOR W0
            shl(xor(select::<32, 32, _, _>(A), select::<96, 32, _, _>(A)), c::<96>()))))
        ),

        // sha1msg2
        expr!(
            // W19 = (SRC1[31: 0] XOR W16) ROL 1;
            or(or(or(xor(select::<0, 32, _, _>(A), xor(select::<96, 32, _, _>(A), select::<64, 32, _, _>(B)).rol::<32, _, _>(c::<1>())).rol::<32, _, _>(c::<1>()),
            // W18 = (SRC1[63: 32] XOR SRC2[31: 0]) ROL 1;
            shl(xor(select::<32, 32, _, _>(A), select::<0, 32, _, _>(B)).rol::<32, _, _>(c::<1>()), c::<32>())),
            // W17 = (SRC1[95:64] XOR SRC2[63: 32]) ROL 1;
            shl(xor(select::<64, 32, _, _>(A), select::<32, 32, _, _>(B)).rol::<32, _, _>(c::<1>()), c::<64>())),
            // W16 = (SRC1[127:96] XOR SRC2[95:64] ) ROL 1;
            shl(xor(select::<96, 32, _, _>(A), select::<64, 32, _, _>(B)).rol::<32, _, _>(c::<1>()), c::<96>()))
        ),

        // sha1nexte
        expr!(add(A, B.rol::<32, _, _>(c::<30>()))),

        // sha256msg1
        expr!({
            macro_rules! sigma0 {
                ($e:expr) => {
                    xor(xor($e.rol::<32, _, _>(c::<25>()), $e.rol::<32, _, _>(c::<14>())), shr($e, c::<3>()))
                }
            }

            let w0 = select::<0, 32, _, _>(A);
            let w1 = select::<32, 32, _, _>(A);
            let w2 = select::<64, 32, _, _>(A);
            let w3 = select::<96, 32, _, _>(A);
            let w4 = select::<0, 32, _, _>(B);

            let r0 = add(w0, sigma0! { w1 }).crop::<32>();
            let r1 = add(w1, sigma0! { w2 }).crop::<32>();
            let r2 = add(w2, sigma0! { w3 }).crop::<32>();
            let r3 = add(w3, sigma0! { w4 }).crop::<32>();

            or_all! {
                r0,
                shl(r1, c::<32>()),
                shl(r2, c::<64>()),
                shl(r3, c::<96>()),
            }
        }),

        // sha256msg2
        expr!({
            macro_rules! sigma1 {
                ($e:expr) => {
                    xor(xor($e.rol::<32, _, _>(c::<15>()), $e.rol::<32, _, _>(c::<13>())), shr($e, c::<10>()))
                }
            }

            let w14 = select::<0, 32, _, _>(B);
            let w15 = select::<32, 32, _, _>(B);

            let w16 = add(select::<0, 32, _, _>(A), sigma1! { w14 }).crop::<32>();
            let w17 = add(select::<32, 32, _, _>(A), sigma1! { w15 }).crop::<32>();
            let w18 = add(select::<64, 32, _, _>(A), sigma1! { w16 }).crop::<32>();
            let w19 = add(select::<96, 32, _, _>(A), sigma1! { w17 }).crop::<32>();

            or_all! {
                w16,
                shl(w17, c::<32>()),
                shl(w18, c::<64>()),
                shl(w19, c::<96>()),
            }
        }),

        // psadbw
        expr!({
            let a0 = select::<0, 8, _, _>(A);
            let a1 = select::<8, 8, _, _>(A);
            let a2 = select::<16, 8, _, _>(A);
            let a3 = select::<24, 8, _, _>(A);
            let a4 = select::<32, 8, _, _>(A);
            let a5 = select::<40, 8, _, _>(A);
            let a6 = select::<48, 8, _, _>(A);
            let a7 = select::<56, 8, _, _>(A);

            let b0 = select::<0, 8, _, _>(B);
            let b1 = select::<8, 8, _, _>(B);
            let b2 = select::<16, 8, _, _>(B);
            let b3 = select::<24, 8, _, _>(B);
            let b4 = select::<32, 8, _, _>(B);
            let b5 = select::<40, 8, _, _>(B);
            let b6 = select::<48, 8, _, _>(B);
            let b7 = select::<56, 8, _, _>(B);

            sum! {
                sub(a0, b0).abs(),
                sub(a1, b1).abs(),
                sub(a2, b2).abs(),
                sub(a3, b3).abs(),
                sub(a4, b4).abs(),
                sub(a5, b5).abs(),
                sub(a6, b6).abs(),
                sub(a7, b7).abs(),
            }
        }),

        // mpsadbw
        expr!({
            let a0 = select::<0, 8, _, _>(A);
            let a1 = select::<8, 8, _, _>(A);
            let a2 = select::<16, 8, _, _>(A);
            let a3 = select::<24, 8, _, _>(A);
            let a4 = select::<32, 8, _, _>(A);
            let a5 = select::<40, 8, _, _>(A);
            let a6 = select::<48, 8, _, _>(A);
            let a7 = select::<56, 8, _, _>(A);
            let a8 = select::<64, 8, _, _>(A);
            let a9 = select::<72, 8, _, _>(A);
            let a10 = select::<80, 8, _, _>(A);

            let b0 = select::<0, 8, _, _>(B);
            let b1 = select::<8, 8, _, _>(B);
            let b2 = select::<16, 8, _, _>(B);
            let b3 = select::<24, 8, _, _>(B);

            let r0 = sum! { sub(a0, b0).abs(), sub(a1, b1).abs(), sub(a2, b2).abs(), sub(a3, b3).abs() };
            let r1 = sum! { sub(a1, b0).abs(), sub(a2, b1).abs(), sub(a3, b2).abs(), sub(a4, b3).abs() };
            let r2 = sum! { sub(a2, b0).abs(), sub(a3, b1).abs(), sub(a4, b2).abs(), sub(a5, b3).abs() };
            let r3 = sum! { sub(a3, b0).abs(), sub(a4, b1).abs(), sub(a5, b2).abs(), sub(a6, b3).abs() };
            let r4 = sum! { sub(a4, b0).abs(), sub(a5, b1).abs(), sub(a6, b2).abs(), sub(a7, b3).abs() };
            let r5 = sum! { sub(a5, b0).abs(), sub(a6, b1).abs(), sub(a7, b2).abs(), sub(a8, b3).abs() };
            let r6 = sum! { sub(a6, b0).abs(), sub(a7, b1).abs(), sub(a8, b2).abs(), sub(a9, b3).abs() };
            let r7 = sum! { sub(a7, b0).abs(), sub(a8, b1).abs(), sub(a9, b2).abs(), sub(a10, b3).abs() };

            or_all! {
                r0,
                shl(r1, c::<16>()),
                shl(r2, c::<32>()),
                shl(r3, c::<48>()),
                shl(r4, c::<64>()),
                shl(r5, c::<80>()),
                shl(r6, c::<96>()),
                shl(r7, c::<112>())
            }
        }),

        // bslmsk
        expr!(bit_mask(add(A.trailing_zeros(), B))),

        // blsi
        expr!(shl(A, add(B.trailing_zeros(), C))),

        // blsr
        expr!(and(A, sub(B, C))),

        // betxr
        expr!(and(shr(A, C), bit_mask(select::<8, 8, _, _>(B)))),

        expr!(A.extract_bits(B)),
        expr!(A.deposit_bits(B)),
        expr!(sub(sub(A, B), shl(add(C, D), c::<3>()))),

        expr!(and(A, bit_mask(B)).popcount()),
        expr!(carryless_mul(A, B)),

        expr!(add(
            mul(shr(A, c::<8>()), shr(B, c::<8>())),
            mul(A.sign_extend::<8>(), B.sign_extend::<8>())
        )),
        expr!(add(
            mul(shr(A, c::<16>()), shr(B, c::<16>())),
            mul(A.sign_extend::<16>(), B.sign_extend::<16>())
        )),
        expr!(add(
            mul(shr(A, c::<32>()), shr(B, c::<32>())),
            mul(A.sign_extend::<32>(), B.sign_extend::<32>())
        )),
        expr!(add(
            mul(shr(A, c::<64>()), shr(B, c::<64>())),
            mul(A.sign_extend::<64>(), B.sign_extend::<64>())
        )),

        expr!(add(
            mul(shr(A, c::<8>()), shr(B, c::<8>())),
            mul(A.crop::<8>(), B.crop::<8>())
        )),
        expr!(add(
            mul(shr(A, c::<16>()), shr(B, c::<16>())),
            mul(A.crop::<16>(), B.crop::<16>())
        )),
        expr!(add(
            mul(shr(A, c::<32>()), shr(B, c::<32>())),
            mul(A.crop::<32>(), B.crop::<32>())
        )),
        expr!(add(
            mul(shr(A, c::<64>()), shr(B, c::<64>())),
            mul(A.crop::<64>(), B.crop::<64>())
        )),

        expr!(add(
            mul(shr(A, c::<8>()), shr(B, c::<8>())),
            mul(A.sign_extend::<8>(), B.crop::<8>())
        )),
        expr!(add(
            mul(shr(A, c::<16>()), shr(B, c::<16>())),
            mul(A.sign_extend::<16>(), B.crop::<16>())
        )),
        expr!(add(
            mul(shr(A, c::<32>()), shr(B, c::<32>())),
            mul(A.sign_extend::<32>(), B.crop::<32>())
        )),
        expr!(add(
            mul(shr(A, c::<64>()), shr(B, c::<64>())),
            mul(A.sign_extend::<64>(), B.crop::<64>())
        )),

        expr!(add(
            mul(shr(A, c::<8>()), shr(B, c::<8>())),
            mul(A.crop::<8>(), B.sign_extend::<8>())
        )),
        expr!(add(
            mul(shr(A, c::<16>()), shr(B, c::<16>())),
            mul(A.crop::<16>(), B.sign_extend::<16>())
        )),
        expr!(add(
            mul(shr(A, c::<32>()), shr(B, c::<32>())),
            mul(A.crop::<32>(), B.sign_extend::<32>())
        )),
        expr!(add(
            mul(shr(A, c::<64>()), shr(B, c::<64>())),
            mul(A.crop::<64>(), B.sign_extend::<64>())
        )),
    ]
};

pub static INTERNAL_SIMPLE_BOOLEAN_TEMPLATES: &[Expr] = &concat_many! {
    [
        // Zero checks for (part of) the operand
        expr!(A),
        expr!(is_zero(A)),
        expr!(is_zero(A.crop::<3>())),
        expr!(is_zero(A.crop::<4>())),
        expr!(is_zero(A.crop::<5>())),
        expr!(is_zero(A.crop::<6>())),

        // Sign flag of an operand
        expr!(select::<7, 1, _, _>(A)),
        expr!(select::<15, 1, _, _>(A)),
        expr!(select::<31, 1, _, _>(A)),
        expr!(select::<63, 1, _, _>(A)),
        expr!(select::<127, 1, _, _>(A)),

        // Parity of an operand
        expr!(parity(A)),

        expr!(is_zero(and(A, bit_mask(sub(B, and(C, bit_mask(D))))))),
        expr!(or(is_zero(xor(A, B)), is_zero(and(C, bit_mask(D))))),
        expr!(or(is_zero(xor(A, B)), not(is_zero(and(C, bit_mask(D)))))),
        expr!(and(is_zero(xor(A, B)), is_zero(and(C, bit_mask(D))))),
        expr!(less_than(shr(A, B), C)),
        expr!(is_zero(sub(and(shr(A, B), bit_mask(C)), and(D, bit_mask(C))))),
    ],

    // Add/sub
    generate_zf_sf_pf_from!(add(A, add(B, C))),
    generate_zf_sf_pf_from!(sub(sub(A, B), C)),
    generate_zf_sf_pf_from!(add(A, sub(c::<0>(), B).crop::<8>())),
    generate_zf_sf_pf_from!(add(A, sub(c::<0>(), B).crop::<16>())),
    generate_zf_sf_pf_from!(add(A, sub(c::<0>(), B).crop::<32>())),
    generate_zf_sf_pf_from!(add(A, sub(c::<0>(), B).crop::<64>())),

    [
        expr!(xor(parity(add(A, sub(c::<0>(), B).crop::<8>())), parity(add(A, (sub(sub(c::<0>(), B), C)).crop::<8>())))),
    ],

    [
        // phadd[wd]
        expr!(less_than(shl(c::<-1>(), C), add(select::<0, 16, _, _>(A).sign_extend::<16>(), select::<16, 16, _, _>(B).sign_extend::<16>()))),
        expr!(less_than(shl(c::<-1>(), C), add(select::<0, 32, _, _>(A).sign_extend::<32>(), select::<32, 32, _, _>(B).sign_extend::<32>()))),

        // phsub[wd]
        expr!(less_than(shl(c::<-1>(), C), sub(select::<0, 16, _, _>(A).sign_extend::<16>(), select::<16, 16, _, _>(B).sign_extend::<16>()))),
        expr!(less_than(shl(c::<-1>(), C), sub(select::<0, 32, _, _>(A).sign_extend::<32>(), select::<32, 32, _, _>(B).sign_extend::<32>()))),

        // phadd[wd]
        expr!(less_than(bit_mask(C), add(select::<0, 16, _, _>(A).sign_extend::<16>(), select::<16, 16, _, _>(B).sign_extend::<16>()))),
        expr!(less_than(bit_mask(C), add(select::<0, 32, _, _>(A).sign_extend::<32>(), select::<32, 32, _, _>(B).sign_extend::<32>()))),

        // phsub[wd]
        expr!(less_than(bit_mask(C), sub(select::<0, 16, _, _>(A).sign_extend::<16>(), select::<16, 16, _, _>(B).sign_extend::<16>()))),
        expr!(less_than(bit_mask(C), sub(select::<0, 32, _, _>(A).sign_extend::<32>(), select::<32, 32, _, _>(B).sign_extend::<32>()))),
    ],

    [
        // Adjust flag for add/sub
        expr!(select::<4, 1, _, _>(add(A.crop::<4>(), add(B, C).crop::<4>()))),
        expr!(select::<4, 1, _, _>(add(A.crop::<4>(), sub(C, B).crop::<4>()))),

        // Carries for bits 8, 16, 32, 64
        expr!(select::<8, 1, _, _>(add(A.crop::<8>(), add(B.crop::<8>(), C)))),
        expr!(select::<8, 1, _, _>(add(A.crop::<8>(), sub(C, B).crop::<8>()))),

        expr!(select::<16, 1, _, _>(add(A.crop::<16>(), add(B.crop::<16>(), C)))),
        expr!(select::<16, 1, _, _>(add(A.crop::<16>(), sub(C, B).crop::<16>()))),

        expr!(select::<32, 1, _, _>(add(A.crop::<32>(), add(B.crop::<32>(), C)))),
        expr!(select::<32, 1, _, _>(add(A.crop::<32>(), sub(C, B).crop::<32>()))),

        expr!(select::<64, 1, _, _>(add(A.crop::<64>(), add(B.crop::<64>(), C)))),
        expr!(select::<64, 1, _, _>(add(A.crop::<64>(), sub(C, B).crop::<64>()))),

        // Carries for bits 7, 15, 31, 63 (needed for overflow flags)
        // static_expr!(select::<7, 1, _, _>(A.crop::<7>() + (B.crop::<7>() + C))),
        // static_expr!(select::<7, 1, _, _>(A.crop::<7>() + (C - B).crop::<7>())),

        // static_expr!(select::<15, 1, _, _>(A.crop::<15>() + (B.crop::<15>() + C))),
        // static_expr!(select::<15, 1, _, _>(A.crop::<15>() + (C - B).crop::<15>())),

        // static_expr!(select::<31, 1, _, _>(A.crop::<31>() + (B.crop::<31>() + C))),
        // static_expr!(select::<31, 1, _, _>(A.crop::<31>() + (C - B).crop::<31>())),

        // static_expr!(select::<63, 1, _, _>(A.crop::<63>() + (B.crop::<63>() + C))),
        // static_expr!(select::<63, 1, _, _>(A.crop::<63>() + (C - B).crop::<63>())),

        // TODO: Can we make it infer overflow from these components below: (!A | !B | R) & (A | B | !R)
        // static_expr!(select::<7, 1, _, _>(B) ^ select::<7, 1, _, _>(A + add(B, C))),
        // static_expr!(select::<15, 1, _, _>(B) ^ select::<15, 1, _, _>(A + add(B, C))),
        // static_expr!(select::<31, 1, _, _>(B) ^ select::<31, 1, _, _>(A + add(B, C))),
        // static_expr!(select::<63, 1, _, _>(B) ^ select::<63, 1, _, _, _>(A + add(B, C))),

        // static_expr!(select::<7, 1, _, _, _>(B) ^ select::<7, 1, _, _>(A + (C - B))),
        // static_expr!(select::<15, 1, _, _>(B) ^ select::<15, 1, _, _>(A + (C - B))),
        // static_expr!(select::<31, 1, _, _>(B) ^ select::<31, 1, _, _>(A + (C - B))),
        // static_expr!(select::<63, 1, _, _>(B) ^ select::<63, 1, _, _>(A + (C - B))),

        // Add OF
        // sign(A) != sign(B)
        expr!(select::<7, 1, _, _>(xor(A, B))),
        expr!(select::<15, 1, _, _>(xor(A, B))),
        expr!(select::<31, 1, _, _>(xor(A, B))),
        expr!(select::<63, 1, _, _>(xor(A, B))),

        // // sign(A) != sign(B + C + D)
        // expr!(select::<7, 1, _, _>(xor(A, add(B, add(C, D))))),
        // expr!(select::<15, 1, _, _>(xor(A, add(B, add(C, D))))),
        // expr!(select::<31, 1, _, _>(xor(A, add(B, add(C, D))))),
        // expr!(select::<63, 1, _, _>(xor(A, add(B, add(C, D))))),

        // sign(A) == sign(B) && sign(A) != sign(A + B + C)
        // TODO: We actually need sign(A) == sign(B) && (sign(A) != sign(A + B + 0) | sign(A) != sign(A + B + 1))
        expr!(select::<7, 1, _, _>(and(not(xor(A, B)), xor(A, add(A, add(B, C)))))),
        expr!(select::<15, 1, _, _>(and(not(xor(A, B)), xor(A, add(A, add(B, C)))))),
        expr!(select::<31, 1, _, _>(and(not(xor(A, B)), xor(A, add(A, add(B, C)))))),
        expr!(select::<63, 1, _, _>(and(not(xor(A, B)), xor(A, add(A, add(B, C)))))),

        expr!(is_zero(sub(add(A, add(B, C)), bit_mask(D)))),
        expr!(is_zero(sub(add(A, sub(B, C)), bit_mask(D)))),

        expr!(
            is_zero(sub(
                concat_bit(
                    select::<7, 1, _, _>(xor(A, B)),
                    concat_bit(
                        select::<7, 1, _, _>(xor(A, add(A, B))),
                        select::<7, 1, _, _>(xor(A, add(A, add(B, c::<1>())))),
                    )
                ),
                C
            ))
        ),

        expr!(
            is_zero(sub(
                concat_bit(
                    select::<15, 1, _, _>(xor(A, B)),
                    concat_bit(
                        select::<15, 1, _, _>(xor(A, add(A, B))),
                        select::<15, 1, _, _>(xor(A, add(A, add(B, c::<1>())))),
                    )
                ),
                C
            ))
        ),

        expr!(
            is_zero(sub(
                concat_bit(
                    select::<31, 1, _, _>(xor(A, B)),
                    concat_bit(
                        select::<31, 1, _, _>(xor(A, add(A, B))),
                        select::<31, 1, _, _>(xor(A, add(A, add(B, c::<1>())))),
                    )
                ),
                C
            ))
        ),

        expr!(
            is_zero(sub(
                concat_bit(
                    select::<63, 1, _, _>(xor(A, B)),
                    concat_bit(
                        select::<63, 1, _, _>(xor(A, add(A, B))),
                        select::<63, 1, _, _>(xor(A, add(A, add(B, c::<1>())))),
                    )
                ),
                C
            ))
        ),

        // Sub OF
        expr!(and(select::<7, 1, _, _>(xor(A, B)), not(xor(select::<7, 1, _, _>(B), select::<7, 1, _, _>(add(A, sub(C, B))))))),
        expr!(and(select::<15, 1, _, _>(xor(A, B)), not(xor(select::<15, 1, _, _>(B), select::<15, 1, _, _>(add(A, sub(C, B))))))),
        expr!(and(select::<31, 1, _, _>(xor(A, B)), not(xor(select::<31, 1, _, _>(B), select::<31, 1, _, _>(add(A, sub(C, B))))))),
        expr!(and(select::<63, 1, _, _>(xor(A, B)), not(xor(select::<63, 1, _, _>(B), select::<63, 1, _, _>(add(A, sub(C, B))))))),
    ],

    // Various
    generate_zf_sf_pf_from!(shr(mul(A, B), C)),
    [
        expr!(is_zero(shr(mul(A, B), C))),
        expr!(is_zero(not(shr(mul(A, B), C))))
    ],
    generate_zf_sf_pf_from!(shr(mul(A, B), C.crop::<3>())),
    generate_zf_sf_pf_from!(shr(mul(A, B), C.crop::<4>())),
    generate_zf_sf_pf_from!(shr(mul(A, B), C.crop::<5>())),
    generate_zf_sf_pf_from!(shr(mul(A, B), C.crop::<6>())),
    generate_zf_sf_pf_from!(div(A, B)),

    generate_zf_sf_pf_from!(or(A, shl(C, B.crop::<3>()))),
    generate_zf_sf_pf_from!(or(A, shl(C, B.crop::<4>()))),
    generate_zf_sf_pf_from!(or(A, shl(C, B.crop::<5>()))),
    generate_zf_sf_pf_from!(or(A, shl(C, B.crop::<6>()))),
    generate_zf_sf_pf_from!(or(A, shl(C, B))),

    // SHLD
    generate_zf_sf_pf_from!(or(shl(A, B), shr(shl(C, B), D))),

    // SHRD
    generate_zf_sf_pf_from!(shr(or(A, shl(B, shl(c::<1>(), D))), and(C, bit_mask(D)))),

    [
        // SHRD OF
        expr!(select::<15, 1, _, _>(xor(
            shr(or(A, shl(B, shl(c::<1>(), D))), and(C, bit_mask(D))),
            shr(or(A, shl(B, shl(c::<1>(), D))), and(sub(C, c::<1>()), bit_mask(D)))
        ))),
        expr!(select::<31, 1, _, _>(xor(
            shr(or(A, shl(B, shl(c::<1>(), D))), and(C, bit_mask(D))),
            shr(or(A, shl(B, shl(c::<1>(), D))), and(sub(C, c::<1>()), bit_mask(D)))
        ))),
        expr!(select::<63, 1, _, _>(xor(
            shr(or(A, shl(B, shl(c::<1>(), D))), and(C, bit_mask(D))),
            shr(or(A, shl(B, shl(c::<1>(), D))), and(sub(C, c::<1>()), bit_mask(D)))
        ))),

        // SHL CF
        expr!(select::<8, 1, _, _>(shl(A, B.crop::<3>()))),
        expr!(select::<16, 1, _, _>(shl(A, B.crop::<4>()))),
        expr!(select::<32, 1, _, _>(shl(A, B.crop::<5>()))),
        expr!(select::<64, 1, _, _>(shl(A, B.crop::<6>()))),

        // SHL OF (1)
        expr!(xor(select::<8, 1, _, _>(shl(A, B.crop::<3>())), select::<7, 1, _, _>(shl(A, B.crop::<3>())))),
        expr!(xor(select::<16, 1, _, _>(shl(A, B.crop::<4>())), select::<15, 1, _, _>(shl(A, B.crop::<4>())))),
        expr!(xor(select::<32, 1, _, _>(shl(A, B.crop::<5>())), select::<31, 1, _, _>(shl(A, B.crop::<5>())))),
        expr!(xor(select::<64, 1, _, _>(shl(A, B.crop::<6>())), select::<63, 1, _, _>(shl(A, B.crop::<6>())))),

        // SHL OF
        expr!(xor_top2! { 8, shl(A, B.crop::<3>()) }),
        expr!(xor_top2! { 8, shl(A, B.crop::<5>()) }),
        expr!(xor_top2! { 9, shl(A, B.crop::<3>()) }),
        expr!(xor_top2! { 9, shl(A, B.crop::<5>()) }),
        expr!(xor_top2! { 16, shl(A, B.crop::<4>()) }),
        expr!(xor_top2! { 16, shl(A, B.crop::<5>()) }),
        expr!(xor_top2! { 17, shl(A, B.crop::<4>()) }),
        expr!(xor_top2! { 17, shl(A, B.crop::<5>()) }),
        expr!(xor_top2! { 32, shl(A, B.crop::<5>()) }),
        expr!(xor_top2! { 33, shl(A, B.crop::<5>()) }),
        expr!(xor_top2! { 64, shl(A, B.crop::<6>()) }),
        expr!(xor_top2! { 65, shl(A, B.crop::<6>()) }),

        // ROL CF
        expr!(A.rol::<8, _, _>(B.crop::<3>())),
        expr!(A.rol::<16, _, _>(B.crop::<4>())),
        expr!(A.rol::<32, _, _>(B.crop::<5>())),
        expr!(A.rol::<64, _, _>(B.crop::<6>())),

        // ROL OF
        expr!(xor(A.rol::<8, _, _>(B.crop::<3>()) , select::<7, 1, _, _>(A.rol::<8, _, _>(B.crop::<3>()) ))),
        expr!(xor(A.rol::<16, _, _>(B.crop::<4>()), select::<15, 1, _, _>(A.rol::<16, _, _>(B.crop::<4>())))),
        expr!(xor(A.rol::<32, _, _>(B.crop::<5>()), select::<31, 1, _, _>(A.rol::<32, _, _>(B.crop::<5>())))),
        expr!(xor(A.rol::<64, _, _>(B.crop::<6>()), select::<63, 1, _, _>(A.rol::<64, _, _>(B.crop::<6>())))),

        // ROR OF
        expr!(xor_top2! { 8, A.rol::<8, _, _>(sub(c::<8>(), B.crop::<3>())) }),
        expr!(xor_top2! { 16, A.rol::<16, _, _>(sub(c::<16>(), B.crop::<4>())) }),
        expr!(xor_top2! { 32, A.rol::<32, _, _>(sub(c::<32>(), B.crop::<5>())) }),
        expr!(xor_top2! { 64, A.rol::<64, _, _>(sub(c::<64>(), B.crop::<6>())) }),

        expr!(or(xor_top2! { 8, A.rol::<8, _, _>(sub(c::<8>(), B.crop::<3>())) }, is_zero(B.crop::<3>()))),
        expr!(or(xor_top2! { 16, A.rol::<16, _, _>(sub(c::<16>(), B.crop::<4>())) }, is_zero(B.crop::<4>()))),
        expr!(or(xor_top2! { 32, A.rol::<32, _, _>(sub(c::<32>(), B.crop::<5>())) }, is_zero(B.crop::<5>()))),
        expr!(or(xor_top2! { 64, A.rol::<64, _, _>(sub(c::<64>(), B.crop::<6>())) }, is_zero(B.crop::<6>()))),

        expr!(or(not(xor_top2! { 8, A.rol::<8, _, _>(sub(c::<8>(), B.crop::<3>())) }), is_zero(B.crop::<3>()))),
        expr!(or(not(xor_top2! { 16, A.rol::<16, _, _>(sub(c::<16>(), B.crop::<4>())) }), is_zero(B.crop::<4>()))),
        expr!(or(not(xor_top2! { 32, A.rol::<32, _, _>(sub(c::<32>(), B.crop::<5>())) }), is_zero(B.crop::<5>()))),
        expr!(or(not(xor_top2! { 64, A.rol::<64, _, _>(sub(c::<64>(), B.crop::<6>())) }), is_zero(B.crop::<6>()))),

        // RCL CF
        expr!(select::<8, 1, _, _>(or(A, shl(B, c::<8>())).rol::<9, _, _>(and(C, bit_mask(D))))),
        expr!(select::<16, 1, _, _>(or(A, shl(B, c::<16>())).rol::<17, _, _>(and(C, bit_mask(D))))),
        expr!(select::<32, 1, _, _>(or(A, shl(B, c::<32>())).rol::<33, _, _>(and(C, bit_mask(D))))),
        expr!(select::<64, 1, _, _>(or(A, shl(B, c::<64>())).rol::<65, _, _>(and(C, bit_mask(D))))),

        // RCL OF
        expr!(xor_top2! { 9, or(A, shl(B, c::<8>())).rol::<9, _, _>(and(C, bit_mask(D))) }),
        expr!(xor_top2! { 17, select::<16, 1, _, _>(or(A, shl(B, c::<16>())).rol::<17, _, _>(and(C, bit_mask(D)))) }),
        expr!(xor_top2! { 33, select::<32, 1, _, _>(or(A, shl(B, c::<32>())).rol::<33, _, _>(and(C, bit_mask(D)))) }),
        expr!(xor_top2! { 65, select::<64, 1, _, _>(or(A, shl(B, c::<64>())).rol::<65, _, _>(and(C, bit_mask(D)))) }),

        expr!(or(xor_top2! { 9, or(A, shl(B, c::<8>())).rol::<9, _, _>(and(C, bit_mask(D))) }, is_zero(and(C, bit_mask(D))))),
        expr!(or(xor_top2! { 17, select::<16, 1, _, _>(or(A, shl(B, c::<16>())).rol::<17, _, _>(and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),
        expr!(or(xor_top2! { 33, select::<32, 1, _, _>(or(A, shl(B, c::<32>())).rol::<33, _, _>(and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),
        expr!(or(xor_top2! { 65, select::<64, 1, _, _>(or(A, shl(B, c::<64>())).rol::<65, _, _>(and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),

        expr!(or(not(xor_top2! { 9, or(A, shl(B, c::<8>())).rol::<9, _, _>(and(C, bit_mask(D))) }), is_zero(and(C, bit_mask(D))))),
        expr!(or(not(xor_top2! { 17, select::<16, 1, _, _>(or(A, shl(B, c::<16>())).rol::<17, _, _>(and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),
        expr!(or(not(xor_top2! { 33, select::<32, 1, _, _>(or(A, shl(B, c::<32>())).rol::<33, _, _>(and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),
        expr!(or(not(xor_top2! { 65, select::<64, 1, _, _>(or(A, shl(B, c::<64>())).rol::<65, _, _>(and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),

        // RCR CF
        expr!(select::<8, 1, _, _>(or(A, shl(B, c::<8>())).rol::<9, _, _>(sub(c::<{9 * 11}>(), and(C, bit_mask(D)))))),
        expr!(select::<16, 1, _, _>(or(A, shl(B, c::<16>())).rol::<17, _, _>(sub(c::<{17 * 7}>(), and(C, bit_mask(D)))))),
        expr!(select::<32, 1, _, _>(or(A, shl(B, c::<32>())).rol::<33, _, _>(sub(c::<{33 * 3}>(), and(C, bit_mask(D)))))),
        expr!(select::<64, 1, _, _>(or(A, shl(B, c::<64>())).rol::<65, _, _>(sub(c::<65>(), and(C, bit_mask(D)))))),

        // Condition for when old OF affects new OF in RCL/RCR
        expr!(is_zero(sub(A, urem(and(B, bit_mask(C)), c::<9>())))),
        expr!(is_zero(sub(A, urem(and(B, bit_mask(C)), c::<17>())))),
        expr!(is_zero(sub(A, urem(and(B, bit_mask(C)), c::<33>())))),
        expr!(is_zero(sub(A, urem(and(B, bit_mask(C)), c::<65>())))),

        // RCR OF
        expr!(or(not(xor_top2! { 8, or(A, shl(B, c::<8>())).rol::<9, _, _>(sub(c::<{9 * 11}>(), and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),
        expr!(or(not(xor_top2! { 16, or(A, shl(B, c::<16>())).rol::<17, _, _>(sub(c::<{17 * 7}>(), and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),
        expr!(or(not(xor_top2! { 32, or(A, shl(B, c::<32>())).rol::<33, _, _>(sub(c::<{33 * 3}>(), and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),
        expr!(or(not(xor_top2! { 64, or(A, shl(B, c::<64>())).rol::<65, _, _>(sub(c::<65>(), and(C, bit_mask(D)))) }), is_zero(and(C, bit_mask(D))))),

        expr!(or(xor_top2! { 8, or(A, shl(B, c::<8>())).rol::<9, _, _>(sub(c::<{9 * 11}>(), and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),
        expr!(or(xor_top2! { 16, or(A, shl(B, c::<16>())).rol::<17, _, _>(sub(c::<{17 * 7}>(), and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),
        expr!(or(xor_top2! { 32, or(A, shl(B, c::<32>())).rol::<33, _, _>(sub(c::<{33 * 3}>(), and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),
        expr!(or(xor_top2! { 64, or(A, shl(B, c::<64>())).rol::<65, _, _>(sub(c::<65>(), and(C, bit_mask(D)))) }, is_zero(and(C, bit_mask(D))))),
    ],

    generate_zf_sf_pf_from!(shr(A, B)),
    generate_zf_sf_pf_from!(shr(A, B.crop::<3>())),
    generate_zf_sf_pf_from!(shr(A, B.crop::<4>())),
    generate_zf_sf_pf_from!(shr(A, B.crop::<5>())),
    generate_zf_sf_pf_from!(shr(A, B.crop::<6>())),
    generate_zf_sf_pf_from!(and(shr(A, B), bit_mask(C))),

    [
        // Bit tests
        expr!(xor(shr(A, sub(B, C)), shr(A, add(sub(B, C), D)))),
        expr!(shr(A, B.crop::<3>())),
        expr!(shr(A, B.crop::<4>())),
        expr!(shr(A, B.crop::<5>())),
        expr!(shr(A, B.crop::<6>())),

        // bitmasks
        expr!(is_zero(and(A, shl(bit_mask(B), C)))),
        expr!(parity(and(A, bit_mask(B)))),
    ],

    generate_zf_sf_pf_from!(and(A, shl(B, C))),
    generate_zf_sf_pf_from!(and(A, shr(B, C))),
    generate_zf_sf_pf_from!(and(A, not(shl(B, C)))),

    [
        expr!(is_zero(and(A, shl(B, C)))),
        expr!(is_zero(and(A, shr(B, C)))),
        expr!(is_zero(and(A, not(shl(B, C))))),
    ],

    // To handle the case where a small imm value is sign-extended, where libLISA has a tendency to see different sign bits as different instructions
    generate_zf_sf_pf_from!(and(A, shl(or(B, shl(c::<1>(), c::<7>())).sign_extend::<8>(), C))),
    generate_zf_sf_pf_from!(and(A, shl(or(B, shl(c::<1>(), c::<8>())).sign_extend::<9>(), C))),

    generate_zf_sf_pf_from!(or(A, or(B, shl(C, D)))),
    generate_zf_sf_pf_from!(xor(A, shl(B, C))),
    generate_zf_sf_pf_from!(xor(and(A, bit_mask(B)), shr(C, D))),

    generate_zf_sf_pf_from!(add(A, mul(B, C))),
    generate_zf_sf_pf_from!(add(A, shl(B, C))),

    // saturation logic
    [
        expr!(less_than(add(A, B), shl(C, D))),
        expr!(less_than(add(A, B), sub(c::<0>(), shl(C, D)))),

        expr!(less_than(add(select::<0, 16, _, _>(A), select::<16, 16, _, _>(B)), shl(C, D))),
        expr!(less_than(add(select::<0, 32, _, _>(A), select::<32, 32, _, _>(B)), shl(C, D))),
        expr!(less_than(add(select::<0, 16, _, _>(A), select::<16, 16, _, _>(B)), sub(c::<0>(), shl(C, D)))),
        expr!(less_than(add(select::<0, 32, _, _>(A), select::<32, 32, _, _>(B)), sub(c::<0>(), shl(C, D)))),

        expr!(less_than(sub(select::<0, 16, _, _>(A), select::<16, 16, _, _>(B)), shl(C, D))),
        expr!(less_than(sub(select::<0, 32, _, _>(A), select::<32, 32, _, _>(B)), shl(C, D))),
        expr!(less_than(sub(select::<0, 16, _, _>(A), select::<16, 16, _, _>(B)), sub(c::<0>(), shl(C, D)))),
        expr!(less_than(sub(select::<0, 32, _, _>(A), select::<32, 32, _, _>(B)), sub(c::<0>(), shl(C, D)))),
    ],

    // bslmsk
    generate_zf_sf_pf_from!(bit_mask(add(A.trailing_zeros(), B))),

    // blsi
    generate_zf_sf_pf_from!(shl(A, add(B.trailing_zeros(), C))),

    // blsr
    generate_zf_sf_pf_from!(and(A, sub(B, C))),

    // betxr
    generate_zf_sf_pf_from!(and(shr(A, C.crop::<8>()), bit_mask(select::<8, 8, _, _>(B)))),

    [
        // Carry flag for shr/sar
        expr!(shr(A, sub(B.crop::<3>(), one()))),
        expr!(shr(A, sub(B.crop::<4>(), one()))),
        expr!(shr(A, sub(B.crop::<5>(), one()))),
        expr!(shr(A, sub(B.crop::<6>(), one()))),

        // Bytewise XOR
        expr!(and(
            and(
                is_zero(xor(A, select::<0, 8, _, _>(D))),
                is_zero(xor(B, select::<8, 8, _, _>(D))),
            ),
            is_zero(xor(C, select::<16, 8, _, _>(D))),
        )),
        expr!(or(
            or(
                not(is_zero(xor(A, select::<0, 8, _, _>(D)))),
                not(is_zero(xor(B, select::<8, 8, _, _>(D)))),
            ),
            not(is_zero(xor(C, select::<16, 8, _, _>(D)))),
        )),

        expr!(or(
            not(is_zero(sub(A.crop::<8>(), B.crop::<8>()))),
            not(is_zero(sub(C.crop::<8>(), D.crop::<8>()))),
        )),
        expr!(or(
            not(is_zero(sub(select::<8, 8, _, _>(A), B.crop::<8>()))),
            not(is_zero(sub(select::<8, 8, _, _>(C), D.crop::<8>()))),
        )),

        // Bytewise OR
        expr!(and(
            and(
                is_zero(A),
                is_zero(B),
            ),
            and(
                is_zero(C),
                is_zero(D),
            )
        )),

        // Comparisons with numbers spread accross multiple inputs (used in e.g. cmpxchg8b/cmpxchg16b)
        expr!(and(
            is_zero(xor(A, B).crop::<8>()),
            is_zero(xor(C, D).crop::<8>()),
        )),
        expr!(and(
            is_zero(xor(A, B).crop::<16>()),
            is_zero(xor(C, D).crop::<16>()),
        )),
        expr!(and(
            is_zero(xor(A, B).crop::<32>()),
            is_zero(xor(C, D).crop::<32>()),
        )),
        expr!(and(
            is_zero(xor(A, B).crop::<64>()),
            is_zero(xor(C, D).crop::<64>()),
        )),
        expr!(is_zero(xor(
            or(A, shl(B, C)),
            D
        ))),


        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.sign_extend::<8>(), B.sign_extend::<8>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.sign_extend::<8>(), B.sign_extend::<8>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.sign_extend::<16>(), B.sign_extend::<16>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.sign_extend::<16>(), B.sign_extend::<16>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.sign_extend::<32>(), B.sign_extend::<32>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.sign_extend::<32>(), B.sign_extend::<32>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.sign_extend::<64>(), B.sign_extend::<64>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.sign_extend::<64>(), B.sign_extend::<64>())
            )
        )),


        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.crop::<8>(), B.crop::<8>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.crop::<8>(), B.crop::<8>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.crop::<16>(), B.crop::<16>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.crop::<16>(), B.crop::<16>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.crop::<32>(), B.crop::<32>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.crop::<32>(), B.crop::<32>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.crop::<64>(), B.crop::<64>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.crop::<64>(), B.crop::<64>())
            )
        )),


        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.sign_extend::<8>(), B.crop::<8>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.sign_extend::<8>(), B.crop::<8>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.sign_extend::<16>(), B.crop::<16>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.sign_extend::<16>(), B.crop::<16>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.sign_extend::<32>(), B.crop::<32>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.sign_extend::<32>(), B.crop::<32>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.sign_extend::<64>(), B.crop::<64>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.sign_extend::<64>(), B.crop::<64>())
            )
        )),


        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.crop::<8>(), B.sign_extend::<8>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<8>()), shr(B, c::<8>())),
                mul(A.crop::<8>(), B.sign_extend::<8>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.crop::<16>(), B.sign_extend::<16>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<16>()), shr(B, c::<16>())),
                mul(A.crop::<16>(), B.sign_extend::<16>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.crop::<32>(), B.sign_extend::<32>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<32>()), shr(B, c::<32>())),
                mul(A.crop::<32>(), B.sign_extend::<32>())
            )
        )),

        expr!(less_than(
            bit_mask(C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.crop::<64>(), B.sign_extend::<64>())
            )
        )),
        expr!(less_than(
            shl(c::<-1>(), C),
            add(
                mul(shr(A, c::<64>()), shr(B, c::<64>())),
                mul(A.crop::<64>(), B.sign_extend::<64>())
            )
        )),

        expr!(less_than(
            bit_mask(B),
            A
        )),
        expr!(less_than(
            shl(c::<-1>(), B),
            A
        )),
    ],
};

lazy_static::lazy_static! {
    pub static ref EXPR_TEMPLATES: Vec<PreprocessedTemplate<'static>> = templates!(128, INTERNAL_EXPR_TEMPLATES);
    pub static ref SIMPLE_BOOLEAN_TEMPLATES: Vec<PreprocessedTemplate<'static>> = templates!(1, INTERNAL_SIMPLE_BOOLEAN_TEMPLATES);
}
