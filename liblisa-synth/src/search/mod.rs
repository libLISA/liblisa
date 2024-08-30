use std::fmt::{Debug, Display};
use std::marker::PhantomData;

use arrayvec::ArrayVec;
use liblisa::semantics::default::computation::{
    Arg, ArgEncoding, CompareResult, ComputationRef, ExprComputation, ExpressionComputation, OutputEncoding, PreparedComparison,
};
use liblisa::semantics::default::MAX_TEMPLATE_ARGS;
use liblisa::semantics::{Computation, IoType, OutputType, ARG_NAMES};
use liblisa::utils::bitmask_u64;
use liblisa::value::{AsValue, OwnedValue};

use crate::templates::preprocess::PreprocessedTemplate;
use crate::templates::{AnyTemplate, CONST_VALUES};

pub mod exprsearcher;
pub mod searcher;
pub mod termsearcher;

#[derive(Copy, Clone)]
pub struct IterItemComputation<'a, 'e, 'r> {
    template_iterator: &'a TemplateIterator<'e, PreprocessedTemplate<'e>>,
    computation_enumerator: &'a ComputationEnumerator<'r>,
}

impl<'a> IterItemComputation<'a, '_, '_> {
    pub fn arg_indexes(&self) -> &[u16] {
        &self.template_iterator.counter
    }

    fn all_args(&self) -> &[Arg] {
        &self.computation_enumerator.args
    }

    fn expr_computation(&self, output_encoding: OutputEncoding) -> ExprComputation<'a> {
        ExprComputation::new(
            *self.template_iterator.template.expr(),
            output_encoding,
            self.computation_enumerator.output_type,
        )
    }

    pub fn to_template_computation(&self, output_encoding: OutputEncoding) -> ExpressionComputation {
        self.with_internal_computation(output_encoding, |c| c.to_expression_computation())
    }

    pub fn with_internal_computation<T>(&self, output_encoding: OutputEncoding, f: impl FnOnce(ComputationRef) -> T) -> T {
        let arg_interpretation = self
            .arg_indexes()
            .iter()
            .map(|index| self.all_args()[*index as usize])
            .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
        let comp = ComputationRef {
            template: self.expr_computation(output_encoding),
            consts: &[],
            arg_interpretation: &arg_interpretation,
        };

        f(comp)
    }

    /// Expressions are iterated in ascending order.
    /// An expression with a big endian output encoding is always guaranteed to be smaller (<) than an expression with little-endian output encoding.
    pub fn compress(&self, output_encoding: OutputEncoding) -> CompressedIterComputation {
        debug_assert_eq!(self.arg_indexes().len(), self.template_iterator.template.num_total_holes());

        CompressedIterComputation::create(
            self.computation_enumerator.index - 1,
            self.computation_enumerator.num_bits_for_template_index,
            self.computation_enumerator.template_index_offset,
            self.arg_indexes(),
            self.computation_enumerator.num_bits_for_arg_index,
            output_encoding,
        )
    }

    pub fn prepared_compare_eq_with_args_indirect(&self, all_args: &[i128], expected: &PreparedComparison) -> CompareResult {
        let mapping = self.arg_indexes();
        let result = self.template_iterator.template.expr().evaluate_indirect(all_args, mapping);

        expected.compare_dual(self.computation_enumerator.internal_output_type, result)
    }

    pub fn evaluate_as_bool_with_args(&self, all_args: &[i128]) -> bool {
        self.expr_computation(OutputEncoding::UnsignedBigEndian)
            .evaluate_as_bool_with_args_indirect(all_args, self.arg_indexes())
    }
}

impl Debug for IterItemComputation<'_, '_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with_internal_computation(OutputEncoding::UnsignedBigEndian, |c| Debug::fmt(&c, f))
    }
}

impl Display for IterItemComputation<'_, '_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with_internal_computation(OutputEncoding::UnsignedBigEndian, |c| Display::fmt(&c.display(ARG_NAMES), f))
    }
}

/// Generally we build expressions with:
///     - 1-5 holes
///     - <1000 templates
///     - <128 arguments (30 + 4n where n is number of inputs; Number of inputs is usually <= 16)
///
/// This means that for any fixed set of input types, output type, etc. we generate only a limited number of unique outputs:
///     128**5*1000 = 34359738368000 =~ 45 bits
///
/// We can therefore describe every expression in just a single u64, and gain huge memory benefits.
///
/// This struct is that compressed form representation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CompressedIterComputation(u64);

fn num_bits_in(n: usize) -> u32 {
    64 - n.leading_zeros()
}

impl CompressedIterComputation {
    /// A CompressedIterComputation which is guaranteed `MIN <= c` for all CompressedIterComputation `c`.
    pub const MIN: CompressedIterComputation = CompressedIterComputation::from_u64(0);

    /// A CompressedIterComputation which is guaranteed `MAX >= c` for all CompressedIterComputation `c`.
    pub const MAX: CompressedIterComputation = CompressedIterComputation::from_u64(u64::MAX);

    fn create(
        template_index: usize, _num_bits_in_template_index: u32, template_index_offset: u32, arg_indices: &[u16],
        num_bits_for_arg_index: u32, output_encoding: OutputEncoding,
    ) -> CompressedIterComputation {
        let mut n = 0u64;
        for index in arg_indices.iter().rev() {
            let index = u8::try_from(*index).unwrap() as u64;
            n = (n << num_bits_for_arg_index) | index;
        }

        n <<= 1;
        n |= match output_encoding {
            OutputEncoding::UnsignedBigEndian => 0,
            OutputEncoding::UnsignedLittleEndian => 1,
        };

        n |= (template_index as u64) << template_index_offset;

        CompressedIterComputation(n)
    }

    pub fn decompress<'r, 'a>(&self, enumerator: &'r ComputationEnumerator<'a>) -> UncompressedIterComputation<'r, 'a> {
        let n = self.0;
        let templates = &enumerator.templates;
        let num_templates = templates.len();
        assert!(num_templates > 0);

        let offset = enumerator.template_index_offset;
        let template_index = (n >> offset) as usize;

        let template = &templates[template_index];

        UncompressedIterComputation {
            template,
            enumerator,
            data: n,
        }
    }

    #[inline(always)]
    pub fn with_extra_data(self) -> CompressedIterComputationWithExtraData<Nil> {
        CompressedIterComputationWithExtraData(self.0, PhantomData)
    }

    pub fn as_u64(self) -> u64 {
        self.0
    }

    pub const fn from_u64(n: u64) -> CompressedIterComputation {
        CompressedIterComputation(n)
    }
}

pub trait ExtraDataSpec: Copy + Clone + Debug {}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Cons<const MIN: u64, const MAX: u64, Next: ExtraDataSpec>(PhantomData<fn() -> Next>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Nil;

impl<const MIN: u64, const MAX: u64, Next: ExtraDataSpec> Cons<MIN, MAX, Next> {
    const fn num() -> u64 {
        MAX - MIN + 1
    }
}

impl<const MIN: u64, const MAX: u64, Next: ExtraDataSpec> ExtraDataSpec for Cons<MIN, MAX, Next> {}
impl ExtraDataSpec for Nil {}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CompressedIterComputationWithExtraData<ExtraDataSpec>(u64, PhantomData<ExtraDataSpec>);

impl<E: ExtraDataSpec> CompressedIterComputationWithExtraData<E> {
    /// A CompressedIterComputationWithExtraData<E> which is guaranteed `MIN <= c` for all CompressedIterComputationWithExtraData<E> `c`.
    pub const MIN: Self = Self::from_u64(0);

    /// A CompressedIterComputationWithExtraData<E> which is guaranteed `MAX >= c` for all CompressedIterComputationWithExtraData<E> `c`.
    pub const MAX: Self = Self::from_u64(u64::MAX);

    pub fn as_u64(self) -> u64 {
        self.0
    }

    pub const fn from_u64(value: u64) -> Self {
        Self(value, PhantomData)
    }

    #[inline(always)]
    pub fn add_value<const MIN: u64, const MAX: u64>(
        self, value: u64,
    ) -> CompressedIterComputationWithExtraData<Cons<MIN, MAX, E>> {
        let n = self.0 * Cons::<MIN, MAX, E>::num() + (value - MIN);
        CompressedIterComputationWithExtraData(n, PhantomData)
    }
}

impl<const MIN: u64, const MAX: u64, const X: u64, const Y: u64, E: ExtraDataSpec>
    CompressedIterComputationWithExtraData<Cons<MIN, MAX, Cons<X, Y, E>>>
{
    #[inline(always)]
    pub fn pop_value(self) -> (CompressedIterComputationWithExtraData<Cons<X, Y, E>>, u64) {
        let val = self.0 % Cons::<MIN, MAX, E>::num();
        let n = self.0 / Cons::<MIN, MAX, E>::num();

        (CompressedIterComputationWithExtraData(n, PhantomData), val)
    }
}

impl<const MIN: u64, const MAX: u64> CompressedIterComputationWithExtraData<Cons<MIN, MAX, Nil>> {
    #[inline(always)]
    pub fn pop_value(self) -> (CompressedIterComputation, u64) {
        let val = self.0 % Cons::<MIN, MAX, Nil>::num();
        let n = self.0 / Cons::<MIN, MAX, Nil>::num();

        (CompressedIterComputation(n), val)
    }
}

#[derive(Clone)]
pub struct UncompressedIterComputation<'r, 'a> {
    template: &'a PreprocessedTemplate<'a>,
    enumerator: &'r ComputationEnumerator<'a>,
    data: u64,
}

impl Debug for UncompressedIterComputation<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UncompressedIterComputation")
            .field("template", self.template.expr())
            .field("data", &self.data)
            .finish()
    }
}

impl<'a> UncompressedIterComputation<'_, 'a> {
    pub fn arg_indexes(&self) -> impl Iterator<Item = usize> + '_ {
        let shift = self.enumerator.num_bits_for_arg_index;
        let mask = bitmask_u64(shift);
        let mut n = self.data >> 1;
        (0..self.template.num_total_holes()).map(move |_| {
            let index = u8::try_from(n & mask).unwrap();
            n >>= shift;

            index as usize
        })
    }

    pub fn output_encoding(&self) -> OutputEncoding {
        match self.data % 2 {
            0 => OutputEncoding::UnsignedBigEndian,
            1 => OutputEncoding::UnsignedLittleEndian,
            _ => unreachable!(),
        }
    }

    pub fn template(&self) -> ExprComputation<'a> {
        ExprComputation::new(*self.template.expr(), self.output_encoding(), self.enumerator.output_type)
    }

    pub fn to_template_computation(&self) -> ExpressionComputation {
        self.with_internal_computation(|c| c.to_expression_computation())
    }

    pub fn with_internal_computation<T>(&self, f: impl FnOnce(ComputationRef) -> T) -> T {
        let arg_interpretation = self
            .arg_indexes()
            .map(|index| self.enumerator.args[index])
            .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
        let comp = ComputationRef {
            template: self.template(),
            consts: &[],
            arg_interpretation: &arg_interpretation,
        };

        f(comp)
    }

    pub fn prepared_compare_eq_with_args_indirect(&self, all_args: &[i128], expected: &PreparedComparison) -> bool {
        let mapping = self
            .arg_indexes()
            .map(|x| x as u16)
            .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();
        let result = self.template.expr().evaluate_indirect(all_args, &mapping);

        let result = expected.compare_dual(self.enumerator.internal_output_type, result);
        match self.output_encoding() {
            OutputEncoding::UnsignedLittleEndian => result.little_endian,
            OutputEncoding::UnsignedBigEndian => result.big_endian,
        }
    }

    fn all_args(&self) -> &[Arg] {
        &self.enumerator.args
    }
}

#[derive(Debug)]
struct DisplayUIC<'r, 'a, 'uic> {
    item: &'uic UncompressedIterComputation<'r, 'a>,
    args: Vec<String>,
}

impl<'r, 'a> Computation for UncompressedIterComputation<'r, 'a> {
    fn evaluate<V: AsValue>(&self, inputs: &[V]) -> OwnedValue {
        let args = self
            .arg_indexes()
            .map(|arg_index| self.all_args()[arg_index].interpret_inputs(inputs, &[]))
            .collect::<ArrayVec<_, MAX_TEMPLATE_ARGS>>();

        self.template().evaluate_with_args(&args[..])
    }

    fn display<'v, S: AsRef<str>>(&'v self, input_names: &'v [S]) -> impl Display + Debug + 'v {
        DisplayUIC {
            item: self,
            args: input_names.iter().map(|s| s.as_ref().to_string()).collect(),
        }
    }

    fn used_input_indices(&self) -> Vec<usize> {
        self.with_internal_computation(|c| c.used_input_indices())
    }

    fn remap_inputs(&mut self, _map: &[Option<usize>]) {
        panic!("Unable to remap inputs on TemplateEnumerationItem")
    }

    fn is_identity(&self) -> bool {
        self.with_internal_computation(|c| c.is_identity())
    }
}

impl Display for DisplayUIC<'_, '_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.item
            .with_internal_computation(|c| Display::fmt(&c.display(&self.args), f))
    }
}

type Counter = ArrayVec<u16, MAX_TEMPLATE_ARGS>;

pub struct TemplateIterator<'e, T: AnyTemplate + 'e> {
    template: &'e T,

    /// Which args we select from the full argument list
    counter: Counter,
}

impl<'e, T: AnyTemplate + 'e> Clone for TemplateIterator<'e, T> {
    fn clone(&self) -> Self {
        Self {
            template: self.template,
            counter: self.counter.clone(),
        }
    }
}

impl<'e, T: AnyTemplate + 'e> TemplateIterator<'e, T> {
    pub fn new(template: &'e T) -> Self {
        let counter = template.new_counter();
        debug_assert_eq!(counter.len(), template.num_total_holes());

        Self {
            template,
            counter,
        }
    }

    /// Returns true if the counter has overflowed past the end of the possible values.
    fn increment_counter(&mut self, num_args: usize) -> bool {
        for index in self.template.active_indices() {
            let reset_value = self.template.ordering_indexes()[index]
                .map(|index| self.counter[index])
                .unwrap_or(num_args as u16 - 1);
            let n = &mut self.counter[index];

            *n += 1;
            if *n > reset_value {
                *n = self.template.start_value() as u16;

                debug_assert!(
                    *n <= reset_value,
                    "Reset value of {reset_value:?} is smaller than start value {} of template {:?}",
                    self.template.start_value(),
                    self.template
                );
            } else {
                return false;
            }
        }

        true
    }

    pub fn next(&mut self, num_args: usize) -> bool {
        !self.increment_counter(num_args)
    }

    pub fn arg_indices(&self) -> &[u16] {
        &self.counter
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterpretedArgs {
    data: Vec<i128>,
}

impl InterpretedArgs {
    pub fn from_arg_list<V: AsValue>(all_args: &[Arg], inputs: &[V]) -> Self {
        InterpretedArgs {
            data: all_args.iter().map(|arg| arg.interpret_inputs(inputs, &[])).collect(),
        }
    }

    pub fn instantiate<const N: usize, T: Copy>(&self, arg_indices: impl Iterator<Item = T>, args: &mut [i128; N])
    where
        usize: From<T>,
    {
        for (arg_value, arg_index) in args.iter_mut().zip(arg_indices) {
            *arg_value = self.data[usize::from(arg_index)];
        }
    }

    pub fn as_slice(&self) -> &[i128] {
        &self.data
    }
}

#[derive(Clone)]
pub struct ComputationEnumerator<'a> {
    args: Vec<Arg>,
    output_type: IoType,
    internal_output_type: OutputType,
    templates: &'a [PreprocessedTemplate<'a>],
    index: usize,
    inner: Option<TemplateIterator<'a, PreprocessedTemplate<'a>>>,
    num_bits_for_template_index: u32,
    num_bits_for_arg_index: u32,
    template_index_offset: u32,
}

impl<'a> ComputationEnumerator<'a> {
    fn generate_args_encodings(input_types: &[IoType]) -> Vec<Arg> {
        let mut args = Vec::new();

        args.extend(CONST_VALUES.iter().map(|&v| Arg::TinyConst(v.try_into().unwrap())));

        for (index, input) in input_types.iter().enumerate() {
            if input.num_bits() > 8 {
                args.push(Arg::Input {
                    index: index.try_into().unwrap(),
                    encoding: ArgEncoding::SignedLittleEndian,
                    num_bits: input.num_bits().try_into().unwrap(),
                });
                args.push(Arg::Input {
                    index: index.try_into().unwrap(),
                    encoding: ArgEncoding::UnsignedLittleEndian,
                    num_bits: input.num_bits().try_into().unwrap(),
                });
            }

            args.push(Arg::Input {
                index: index.try_into().unwrap(),
                encoding: ArgEncoding::SignedBigEndian,
                num_bits: input.num_bits().try_into().unwrap(),
            });
            args.push(Arg::Input {
                index: index.try_into().unwrap(),
                encoding: ArgEncoding::UnsignedBigEndian,
                num_bits: input.num_bits().try_into().unwrap(),
            });
        }

        args
    }

    pub fn new(templates: &'a [PreprocessedTemplate<'a>], input_types: &[IoType], output_type: IoType) -> Self {
        let args = Self::generate_args_encodings(input_types);
        let num_bits_for_arg_index = num_bits_in(args.len());
        ComputationEnumerator {
            args,
            output_type,
            internal_output_type: From::from(output_type),
            templates,
            index: 0,
            inner: None,
            num_bits_for_template_index: num_bits_in(templates.len()),
            num_bits_for_arg_index,
            template_index_offset: num_bits_for_arg_index * MAX_TEMPLATE_ARGS as u32 + 1,
        }
    }

    pub fn current(&self) -> IterItemComputation<'_, '_, '_> {
        IterItemComputation {
            template_iterator: self.inner.as_ref().expect("Cannot call current() when enumeration is done"),
            computation_enumerator: self,
        }
    }

    /// Enumerates expressions one-by-one.
    /// Will continue to yield None after the first None when complete.
    pub fn find_next(&mut self) -> Option<IterItemComputation<'_, '_, '_>> {
        loop {
            if self.inner.is_some() {
                if self.inner.as_mut().unwrap().next(self.args.len()) {
                    return Some(self.current());
                } else {
                    self.inner = None;
                }
            } else {
                while let Some(next_template) = self.templates.get(self.index) {
                    self.inner = Some(TemplateIterator::new(next_template));
                    self.index += 1;

                    if next_template.num_unfilled_holes() == 0 || self.args.len() > CONST_VALUES.len() {
                        return Some(self.current());
                    }
                }

                return None;
            }
        }
    }

    pub fn templates_remaining(&self) -> usize {
        self.templates.len() - self.index
    }

    pub fn is_empty(&self) -> bool {
        self.templates_remaining() == 0
    }

    pub fn prepare_interpreted_args<V: AsValue>(&self, inputs: &[V]) -> InterpretedArgs {
        InterpretedArgs::from_arg_list(&self.args, inputs)
    }

    pub fn nth(&mut self, position: usize) -> Option<IterItemComputation<'_, '_, '_>> {
        self.skip(position);

        self.find_next()
    }

    pub fn skip(&mut self, num: usize) {
        for _ in 0..num {
            self.find_next();
        }
    }

    pub fn args(&self) -> &[Arg] {
        self.args.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use liblisa::semantics::default::computation::OutputEncoding;
    use liblisa::semantics::IoType;

    use super::{CompressedIterComputation, ComputationEnumerator};
    use crate::templates::SIMPLE_BOOLEAN_TEMPLATES;

    #[test]
    pub fn decompress_consistent() {
        let mut enumerator = ComputationEnumerator::new(
            &SIMPLE_BOOLEAN_TEMPLATES,
            &[
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 8,
                },
                IoType::Integer {
                    num_bits: 1,
                },
            ],
            IoType::Integer {
                num_bits: 1,
            },
        );
        let mut n = 0usize;

        while enumerator.find_next().is_some() {
            n += 1;
            if n % 100_000 == 0 {
                println!("Processed: {n}");
            }

            let e = enumerator.current();
            for endianness in [OutputEncoding::UnsignedBigEndian, OutputEncoding::UnsignedLittleEndian] {
                let compressed = e.compress(endianness);
                let decompressed = compressed.decompress(&enumerator);

                assert!(
                    e.arg_indexes()
                        .iter()
                        .map(|&index| index as usize)
                        .zip(decompressed.arg_indexes())
                        .all(|(a, b)| a == b),
                    "Arg indices must stay the same: before: {:?} vs decompressed: {:?}",
                    e.arg_indexes(),
                    decompressed.arg_indexes().format(", ")
                );
                assert_eq!(
                    e.expr_computation(endianness).output_encoding(),
                    decompressed.output_encoding(),
                    "Output encoding must stay the same"
                );
                assert_eq!(
                    e.expr_computation(endianness).expr().ops(),
                    decompressed.template().expr().ops(),
                    "Actual: {:?}, compressed={:?}, decompressed={:?}",
                    e.expr_computation(endianness),
                    compressed,
                    decompressed
                );

                let compressed = e.compress(endianness);
                let compressed = compressed.with_extra_data().add_value::<0, 1>(1);
                let (decompressed, _) = compressed.pop_value();
                let decompressed = decompressed.decompress(&enumerator);

                assert!(
                    e.arg_indexes()
                        .iter()
                        .map(|&index| index as usize)
                        .zip(decompressed.arg_indexes())
                        .all(|(a, b)| a == b),
                    "Arg indices must stay the same: before: {:?} vs decompressed: {:?}",
                    e.arg_indexes(),
                    decompressed.arg_indexes().format(", ")
                );
                assert_eq!(
                    e.expr_computation(endianness).output_encoding(),
                    decompressed.output_encoding(),
                    "Output encoding must stay the same"
                );
                assert_eq!(
                    e.expr_computation(endianness).expr().ops(),
                    decompressed.template().expr().ops(),
                    "Actual: {:?}, compressed={:?}, decompressed={:?}",
                    e.expr_computation(endianness),
                    compressed,
                    decompressed
                );
            }
        }
    }
    #[test]
    pub fn compress_is_increasing() {
        let mut enumerator = ComputationEnumerator::new(
            &SIMPLE_BOOLEAN_TEMPLATES,
            &[
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 64,
                },
                IoType::Integer {
                    num_bits: 8,
                },
                IoType::Integer {
                    num_bits: 1,
                },
            ],
            IoType::Integer {
                num_bits: 1,
            },
        );
        let mut n = 0usize;
        let mut last = CompressedIterComputation::MIN;
        let mut first = true;
        while enumerator.find_next().is_some() {
            n += 1;
            if n % 100_000 == 0 {
                println!("Processed: {n}");
            }

            let e = enumerator.current();
            let compressed_be = e.compress(OutputEncoding::UnsignedBigEndian);
            let compressed_le = e.compress(OutputEncoding::UnsignedLittleEndian);
            if !first {
                assert!(
                    compressed_be > last,
                    "Compressed: {:X}; Last: {:X}",
                    compressed_be.as_u64(),
                    last.as_u64()
                );
            }
            assert!(
                compressed_le > compressed_be,
                "Compressed LE: {:X}; Compressed BE: {:X}",
                compressed_le.as_u64(),
                compressed_be.as_u64()
            );

            last = compressed_le;
            first = false;
        }
    }
}
