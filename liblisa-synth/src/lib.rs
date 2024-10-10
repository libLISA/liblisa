#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(generic_arg_infer)]
#![feature(let_chains)]
#![doc(html_no_source)]

//! This library contains the default synthesis implementation for libLISA.
//! It can be invoked as follows (for x64):
//!
//! ```
//! # fn wrap(encoding: liblisa::encoding::Encoding<liblisa::arch::x64::X64Arch, ()>) {
//! // let encoding = ...; // see the `liblisa-enc` crate
//! let semantics = liblisa_x64_observer::with_oracle(|mut oracle| {
//!     liblisa_synth::synthesize_semantics(encoding, &mut oracle)
//! });
//!
//! println!("{semantics}");
//! # }
//! ```

use std::fmt::Debug;
use std::iter::{once, repeat};
use std::time::{Duration, Instant};

use fxhash::FxHashMap;
use liblisa::arch::Arch;
use liblisa::encoding::{Encoding, WriteOrdering};
use liblisa::oracle::Oracle;
#[doc(hidden)]
pub use liblisa::semantics::default as __private_exprs;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::semantics::{Computation, IoType};
use liblisa::state::random::{randomized_bytes, randomized_value};
use liblisa::value::{AsValue, OwnedValue, Value};
use log::{info, trace};
use rand::Rng;
use serde::{Deserialize, Serialize};

mod cond;
mod gen;
mod normalizer;
mod output;
mod predicate;

// only public for benchmarks.
#[doc(hidden)]
pub mod search;

mod synthesis_loop;
mod templates;
mod tree;
mod utils;
mod write_order;

pub use output::Output;
pub use synthesis_loop::SynthesisLoop;
use templates::{EXPR_TEMPLATES, SIMPLE_BOOLEAN_TEMPLATES};
pub use tree::synthesizer::DefaultTreeTemplateSynthesizer;
pub use write_order::determine_overlapping_write_order;

/// The result of synthesis.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SynthesisResult<C> {
    /// The index of the dataflow output in the [`Encoding`].
    pub output_index: usize,

    /// The synthesized semantics.
    /// `None` if synthesis failed or timed out.
    pub computation: Option<C>,
}

/// Prepares the templates needed for synthesis.
/// If this function is not called, templates are prepared the first time synthesis is run.
/// This may cause the first synthesis attempt to time out.
pub fn prepare_templates() {
    let _ = &*EXPR_TEMPLATES;
    let _ = &*SIMPLE_BOOLEAN_TEMPLATES;
}

/// Synthesizes semantics for an [`Encoding`].
pub fn synthesize_semantics<A: Arch, O: Oracle<A>>(
    encoding: Encoding<A, ()>, oracle: &mut O,
) -> Encoding<A, SynthesizedComputation> {
    let mut rng = rand::thread_rng();

    info!("Encoding:");
    info!("{encoding}");

    prepare_templates();

    // Never spend more than 15 minutes on synthesis
    let timeout = Some(Duration::from_secs(15 * 60));
    let (computations, write_ordering) =
        synthesize_outputs::<_, DefaultTreeTemplateSynthesizer, _, _>(&mut rng, oracle, &encoding, timeout);

    info!("Computations: {:?}", computations);

    let encoding = encoding.map_computations(|_, _| None);
    let mut semantics = merge_semantics_into_encoding(encoding, computations);
    info!("Semantics: {}", semantics);
    semantics.write_ordering = write_ordering;

    // Since we only input a single encoding, `semantics` will always contain a single encoding.
    semantics
}

/// Synthesizes semantics for all outputs in the provided [`Encoding`].
pub fn synthesize_outputs<A: Arch, S: Synthesizer<OwnedValue>, O: Oracle<A>, R: Rng>(
    rng: &mut R, oracle: &mut O, encoding: &Encoding<A, ()>, timeout: Option<Duration>,
) -> (Vec<SynthesisResult<S::Computation>>, Vec<WriteOrdering>)
where
    S::Hypothesis: Computation,
    S::Computation: Computation,
{
    let outputs = Output::extract_from_encoding(encoding);

    if outputs.iter().any(|o| {
        o.input_types()
            .iter()
            .copied()
            .chain(once(o.output_type()))
            .any(|t| t.num_bits() > 128)
    }) {
        // Inputs of >128 bits not supported
        return (
            outputs
                .iter()
                .map(|output| SynthesisResult {
                    output_index: output.output_index,
                    computation: None,
                })
                .collect(),
            Vec::new(),
        );
    }

    let mut synthesis_loop = SynthesisLoop::<A, S>::new(encoding, outputs, timeout);
    let result = synthesis_loop.run(oracle, rng);

    let write_order = determine_overlapping_write_order(rng, oracle, encoding, &result);

    (result, write_order)
}

/// Merges the [`SynthesisResult`]s returned by the [`SynthesisLoop`] into an [`Encoding`].
pub fn merge_semantics_into_encoding<A: Arch, C: Computation>(
    mut encoding: Encoding<A, C>, computations: Vec<SynthesisResult<C>>,
) -> Encoding<A, C> {
    for output_index in encoding
        .dataflows
        .output_dataflows()
        .enumerate()
        .filter(|(_, o)| o.computation.is_none())
        .map(|(index, _)| index)
        .collect::<Vec<_>>()
    {
        if let Some(computation) = computations
            .iter()
            .find(|g| g.output_index == output_index)
            .and_then(|c| c.computation.clone())
        {
            encoding.set_computation(output_index, computation);
        }
    }

    let encoding = encoding.remove_unused_inputs();
    encoding.remove_identity_assignments()
}

/// A type that returns the output of a dataflow, given its inputs.
///
/// Internally, the requester will instantiate the [`Encoding`], perform a CPU observation, and extract the output value from the resulting CPU state.
pub trait Requester<Output: SynthesizerOutput> {
    fn request<V: AsValue>(&mut self, inputs: &[V]) -> Option<Output>;
    fn request_debug<V: AsValue>(&mut self, inputs: &[V]) -> Option<Output> {
        self.request(inputs)
    }
}

pub(crate) struct CachedRequester<I: Requester<OwnedValue>> {
    cache: FxHashMap<Vec<OwnedValue>, Option<OwnedValue>>,
    inner: I,
}

impl<I: Requester<OwnedValue>> CachedRequester<I> {
    pub fn new(inner: I) -> Self {
        Self {
            cache: Default::default(),
            inner,
        }
    }
}

impl<I: Requester<OwnedValue>> Requester<OwnedValue> for CachedRequester<I> {
    fn request<V: AsValue>(&mut self, inputs: &[V]) -> Option<OwnedValue> {
        let inputs = inputs.as_owned();
        if let Some(entry) = self.cache.get(&inputs) {
            entry.clone()
        } else {
            let result = self.inner.request(&inputs);
            self.cache.insert(inputs, result.clone());

            result
        }
    }

    fn request_debug<V: AsValue>(&mut self, inputs: &[V]) -> Option<OwnedValue> {
        self.inner.request_debug(inputs)
    }
}

/// The output values used for synthesis.
/// These are usually [`Value`]s or [`OwnedValue`]s.
pub trait SynthesizerOutput {
    type Borrowed<'o>: Copy
    where
        Self: 'o;

    fn borrow(&self) -> Self::Borrowed<'_>;
}

impl SynthesizerOutput for OwnedValue {
    type Borrowed<'o> = Value<'o>;

    fn borrow(&self) -> Self::Borrowed<'_> {
        self.as_value()
    }
}

impl SynthesizerOutput for bool {
    type Borrowed<'o> = bool;

    fn borrow(&self) -> Self::Borrowed<'_> {
        *self
    }
}

impl SynthesizerOutput for Value<'_> {
    type Borrowed<'o>
        = Value<'o>
    where
        Self: 'o;

    fn borrow(&self) -> Self::Borrowed<'_> {
        *self
    }
}

/// A semantics synthesizer.
pub trait SynthesizerBase {
    type Hypothesis;
    type Computation;

    fn new(input_types: &[IoType], output_type: IoType) -> Self;
    fn hypothesis(&self) -> Option<&Self::Hypothesis>;
    fn has_given_up(&self) -> bool;

    fn needs_requester(&self) -> bool;
    fn needs_requester_for_consistency(&self) -> bool {
        false
    }

    fn set_timeout(&mut self, _stop_at: Instant) {}
    fn into_computation(self) -> Option<Self::Computation>;
}

/// A semantics synthesizer.
/// Generic over input and output types.
pub trait Synthesizer<Output: SynthesizerOutput = bool>: SynthesizerBase {
    fn add_case<V: AsValue>(&mut self, inputs: &[V], output: Output);

    fn is_consistent<V: AsValue>(&self, inputs: &[V], output: Output::Borrowed<'_>) -> bool;

    fn add_case_with_requests<V: AsValue>(&mut self, inputs: &[V], output: Output, _requester: &mut impl Requester<Output>)
    where
        Self: Sized,
    {
        self.add_case(inputs, output);
    }

    fn is_consistent_with_requests<V: AsValue>(
        &self, inputs: &[V], output: Output::Borrowed<'_>, _requester: &mut impl Requester<Output>,
    ) -> bool {
        self.is_consistent(inputs, output)
    }
}

struct FnRequester<'a, O: SynthesizerOutput + 'a>(&'a mut dyn for<'r> FnMut(&'r [Value<'_>]) -> Option<O>);

impl<Output: SynthesizerOutput> Requester<Output> for FnRequester<'_, Output> {
    fn request<V: AsValue>(&mut self, inputs: &[V]) -> Option<Output> {
        let inputs = inputs.as_values();
        (self.0)(&inputs)
    }

    fn request_debug<V: AsValue>(&mut self, inputs: &[V]) -> Option<Output> {
        let inputs = inputs.as_values();
        (self.0)(&inputs)
    }
}

/// A simple synthesizer that synthesizes a computation from a function.
pub fn synthesize_from_fn<O: SynthesizerOutput + Debug + Clone, S: Synthesizer<O>>(
    rng: &mut impl Rng, mut synthesizer: S, input_types: &[IoType], mut f: impl for<'r> FnMut(&'r [Value]) -> Option<O>,
) -> Option<S::Computation>
where
    S::Hypothesis: Debug,
    S::Computation: Debug,
{
    let mut num_ok = 0;
    let mut num_failed = 0;
    let mut num_tried = 0;

    info!("Starting synthesis...");
    while !synthesizer.has_given_up() && num_ok < 5_000_000 {
        num_tried += 1;

        let inputs = if rng.gen() {
            let base = randomized_value(rng);
            input_types.iter().map(|ty| randomize_ty_from(ty, base)).collect::<Vec<_>>()
        } else {
            input_types.iter().map(|ty| randomize_ty(ty, rng)).collect::<Vec<_>>()
        };

        let inputs = inputs.iter().map(AsValue::as_value).collect::<Vec<_>>();
        let inputs = &inputs[..];

        if let Some(real_output) = f(inputs) {
            let ok = synthesizer.is_consistent(inputs, real_output.borrow());
            if !ok {
                info!("Adding case: {:X?} => {:X?}", inputs, real_output);

                synthesizer.add_case_with_requests(inputs, real_output.clone(), &mut FnRequester(&mut |inputs| f(inputs)));

                num_ok = 0;
            } else {
                num_ok += 1;
            }
        } else {
            trace!("Unable to observe {:?}", inputs);
            num_failed += 1;

            if num_failed >= num_tried * 9 / 10 && num_tried >= 5000 {
                return None;
            }
        }

        if num_tried >= 100_000_000 {
            break
        }
    }

    let has_given_up = synthesizer.has_given_up();
    let result = synthesizer.into_computation();
    info!(
        "Synthesized with num_oks={}, has_given_up={}: {:?}",
        num_ok, has_given_up, result
    );

    if has_given_up || num_ok < 100_000 {
        return None;
    }

    result
}

fn randomize_ty<R: Rng>(ty: &IoType, rng: &mut R) -> OwnedValue {
    match ty {
        IoType::Integer {
            num_bits,
        } => OwnedValue::Num(randomized_value(rng) & (((1u128 << num_bits) - 1) as u64)),
        IoType::Bytes {
            num_bytes,
        } => OwnedValue::Bytes(randomized_bytes(rng, *num_bytes)),
    }
}

fn randomize_ty_from(ty: &IoType, val: u64) -> OwnedValue {
    match ty {
        IoType::Integer {
            num_bits,
        } => OwnedValue::Num(val & (((1u128 << num_bits) - 1) as u64)),
        IoType::Bytes {
            num_bytes,
        } => OwnedValue::Bytes(repeat(val.to_le_bytes()).flatten().take(*num_bytes).collect()),
    }
}

pub(crate) trait InputSlice {
    fn as_values(&self) -> Vec<Value<'_>>;
    fn as_owned(&self) -> Vec<OwnedValue>;
}

impl<V: AsValue> InputSlice for [V] {
    fn as_values(&self) -> Vec<Value<'_>> {
        self.iter().map(AsValue::as_value).collect()
    }

    fn as_owned(&self) -> Vec<OwnedValue> {
        self.iter().map(AsValue::to_owned_value).collect()
    }
}
