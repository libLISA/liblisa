use std::collections::HashSet;
use std::fmt;
use std::marker::PhantomData;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use liblisa::arch::Arch;
use liblisa::encoding::{Encoding, WriteOrdering};
use liblisa::oracle::Oracle;
use liblisa::semantics::{Computation, ARG_NAMES};
use liblisa::value::OwnedValue;
use liblisa_synth::{synthesize_outputs, SynthesisResult, Synthesizer};
use rand::seq::SliceRandom;
use rand::Rng;
use serde::{Deserialize, Serialize};

use crate::threadpool::work::Work;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Synthesis<'a, S> {
    #[serde(default)]
    pub remaining_entries: Vec<usize>,
    pub runtime_ms: u128,
    pub total_ms: u128,
    pub encodings_path: PathBuf,

    // We can't create a type alias for this, because that will change the trait bounds on Serialize & Deserialize
    #[allow(clippy::type_complexity)]
    _phantom: PhantomData<(&'a (), fn() -> S)>,
}

pub struct SynthesisRuntimeData<'a, A: Arch> {
    pub last_check: Instant,
    pub encodings: &'a [Encoding<A, ()>],
    pub pending: Vec<usize>,
    pub second_chances: HashSet<usize>,
}

pub struct AnalysisRequest<'a, A: Arch> {
    at: Instant,
    encoding_index: usize,
    encoding: &'a Encoding<A, ()>,
}

impl<A: Arch> std::fmt::Debug for AnalysisRequest<'_, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AnalysisRequest")
            .field("at", &self.at)
            .field("index", &self.encoding_index)
            .finish()
    }
}

impl<A: Arch> AnalysisRequest<'_, A> {
    pub fn synthesize<S: Synthesizer<OwnedValue>, O: Oracle<A>, R: Rng>(
        &self, oracle: &mut O, rng: &mut R,
    ) -> (Vec<SynthesisResult<S::Computation>>, Vec<WriteOrdering>)
    where
        S::Hypothesis: Computation,
        S::Computation: Computation,
    {
        synthesize_outputs::<A, S, O, R>(rng, oracle, self.encoding, Some(Duration::from_secs(900)))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SynthesisArtifact<C: Computation> {
    pub ms_taken: u128,
    pub encoding_index: usize,
    pub computations: Vec<SynthesisResult<C>>,
    pub write_ordering: Vec<WriteOrdering>,
}

impl<'a, A: Arch, S: Synthesizer<OwnedValue>> Work<A, ()> for Synthesis<'a, S>
where
    S::Hypothesis: Computation,
    S::Computation: Computation,
{
    type RuntimeData = SynthesisRuntimeData<'a, A>;
    type Request = AnalysisRequest<'a, A>;
    type Result = (Vec<SynthesisResult<S::Computation>>, Vec<WriteOrdering>);
    type Artifact = SynthesisArtifact<S::Computation>;

    fn next(&mut self, data: &mut Self::RuntimeData) -> Option<Self::Request> {
        let next_entry = self.remaining_entries.iter().find(|e| !data.pending.contains(e));

        next_entry.and_then(|&encoding_index| {
            data.encodings.get(encoding_index).map(|encoding| {
                let request = AnalysisRequest {
                    at: Instant::now(),
                    encoding_index,
                    encoding,
                };

                data.pending.push(encoding_index);

                request
            })
        })
    }

    fn complete(
        &mut self, data: &mut Self::RuntimeData, request: Self::Request, (result, write_ordering): Self::Result,
    ) -> Option<Self::Artifact> {
        let ms_step = data.last_check.elapsed().as_millis();
        self.runtime_ms += ms_step;
        data.last_check = Instant::now();

        let ms_taken = request.at.elapsed().as_millis();
        self.total_ms += ms_taken;

        println!(
            "Received analysis for {:X} index={} in {}s:",
            request.encoding.instr(),
            request.encoding_index,
            request.at.elapsed().as_secs()
        );
        for result in result.iter() {
            println!(
                "    Output #{}: {}",
                result.output_index,
                result
                    .computation
                    .as_ref()
                    .map(|c| c.display(ARG_NAMES).to_string())
                    .unwrap_or_else(|| String::from("<failed>"))
            );
        }

        data.pending
            .remove(data.pending.iter().position(|&item| item == request.encoding_index).unwrap());

        // Only remove from remaining entries if synthesis was successful or if we have tried to synthesize twice already.
        if result.iter().all(|r| r.computation.is_some()) || !data.second_chances.insert(request.encoding_index) {
            self.remaining_entries.remove(
                self.remaining_entries
                    .iter()
                    .position(|&item| item == request.encoding_index)
                    .unwrap(),
            );
        }

        Some(SynthesisArtifact {
            ms_taken,
            encoding_index: request.encoding_index,
            computations: result,
            write_ordering,
        })
    }

    fn run<O: Oracle<A>>(oracle: &mut O, _cache: &(), request: &Self::Request) -> Self::Result {
        println!("Synthesizing {}", request.encoding);
        request.synthesize::<S, _, _>(oracle, &mut rand::thread_rng())
    }
}

impl<C> Synthesis<'_, C> {
    pub fn create(encodings_path: PathBuf, num_encodings: usize) -> Self {
        let mut remaining_entries = (0..num_encodings).collect::<Vec<_>>();
        remaining_entries.shuffle(&mut rand::thread_rng());

        Synthesis {
            runtime_ms: 0,
            total_ms: 0,
            remaining_entries,
            encodings_path,
            _phantom: PhantomData,
        }
    }
}
