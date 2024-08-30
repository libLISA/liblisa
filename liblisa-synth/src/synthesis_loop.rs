use std::collections::HashSet;
use std::time::{Duration, Instant};

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::Dataflows;
use liblisa::encoding::Encoding;
use liblisa::oracle::{MappableArea, Observation, Oracle};
use liblisa::semantics::{Computation, InputValues, ARG_NAMES};
use liblisa::state::SystemState;
use liblisa::utils::Timeout;
use liblisa::value::{AsValue, OwnedValue, Value};
use log::{debug, info, trace};
use rand::seq::SliceRandom;
use rand::Rng;

use crate::gen::{TestCase, TestCaseGen};
use crate::output::{OracleRequester, Output};
use crate::{CachedRequester, SynthesisResult, Synthesizer};

const NUM_OK_NEEDED: usize = 5_000_000;

struct SynthesisItem<'a, A: Arch, S> {
    output: Output<'a, A>,
    synthesizer: S,
    num_ok: usize,
    num_nok: usize,
    num_instances_ok: usize,
    interesting_inputs: Vec<InputValues>,
    ms_taken: u128,
}

struct MissingOracle;

#[derive(Copy, Clone, Debug)]
struct MissingMappableArea;

impl MappableArea for MissingMappableArea {
    fn can_map(&self, _addr: liblisa::state::Addr) -> bool {
        unimplemented!()
    }
}

impl<A: Arch> Oracle<A> for MissingOracle {
    type MappableArea = MissingMappableArea;

    fn mappable_area(&self) -> Self::MappableArea {
        unimplemented!()
    }
    fn page_size(&mut self) -> u64 {
        unimplemented!()
    }
    fn observe(&mut self, _before: &SystemState<A>) -> Result<SystemState<A>, liblisa::oracle::OracleError> {
        unimplemented!()
    }
    fn batch_observe_iter<'a, S: liblisa::state::AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, _states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        unimplemented!();

        #[allow(unreachable_code)] // needed for type inference
        [].into_iter()
    }
    fn batch_observe_gpreg_only_iter<'a, S: liblisa::state::AsSystemState<A> + 'a, I: IntoIterator<Item = S> + 'a>(
        &'a mut self, _states: I,
    ) -> impl Iterator<Item = Observation<S, A>> {
        unimplemented!();

        #[allow(unreachable_code)] // needed for type inference
        [].into_iter()
    }
    fn scan_memory_accesses(
        &mut self, _before: &SystemState<A>,
    ) -> Result<Vec<liblisa::state::Addr>, liblisa::oracle::OracleError> {
        unimplemented!()
    }
    fn debug_dump(&mut self) {
        unimplemented!()
    }
    fn restart(&mut self) {
        unimplemented!()
    }
    fn kill(self) {
        unimplemented!()
    }

    const UNRELIABLE_INSTRUCTION_FETCH_ERRORS: bool = false;
}

impl<A: Arch, S: Synthesizer<OwnedValue>> SynthesisItem<'_, A, S>
where
    S::Hypothesis: Computation,
{
    /// Returns true if case is inconsistent.
    fn check(&mut self, inputs: &[Value], output: Value, oracle: Option<&mut impl Oracle<A>>) -> Option<bool> {
        let consistent = if self.synthesizer.needs_requester_for_consistency() {
            if let Some(oracle) = oracle {
                self.synthesizer.is_consistent_with_requests(
                    inputs.as_ref(),
                    output,
                    &mut CachedRequester::new(OracleRequester {
                        output: &mut self.output,
                        oracle,
                    }),
                )
            } else {
                return None
            }
        } else {
            self.synthesizer.is_consistent(inputs.as_ref(), output)
        };

        Some(if consistent {
            self.num_nok = 0;
            self.num_ok += 1;
            if self.num_ok < 1000 || self.num_ok % 10_000 == 0 {
                info!("num_ok={:?}", self.num_ok);
            }

            if self.num_ok == 1000 {
                if let Some(computation) = self.synthesizer.hypothesis() {
                    info!("Probably OK with {}: {:?}", computation.display(ARG_NAMES), self.output);
                }
            }

            true
        } else {
            if self.num_nok < 3 {
                debug!("Not consistent (check): {inputs:?} => {output:?}");
            }

            self.num_nok += 1;
            self.num_ok = 0;
            self.num_instances_ok = 0;

            false
        })
    }

    /// Returns false if the case could not be added because it needs a requester.
    fn check_and_add_if_possible(
        &mut self, instance: &Dataflows<A, ()>, state_in: &TestCase<A>, state_out: &SystemState<A>,
    ) -> bool {
        let (inputs, output) = self
            .output
            .extract_io(instance, &state_in.state, &state_in.part_values, state_out);

        let c = self.check(&inputs, output, Option::<&mut MissingOracle>::None);
        if !c.unwrap_or(false) {
            if self.synthesizer.needs_requester() {
                return false;
            } else {
                if self.synthesizer.hypothesis().is_some() {
                    self.interesting_inputs.push(InputValues::from(&inputs[..]));
                    info!("Interesting inputs: {}", self.interesting_inputs.len());
                }

                let s = Instant::now();
                let output = output.to_owned_value();
                self.synthesizer.add_case(inputs.as_ref(), output);
                self.ms_taken += s.elapsed().as_millis();
            }
        }

        true
    }

    fn check_and_add_with_requester(
        &mut self, instance: &Dataflows<A, ()>, state_in: &TestCase<A>, state_out: &SystemState<A>, oracle: &mut impl Oracle<A>,
    ) {
        let (inputs, output) = self
            .output
            .extract_io(instance, &state_in.state, &state_in.part_values, state_out);

        let c = self.check(&inputs, output, Some(oracle));
        let consistent = c.unwrap();

        if self.synthesizer.needs_requester_for_consistency() && consistent {
            self.num_nok = 0;
            self.num_ok += 1;
            if self.num_ok < 1000 || self.num_ok % 10_000 == 0 {
                info!("num_ok={:?}", self.num_ok);
            }

            if self.num_ok == 1000 {
                if let Some(computation) = self.synthesizer.hypothesis() {
                    info!("Probably OK with {}: {:?}", computation.display(ARG_NAMES), self.output);
                }
            }
        }

        if !consistent {
            if self.num_nok < 3 {
                debug!(
                    "Not consistent (check_and_add_with_requester): State IN:\n{state_in:?}\nState OUT:\n{output:?}\nI/O pair: {inputs:X?} => {output:X?}"
                );
            }

            self.num_nok += 1;
            self.num_ok = 0;
            self.num_instances_ok = 0;

            if self.synthesizer.hypothesis().is_some() {
                self.interesting_inputs.push(InputValues::from(&inputs[..]));
                info!("Interesting inputs: {}", self.interesting_inputs.len());
            }

            let s = Instant::now();
            let output = output.to_owned_value();
            self.synthesizer.add_case_with_requests(
                &inputs,
                output,
                &mut CachedRequester::new(OracleRequester {
                    output: &mut self.output,
                    oracle,
                }),
            );
            self.ms_taken += s.elapsed().as_millis();
        }
    }
}

/// A CEGIS synthesis loop.
pub struct SynthesisLoop<'a, A: Arch, S> {
    encoding: &'a Encoding<A, ()>,
    synthesizers: Vec<SynthesisItem<'a, A, S>>,
    timeout: Option<Duration>,
    timeout_at: Timeout,
}

impl<'a, A: Arch, S: Synthesizer<OwnedValue>> SynthesisLoop<'a, A, S>
where
    S::Hypothesis: Computation,
{
    pub fn gen_testcases(&self, rng: &mut impl Rng) -> Option<TestCaseGen<A>> {
        let output_indices = self.synthesizers.iter().map(|s| s.output.output_index).collect::<Vec<_>>();
        let mut result = TestCaseGen::new_raw(self.encoding, &output_indices, rng)?;

        let mut outputs = HashSet::new();
        let duplicate_outputs = result
            .instance()
            .output_dataflows()
            .any(|f| !outputs.insert(&f.target) || outputs.iter().any(|&o| o.overlaps(&f.target) && o != &f.target));

        if duplicate_outputs {
            info!(
                "This instance has multiple outputs mapped to the same destination; Skipping: {}",
                result.instance()
            );
            return None
        }

        for output in self.synthesizers.iter() {
            for item in output.interesting_inputs.choose_multiple(rng, 100) {
                result.add_interesting_input(output.output.output_index, item.clone());
            }
        }

        Some(result)
    }

    pub fn new(encoding: &'a Encoding<A, ()>, outputs: Vec<Output<'a, A>>, timeout: Option<Duration>) -> Self {
        Self {
            encoding,
            synthesizers: outputs
                .into_iter()
                .map(|output| {
                    info!(
                        "Creating synthesizer for {:?} -> {:?} of {:X?}",
                        output.input_types(),
                        output.output_type(),
                        output
                    );

                    SynthesisItem {
                        synthesizer: S::new(&output.input_types(), output.output_type()),
                        output,
                        num_ok: 0,
                        num_nok: 0,
                        num_instances_ok: 0,
                        interesting_inputs: Vec::new(),
                        ms_taken: 0,
                    }
                })
                .collect::<Vec<_>>(),
            timeout,
            timeout_at: Timeout::default(),
        }
    }

    pub fn run(&mut self, oracle: &mut impl Oracle<A>, rng: &mut impl Rng) -> Vec<SynthesisResult<S::Computation>> {
        crate::prepare_templates();

        let mappable_area = oracle.mappable_area();
        let mut num_observed = 0;

        let start = Instant::now();

        if let Some(timeout) = self.timeout {
            self.timeout_at.set_timeout_at(start + timeout);
            for synth in self.synthesizers.iter_mut() {
                synth.synthesizer.set_timeout(start + timeout);
            }
        }

        let mut post_check_states = vec![Vec::new(); self.synthesizers.len()];
        let mut k = 0;
        loop {
            k += 1;

            if self.timeout_at.is_timed_out() {
                break
            }

            info!("k={k:?}");

            let gen = self.gen_testcases(rng);
            let gen = gen.as_ref().and_then(|gen| gen.with_mappable_area(&mappable_area, rng));

            if let Some(gen) = gen {
                let mut num = 0;
                for (state_in, state_out) in oracle.batch_observe_iter(gen.iter(rng, 1000)) {
                    num += 1;
                    if self.timeout_at.is_timed_out() {
                        break
                    }

                    if let Ok(state_out) = state_out {
                        num_observed += 1;
                        for (synthesizer_index, item) in self.synthesizers.iter_mut().enumerate() {
                            if self.timeout_at.is_timed_out() {
                                break
                            }

                            if item.synthesizer.has_given_up() {
                                continue;
                            }

                            if !item.check_and_add_if_possible(gen.instance(), &state_in, &state_out) {
                                trace!(
                                    "Queueing case for output #{} (total queued: {})",
                                    item.output.output_index,
                                    post_check_states.len()
                                );
                                post_check_states[synthesizer_index].push((state_in.clone(), state_out.clone()));
                            }
                        }
                    } else {
                        trace!("State failed: {state_in:X?} => {state_out:X?}");
                    }

                    if post_check_states.iter().any(|v| v.len() > 1000) {
                        break
                    }
                }

                debug!("Post-checking states: {}", post_check_states.len());

                for (synthesizer_index, states) in post_check_states.iter_mut().enumerate() {
                    let synthesizer = &mut self.synthesizers[synthesizer_index];
                    for (state_in, state_out) in states.drain(..) {
                        if self.timeout_at.is_timed_out() {
                            break
                        }

                        if synthesizer.synthesizer.has_given_up() {
                            break;
                        }

                        synthesizer.check_and_add_with_requester(gen.instance(), &state_in, &state_out, oracle);
                    }
                }

                for synth in self.synthesizers.iter_mut() {
                    if synth.num_ok > 0 {
                        synth.num_instances_ok += 1;
                    }
                }

                info!("Checked {num} states, num_ok: {num_observed}");
            }

            if k > 1000 && num_observed <= k * 10 {
                break;
            }

            if self
                .synthesizers
                .iter()
                .all(|item| item.num_ok >= NUM_OK_NEEDED || item.synthesizer.has_given_up())
            {
                break;
            }
        }

        for item in self.synthesizers.iter() {
            info!("Synthesizer for {:?} took {}ms", item.output, item.ms_taken);
        }

        self.synthesizers
            .drain(..)
            .enumerate()
            .map(|(index, item)| SynthesisResult {
                output_index: item.output.output_index,
                computation: if item.num_ok >= NUM_OK_NEEDED {
                    item.synthesizer.into_computation()
                } else {
                    if item.synthesizer.has_given_up() {
                        info!("Output #{index} not synthesized because synthesizer gave up");
                    } else if item.num_ok > 100_000 {
                        info!("Output #{index} not synthesized because of early timeout");
                    }
                    None
                },
            })
            .collect()
    }
}
