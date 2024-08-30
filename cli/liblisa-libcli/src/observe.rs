use std::marker::PhantomData;

use liblisa::arch::Arch;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::state::SystemState;

use crate::{SimpleCommand, StateSpecArgs};

#[derive(Clone, Debug, clap::Parser)]
/// Observe the CPU state after execution of an instruction
pub struct ObserveCommand<A> {
    /// The instruction to analyze.
    instr: Instruction,

    #[clap(flatten)]
    state_spec: StateSpecArgs,

    #[clap(long = "careful")]
    /// When enabled, observation will call observe_carefully(..) instead of observe(..).
    careful: bool,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for ObserveCommand<A> {
    type Setup = ();

    fn setup(&self, _oracle: &mut impl Oracle<A>) -> Self::Setup {}

    fn run(&self, oracle: &mut impl Oracle<A>, _: &mut Self::Setup) {
        println!("Mappable area: {:X?}", oracle.mappable_area());
        let default_pc = oracle.random_mappable_page(&mut rand::thread_rng()).start_addr();
        let state: SystemState<A> = self.state_spec.create_state(self.instr, default_pc.as_u64());

        println!("Input {state:X?}");

        let output = if self.careful {
            oracle.observe_carefully(&state)
        } else {
            oracle.observe(&state)
        };
        println!("Output {output:X?}");
    }
}
