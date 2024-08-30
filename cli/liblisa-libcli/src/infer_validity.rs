use std::marker::PhantomData;

use liblisa::arch::Arch;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa_enc::Validity;

use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Check the validity of a single instruction
pub struct InferValidityCommand<A> {
    /// The instruction to analyze.
    instr: Instruction,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for InferValidityCommand<A> {
    type Setup = ();

    fn setup(&self, _oracle: &mut impl Oracle<A>) -> Self::Setup {}

    fn run(&self, oracle: &mut impl Oracle<A>, _: &mut Self::Setup) {
        let validity = Validity::infer::<A, _>(oracle, &self.instr);
        println!("Validity: {validity:#?}");
    }
}
