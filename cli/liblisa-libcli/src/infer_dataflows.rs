use std::marker::PhantomData;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{Dataflows, MemoryAccesses};
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa_enc::{DataflowAnalysis, MemoryAccessAnalysis};
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Infer dataflows for a single instruction
pub struct InferDataflowsCommand<A> {
    /// The instruction to analyze.
    instr: Instruction,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for InferDataflowsCommand<A> {
    type Setup = (MemoryAccesses<A>, Option<Dataflows<A, ()>>);

    fn setup(&self, oracle: &mut impl Oracle<A>) -> Self::Setup {
        let instr = self.instr;

        let accesses = MemoryAccessAnalysis::infer::<A, _>(oracle, &instr).unwrap();
        println!("Accesses ({}): {:#?}", accesses.len(), accesses);

        (accesses, None)
    }

    fn run(&self, oracle: &mut impl Oracle<A>, (accesses, prev): &mut Self::Setup) {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());

        let dataflows = DataflowAnalysis::infer(&mut rng, oracle, accesses);
        if dataflows.is_err() || prev.as_ref() != dataflows.as_ref().ok() {
            println!("Dataflows: {dataflows:#?}");
        } else {
            println!("    ( Identical )");
        }

        *prev = dataflows.ok();
    }
}
