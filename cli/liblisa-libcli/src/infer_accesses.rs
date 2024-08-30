use std::marker::PhantomData;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::MemoryAccesses;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa_enc::MemoryAccessAnalysis;

use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Infer memory accesses for a single instruction
pub struct InferAccessesCommand<A> {
    /// The instruction to analyze.
    instr: Instruction,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for InferAccessesCommand<A> {
    type Setup = Option<MemoryAccesses<A>>;

    fn setup(&self, _oracle: &mut impl Oracle<A>) -> Self::Setup {
        None
    }

    fn run(&self, oracle: &mut impl Oracle<A>, prev: &mut Self::Setup) {
        let instr = self.instr;
        let accesses = MemoryAccessAnalysis::infer::<A, _>(oracle, &instr);
        if accesses.is_err() || prev.as_ref() != accesses.as_ref().ok() {
            println!(
                "Accesses ({}): {accesses:#?}",
                accesses.as_ref().map(|m| m.len()).unwrap_or(0)
            );
        } else {
            println!("    ( Identical )");
        }

        *prev = accesses.ok();
    }
}
