use std::marker::PhantomData;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{Dataflows, MemoryAccesses};
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::state::random::StateGen;
use liblisa_enc::cache::CombinedCache;
use liblisa_enc::{ChangeAnalysis, DataflowAnalysis, MemoryAccessAnalysis, ThresholdValues};
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Detect changes between two individual instructions.
pub struct DetectChangesCommand<A> {
    /// The left-hand side instruction
    lhs: Instruction,

    /// The right-hand side instruction
    rhs: Instruction,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for DetectChangesCommand<A> {
    type Setup = (MemoryAccesses<A>, Dataflows<A, ()>);

    fn setup(&self, oracle: &mut impl Oracle<A>) -> Self::Setup {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let instr = self.lhs;
        let accesses = MemoryAccessAnalysis::infer::<A, _>(oracle, &instr).unwrap();
        println!("Accesses ({}): {:#?}", accesses.len(), accesses);

        let dataflows = DataflowAnalysis::infer(&mut rng, oracle, &accesses).unwrap();
        println!("Dataflows: {dataflows:#?}");

        (accesses, dataflows)
    }

    fn run(&self, oracle: &mut impl Oracle<A>, (accesses, dataflows): &mut Self::Setup) {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let cache = CombinedCache::default();
        let mappable = Oracle::<A>::mappable_area(oracle);
        let state_gen = StateGen::new(accesses, &mappable).unwrap();
        let threshold_values = ThresholdValues::infer(oracle, &mut rng, &state_gen, dataflows);
        let change = ChangeAnalysis {
            cache: &cache,
            dataflows,
            state_gen: StateGen::new(&dataflows.addresses, &mappable).unwrap(),
            o: oracle,
            use_trap_flag: &mut false,
            threshold_values: &threshold_values,
            found_dependent_bytes: &mut false,
        }
        .detect_change(&mut rng, &self.rhs)
        .unwrap();

        println!("Change: {change:?}");
    }
}
