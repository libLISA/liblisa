use std::collections::HashSet;
use std::marker::PhantomData;

use liblisa::arch::{Arch, FullScope};
use liblisa::instr::{FilterList, Instruction};
use liblisa::oracle::Oracle;
use liblisa_enc::cache::CombinedCache;

use crate::threadpool::enumeration::{AnalysisRequest, EnumWorkItem, EnumerationArtifactData};
use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Run enumeration between two specified instructions, without saving results
pub struct QuickEnumerateCommand<A> {
    /// The starting point of the enumeration.
    instr: Instruction,

    #[clap(long)]
    /// An optional upper bound for the enumeration.
    to: Option<Instruction>,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for QuickEnumerateCommand<A> {
    type Setup = ();

    fn setup(&self, _oracle: &mut impl Oracle<A>) -> Self::Setup {}

    fn run(&self, oracle: &mut impl Oracle<A>, _: &mut Self::Setup) {
        let mut worker = EnumWorkItem::new(&self.instr, self.to);

        let cache = CombinedCache::<A, _, _, _>::default();
        let mut filters = FilterList::new();
        let mut perfect_instrs_seen = HashSet::new();
        while let Some(counter) = worker.next_instruction() {
            let instr = counter.current();
            let request = AnalysisRequest::new(0, counter, filters.next_matching_instruction(&instr), FullScope);
            println!("Next: ({instr:X}) {request:?}");
            let result = request.run(0, oracle, &cache);
            for filter in result.filters() {
                filters.add(filter);
            }

            if let Some(artifact) = worker.complete(instr, &filters, &mut perfect_instrs_seen, result) {
                match artifact {
                    EnumerationArtifactData::Encoding(encoding) => {
                        println!("{encoding}");

                        let json = serde_json::to_string(&encoding).unwrap();
                        println!("Json = {json}");
                    },
                    EnumerationArtifactData::Failed(instr) => println!("FAILED: {instr:?}"),
                    EnumerationArtifactData::Excluded(instr) => println!("Excluded: {instr:?}"),
                    EnumerationArtifactData::InvalidInstructions(range) => {
                        println!("Invalid instructions between {:X} and {:X}", range.start, range.end)
                    },
                    EnumerationArtifactData::MemoryErrorInstructions(range) => {
                        println!("Bad memory accesses between {:X} and {:X}", range.start, range.end)
                    },
                }
            }
        }
    }
}
