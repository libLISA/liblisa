use std::marker::PhantomData;

use liblisa::arch::Arch;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa_enc::infer_encoding;

use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Infer an encoding for a single instruction
pub struct InferEncodingCommand<A> {
    /// The instruction to analyze.
    instr: Instruction,

    #[clap(long)]
    /// When enabled, the JSON representation of the encoding is printed to stdout.
    print_json: bool,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch> SimpleCommand<A> for InferEncodingCommand<A> {
    type Setup = ();

    fn setup(&self, _oracle: &mut impl Oracle<A>) -> Self::Setup {}

    fn run(&self, oracle: &mut impl Oracle<A>, _: &mut Self::Setup) {
        let instr = self.instr;
        let mut encoding = infer_encoding::<A, _>(&instr, oracle).unwrap();
        println!("Encoding: {encoding}");

        if self.print_json {
            let json = serde_json::to_string(&encoding).unwrap();
            println!("Json = {json}");
        }

        encoding.split_flag_output();
        println!("Split flags encoding: {encoding}");

        println!("Filters: {:?}", encoding.filters());
    }
}
