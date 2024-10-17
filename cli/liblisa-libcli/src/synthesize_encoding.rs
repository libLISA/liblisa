use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::marker::PhantomData;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use liblisa::arch::Arch;
use liblisa::encoding::Encoding;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::semantics::default::smtgen::{StorageLocations, Z3Model};
use liblisa::smt::z3::Z3Solver;
use liblisa::smt::{SmtBV, SmtSolver};
use liblisa_enc::infer_encoding;
use liblisa_synth::{
    determine_overlapping_write_order, merge_semantics_into_encoding, prepare_templates, DefaultTreeTemplateSynthesizer, Output,
    SynthesisLoop,
};
use log::info;

use crate::SimpleCommand;

#[derive(Clone, Debug, clap::Parser)]
/// Synthesize semantics for a single encoding
pub struct SynthesizeEncodingCommand<A> {
    /// The JSON-representation of the encoding.
    encoding_data: Option<String>,

    #[clap(long)]
    /// The instruction to synthesize.
    instruction: Option<Instruction>,

    #[clap(long)]
    /// A file containing the JSON-representation of the encoding.
    file: Option<PathBuf>,

    #[clap(long)]
    /// Which output indices to synthesize.
    /// When not specified, all outputs are synthesized.
    output_index: Vec<usize>,

    #[clap(long)]
    /// When enabled, a panic will be triggered when synthesis is not successful.
    /// In that case, the binary will exit with a non-zero status code.
    panic_when_failed: bool,

    #[clap(long)]
    /// An optional synthesis timeout, in seconds.
    timeout: Option<u64>,

    #[clap(long)]
    /// When enabled, the synthesized semantics will be printed in SMTLib format to stdout.
    print_smt: bool,

    #[clap(long)]
    /// When enabled, the synthesized semantics will be printed as JSON to stdout.
    print_json: bool,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

fn shortest_smt<'ctx, S: SmtSolver<'ctx>>(smt: S::BV) -> String {
    let simplified_str = smt.clone().simplify().to_string();
    let normal_str = smt.to_string();
    if simplified_str.len() < normal_str.len() {
        simplified_str
    } else {
        normal_str
    }
}

impl<A: Arch> SimpleCommand<A> for SynthesizeEncodingCommand<A> {
    type Setup = Encoding<A, ()>;

    fn prepare(&self) {
        // Do the work to const-expand the templates upfront, so it doesn't count against the synthesis time.
        println!("Preparing templates...");
        prepare_templates();
        println!("Templates prepared!");
    }

    fn setup(&self, oracle: &mut impl Oracle<A>) -> Self::Setup {
        let encoding: Encoding<A, ()> = if let Some(data) = &self.encoding_data {
            serde_json::from_str(data).unwrap()
        } else if let Some(file) = &self.file {
            if let Ok(file) = File::open(file) {
                serde_json::from_reader(BufReader::new(file)).unwrap()
            } else {
                let encoding = infer_encoding(&self.instruction.unwrap(), oracle).unwrap();
                serde_json::to_writer(BufWriter::new(File::create(file).unwrap()), &encoding).unwrap();
                encoding
            }
        } else {
            infer_encoding(&self.instruction.unwrap(), oracle).unwrap()
        };
        println!("Encoding: {encoding:}");

        let mut encoding = encoding.canonicalize();
        encoding.split_flag_output();
        encoding.integrity_check().expect("encoding integrity check should not fail");

        println!("Encoding:");
        println!("{encoding}");

        encoding
    }

    fn run(&self, oracle: &mut impl Oracle<A>, encoding: &mut Self::Setup) {
        let mut rng = rand::thread_rng();
        let timeout = self.timeout.map(Duration::from_secs);
        let mut outputs = Output::extract_from_encoding(encoding);

        if !self.output_index.is_empty() {
            outputs.retain(|item| self.output_index.contains(&item.output_index));
        }

        let outputs = outputs;

        println!("Encoding: {encoding}");

        let stopwatch = Instant::now();

        let mut synthesis_loop = SynthesisLoop::<_, DefaultTreeTemplateSynthesizer>::new(encoding, outputs.clone(), timeout);
        let computations = synthesis_loop.run(oracle, &mut rng);
        let write_ordering = determine_overlapping_write_order(&mut rng, oracle, encoding, &computations);

        info!("Computations: {computations:#?}");

        let encoding = encoding.map_computations(|_, _| None);
        let mut semantics = merge_semantics_into_encoding(encoding, computations.clone());
        semantics.write_ordering = write_ordering;

        println!("Semantics: {semantics}");
        println!("That took {}ms", stopwatch.elapsed().as_millis());

        if self.panic_when_failed {
            assert!(
                computations.iter().all(|c| c.computation.is_some()),
                "Some computations failed"
            );
        }

        if self.print_smt {
            Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
                let mut storage = StorageLocations::new(&mut context);
                let model = Z3Model::of(&semantics, &mut storage, &mut context);
                let concrete = model.compute_concrete_outputs(&semantics, &mut storage, &mut context);

                println!();

                for item in model.constraints() {
                    println!("constraint: {item}");
                }

                for &index in concrete.intermediate_values_needed() {
                    let intermediate = &model.intermediate_outputs()[index];
                    if let Some(smt) = intermediate.smt() {
                        println!("intermediate: {:?} = {}", intermediate.name(), shortest_smt::<Z3Solver>(smt.clone()))
                    } else {
                        println!("intermediate: {:?} = <missing>", intermediate.name())
                    }
                }

                println!();

                for part_name in concrete.part_names().iter() {
                    println!("part: {:?} = {:?}", part_name.name(), part_name.smt())
                }

                println!();

                for output in concrete.concrete_outputs().iter() {
                    if let Some(smt) = output.smt() {
                        println!("output: {:?} = {}", output.target(), shortest_smt::<Z3Solver>(smt.clone()))
                    } else {
                        println!("output: {:?} = <missing>", output.target())
                    }
                }
            });
        }

        if self.print_json {
            println!("{}", serde_json::to_string(&semantics).unwrap());
        }
    }
}
