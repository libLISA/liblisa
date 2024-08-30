use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::time::Duration;

use clap::Parser;
use liblisa::arch::x64::X64Arch;
use liblisa::encoding::Encoding;
use liblisa::instr::Instruction;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::semantics::default::smtgen::{StorageLocations, Z3Model};
use liblisa::smt::z3::{Z3Solver, BV};
use liblisa::smt::SmtBV;

#[derive(Clone, Debug, clap::Parser)]
pub struct Args {
    encodings: PathBuf,
    instr: Instruction,

    #[clap(long)]
    instantiate: bool,
}

fn shortest_smt(smt: BV) -> String {
    let simplified_str = smt.clone().simplify().to_string();
    let normal_str = smt.to_string();
    if simplified_str.len() < normal_str.len() {
        simplified_str
    } else {
        normal_str
    }
}

pub fn main() {
    env_logger::init();

    let args = Args::parse();

    println!("Loading encodings...");
    let encodings: Vec<Encoding<X64Arch, SynthesizedComputation>> =
        serde_json::from_reader(BufReader::new(File::open(args.encodings).unwrap())).unwrap();

    Z3Solver::with_thread_local(Duration::from_secs(30), |mut context| {
        let mut storage = StorageLocations::new(&mut context);

        for encoding in encodings.iter() {
            if encoding.bitpattern_as_filter().matches(&args.instr) && encoding.filters().iter().any(|f| f.matches(&args.instr)) {
                println!("Generating z3 model of: {encoding}");
                let encoding = if args.instantiate {
                    let part_values = encoding.extract_parts(&args.instr).into_iter().map(Some).collect::<Vec<_>>();
                    let encoding = encoding.instantiate_partially(&part_values).unwrap();
                    println!("Instantiated to: {encoding}");
                    encoding
                } else {
                    encoding.clone()
                };

                let model = Z3Model::of(&encoding, &mut storage, &mut context);
                let concrete = model.compute_concrete_outputs(&encoding, &mut storage, &mut context);

                println!();

                for item in model.constraints() {
                    println!("constraint: {item}");
                }

                for &index in concrete.intermediate_values_needed() {
                    let intermediate = &model.intermediate_outputs()[index];
                    if let Some(smt) = intermediate.smt() {
                        println!("intermediate: {:?} = {}", intermediate.name(), shortest_smt(smt.clone()))
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
                        println!("output: {:?} = {}", output.target(), shortest_smt(smt.clone()))
                    } else {
                        println!("output: {:?} = <missing>", output.target())
                    }
                }
            }
        }
    });
}
