#![feature(let_chains)]
#![doc(html_no_source)]

use std::collections::HashMap;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use clap::{Args, FromArgMatches};
use liblisa::arch::{Arch, CpuState, Flag, Register, Scope};
use liblisa::instr::Instruction;
use liblisa::oracle::{Oracle, OracleSource};
use liblisa::state::{Addr, MemoryState, Permissions, SystemState};
use liblisa::value::MutValue;
use nix::sched::CpuSet;
use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::threadpool::cpu::CpuCaches;

mod detect_changes;
mod enumerate;
mod infer_accesses;
mod infer_dataflows;
mod infer_encoding;
mod infer_validity;
mod observe;
mod quick_enumerate;
mod synthesize;
mod synthesize_encoding;
pub mod threadpool;

pub use detect_changes::DetectChangesCommand;
pub use enumerate::EnumerationCommand;
pub use infer_accesses::InferAccessesCommand;
pub use infer_dataflows::InferDataflowsCommand;
pub use infer_encoding::InferEncodingCommand;
pub use infer_validity::InferValidityCommand;
pub use observe::ObserveCommand;
pub use quick_enumerate::QuickEnumerateCommand;
pub use synthesize::SynthesizeCommand;
pub use synthesize_encoding::SynthesizeEncodingCommand;

/// Prints a command sequence to stdout that clears the screen.
pub fn clear_screen() {
    println!();
    println!("\x1B[H\x1B[2J\x1B[3J");
}

/// Helper function that converts a hexadecimal string to bytes.
pub fn hex_str_to_bytes(s: &str) -> Vec<u8> {
    let tmp;
    let s = if let Some(pos) = s.find('*') {
        let num_repeat = s[..pos].parse().unwrap();
        tmp = s[pos + 1..].repeat(num_repeat);
        &tmp
    } else {
        s
    };

    let mut bytes = vec![0; s.len() / 2];
    hex::decode_to_slice(s, &mut bytes).unwrap();
    bytes
}

#[derive(Clone, Debug, thiserror::Error)]
enum ParseError {}

fn parse_flag(s: &str) -> Result<(String, bool), ParseError> {
    let mut split = s.split('=');
    let name = split.next().unwrap();
    let value = match split.next().unwrap() {
        "false" | "unset" | "no" | "0" => false,
        "true" | "set" | "yes" | "1" => true,
        value => panic!("Invalid flag value: {value}. Use true or false."),
    };

    Ok((name.to_owned(), value))
}

fn parse_register(s: &str) -> Result<(String, Vec<u8>), ParseError> {
    let mut split = s.split('=');
    let name = split.next().unwrap();
    let value = hex_str_to_bytes(split.next().unwrap());

    Ok((name.to_owned(), value))
}

fn parse_memory(s: &str) -> Result<(u64, Vec<u8>), ParseError> {
    let mut split = s.split('=');
    let addr = split.next().unwrap();
    let value = hex_str_to_bytes(split.next().unwrap());
    let addr = u64::from_str_radix(addr, 16).unwrap();

    Ok((addr, value))
}

/// Parsed register, flag and memory inputs from the command line.
#[derive(Clone, Debug, clap::Parser)]
pub struct StateSpecArgs {
    #[clap(short = 'r', value_parser = parse_register)]
    regs: Vec<(String, Vec<u8>)>,

    #[clap(short = 'f', value_parser = parse_flag)]
    flags: Vec<(String, bool)>,

    #[clap(short = 'm', value_parser = parse_memory)]
    memory: Vec<(u64, Vec<u8>)>,
}

fn bytes_to_u64(bytes: impl AsRef<[u8]>) -> u64 {
    bytes.as_ref().iter().fold(0, |acc, &x| (acc << 8) | x as u64)
}

impl StateSpecArgs {
    pub fn create_state<A: Arch>(&self, instr: Instruction, default_pc: u64) -> SystemState<A> {
        let regs = self.regs.iter().cloned().collect::<HashMap<_, _>>();
        let flags = self.flags.iter().cloned().collect::<HashMap<_, _>>();
        let pc = regs.get(&format!("{}", A::PC)).map(bytes_to_u64).unwrap_or(default_pc);
        let mut mem = vec![(Addr::new(pc), Permissions::Execute, instr.bytes().to_owned())];

        for (addr, data) in self.memory.iter() {
            mem.push((Addr::new(*addr), Permissions::ReadWrite, data.clone()));
        }

        let mut cpu = A::CpuState::create(|reg, value| {
            if reg.is_pc() {
                match value {
                    MutValue::Num(value) => *value = pc,
                    _ => unreachable!(),
                }
            } else {
                let bytes = regs.get(&format!("{reg}"));
                match value {
                    MutValue::Num(value) => *value = bytes.map(bytes_to_u64).unwrap_or(0),
                    MutValue::Bytes(buf) => {
                        if let Some(bytes) = bytes {
                            buf[0..bytes.len()].copy_from_slice(bytes);
                        }
                    },
                }
            }
        });

        for flag in A::Flag::iter() {
            cpu.set_flag(flag, flags.get(&format!("{flag}")).cloned().unwrap_or(false));
        }

        SystemState::new(cpu, MemoryState::from_vec(mem))
    }
}

/// A trait required for [`CommandExtension`].
pub trait SimpleCommand<A: Arch> {
    type Setup;

    /// Preparation function executed before restricting CPU cores for oracle.
    fn prepare(&self) {}

    /// Setup of command, using the oracle.
    fn setup(&self, oracle: &mut impl Oracle<A>) -> Self::Setup;

    /// Runs the command once
    fn run(&self, oracle: &mut impl Oracle<A>, setup: &mut Self::Setup);
}

/// Wraps any command and provides it `--repeat`, `--measure` and `--clear` flags.
#[derive(Clone, Debug, clap::Parser)]
pub struct CommandExtension<A, T: Args + FromArgMatches> {
    #[clap(long)]
    /// The number of times that the operation should be repeated.
    repeat: Option<usize>,

    #[clap(long)]
    /// When enabled, the runtime of each iteration is measured.
    measure: bool,

    #[clap(long)]
    /// When enabled, the terminal output is cleared at the start of each iteration.
    clear: bool,

    #[clap(flatten)]
    inner: T,

    #[clap(skip)]
    _phantom: PhantomData<A>,
}

impl<A: Arch, T: SimpleCommand<A> + Args + FromArgMatches> CommandExtension<A, T> {
    fn single_oracle<S: OracleSource>(mut create_oracle_source: impl FnMut(CpuSet) -> S) -> S::Oracle {
        let cpu = CpuCaches::from_path("/sys/devices/system/cpu/cpu0/cache").unwrap();
        // Restrict the current thread to only run on cores that share L3 cache.
        let cache = cpu.caches().find(|c| c.level() == 3).unwrap();
        println!("Restricting affinity to CPUs that share {cache:#?}");
        cache.restrict_current_thread_affinity_to_shared_caches().unwrap();

        create_oracle_source(cache.shared_with()).start().remove(0)
    }

    pub fn run<S: OracleSource>(&self, create_oracle_source: impl FnMut(CpuSet) -> S)
    where
        S::Oracle: Oracle<A> + Send,
    {
        self.inner.prepare();

        let mut oracle = Self::single_oracle(create_oracle_source);
        let mut setup = self.inner.setup(&mut oracle);

        let mut timings = Vec::new();
        let repeat = self.repeat.unwrap_or(1);
        for k in 0..repeat {
            if repeat != 1 {
                println!("Iteration {k}:");
            }

            let start = Instant::now();
            self.inner.run(&mut oracle, &mut setup);

            // TODO: Abort on error
            // TODO: Count invocations

            if repeat != 1 {
                println!();
            }

            if self.measure {
                let elapsed = start.elapsed();
                timings.push(elapsed);
                println!("That took {}ms", elapsed.as_millis());
                println!();
            }

            if self.clear {
                clear_screen();
            }
        }

        if self.measure {
            let avg = timings.iter().sum::<Duration>() / timings.len() as u32;
            let min = timings.iter().min().unwrap();
            let max = timings.iter().max().unwrap();
            println!("Average time taken: {}ms", avg.as_millis());
            println!("Range: {}ms - {}ms", min.as_millis(), max.as_millis());
        }
    }
}

#[derive(Clone, Debug, clap::Parser)]
#[clap(verbatim_doc_comment)]
/// This is the libLISA command line analysis tool.
///
/// The `enumerate` and `synthesize` subcommands are the main entry points.
/// Other commands are intended for debugging or manual exploration.
///
/// In order to analyze a CPU, you first need to enumerate the instruction space.
/// The `enumerate` command can do this. Next, semantics can be synthesized using
/// the `synthesize` command.
pub enum CliCommand<A> {
    Enumerate(EnumerationCommand<A>),
    Synthesize(SynthesizeCommand<A>),

    QuickEnumerate(CommandExtension<A, QuickEnumerateCommand<A>>),

    InferValidity(CommandExtension<A, InferValidityCommand<A>>),
    InferAccesses(CommandExtension<A, InferAccessesCommand<A>>),
    InferDataflows(CommandExtension<A, InferDataflowsCommand<A>>),
    InferEncoding(CommandExtension<A, InferEncodingCommand<A>>),
    SynthesizeEncoding(CommandExtension<A, SynthesizeEncodingCommand<A>>),

    DetectChange(CommandExtension<A, DetectChangesCommand<A>>),
    Observe(CommandExtension<A, ObserveCommand<A>>),
}

impl<A: Arch> CliCommand<A> {
    pub fn run<S: OracleSource, E: Scope + Serialize + DeserializeOwned>(
        &self, create_oracle_source: impl FnMut(CpuSet) -> S, scope: E,
    ) where
        S::Oracle: Oracle<A> + Send,
    {
        match self {
            CliCommand::Enumerate(x) => x.run(create_oracle_source, scope),
            CliCommand::Synthesize(x) => x.run(create_oracle_source),
            CliCommand::DetectChange(x) => x.run(create_oracle_source),
            CliCommand::InferAccesses(x) => x.run(create_oracle_source),
            CliCommand::InferDataflows(x) => x.run(create_oracle_source),
            CliCommand::InferEncoding(x) => x.run(create_oracle_source),
            CliCommand::SynthesizeEncoding(x) => x.run(create_oracle_source),
            CliCommand::InferValidity(x) => x.run(create_oracle_source),
            CliCommand::Observe(x) => x.run(create_oracle_source),
            CliCommand::QuickEnumerate(x) => x.run(create_oracle_source),
        }
    }
}
