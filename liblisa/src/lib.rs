#![allow(incomplete_features)]
#![deny(rustdoc::missing_crate_level_docs, rustdoc::invalid_codeblock_attributes)]
#![warn(missing_docs)]
#![feature(asm_const)]
#![feature(let_chains)]
#![feature(generic_const_exprs)]
#![feature(const_intrinsic_copy)]
#![feature(const_mut_refs)]
#![feature(const_size_of_val)]
#![doc(html_no_source)]

//! libLISA is a library for automated discovery and analysis of CPU instructions.
//! This crate is the core library that can be used to load and manipulate already-analyzed datasets.
//! Several separate crates are available for enumeration, synthesis and architecture support:
//!
//! - `liblisa-enc` for enumeration and encoding analysis
//! - `liblisa-synth` for synthesis
//! - `liblisa-x64` and `liblisa-x64-observer` for x86-64 support
//!
//! # Loading semantics from disk
//! Encodings support serde, and can be serialized and deserialized by any library that supports serde.
//! By default, libLISA uses JSON.
//! You can import these semantics as follows:
//!
//! ```rust
//! # fn wrap() { // wrap the code in a function so that the test does not access the filesystem, but still typechecks.
//! use std::fs::File;
//! use std::io::BufReader;
//! use std::path::PathBuf;
//!
//! use liblisa::encoding::Encoding;
//! use liblisa::semantics::default::computation::SynthesizedComputation;
//! use liblisa::arch::x64::X64Arch;
//!
//! let file = File::open("semantics.json").unwrap();
//! let reader = BufReader::new(file);
//! let semantics: Vec<Encoding<X64Arch, SynthesizedComputation>> =
//!     serde_json::from_reader(reader).unwrap();
//! # }
//! ```
//!
//! See [`encoding::Encoding`] for how these semantics can be used.
//!
//! # Features
//!
//! - `z3`: adds the `z3` crate as a dependency, and enables the Z3 implementation for [`smt::SmtSolver`].
//! - `x64-undef`: enables the [`arch::x64::undef`] namespace, which uses the XED disassembler library to provide definitions for undefined behavior.

pub mod arch;
pub mod compare;
pub mod encoding;
pub mod instr;
pub mod oracle;
pub mod semantics;
pub mod smt;
pub mod state;
pub mod utils;
pub mod value;

pub use instr::Instruction;
