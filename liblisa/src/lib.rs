#![allow(incomplete_features)]
#![deny(rustdoc::missing_crate_level_docs, rustdoc::invalid_codeblock_attributes)]
#![warn(missing_docs)]
#![feature(let_chains)]
#![feature(generic_const_exprs)]
#![feature(const_size_of_val)]
#![doc(html_no_source)]
#![doc = include_str!("../README.md")]

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
