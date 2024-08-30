mod random_search;
mod tunnel;

#[doc(hidden)] // see `random_instr_bytes`
pub use random_search::random_instr_bytes;
pub use random_search::random_search_skip_invalid_instrs;
pub use tunnel::{tunnel_invalid_instrs, tunnel_memory_errors};
