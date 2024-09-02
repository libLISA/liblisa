libLISA is a library for automated discovery and analysis of CPU instructions.
This crate is the core library that can be used to load and manipulate already-analyzed datasets.
Several separate crates are available for enumeration, synthesis and architecture support:

- [`liblisa-enc`](https://crates.io/crates/liblisa-enc) for enumeration and encoding analysis
- [`liblisa-synth`](https://crates.io/crates/liblisa-synth) for synthesis
- [`liblisa-x64-observer`](https://crates.io/crates/liblisa-x64-observer) for observing instruction execution on x86-64

# Loading semantics from disk
Encodings support serde, and can be serialized and deserialized by any library that supports serde.
By default, libLISA uses JSON.
You can import these semantics as follows:

```rust
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use liblisa::encoding::Encoding;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::arch::x64::X64Arch;

let file = File::open("semantics.json").unwrap();
let reader = BufReader::new(file);
let semantics: Vec<Encoding<X64Arch, SynthesizedComputation>> =
    serde_json::from_reader(reader).unwrap();
```

See [`encoding::Encoding`](https://docs.liblisa.nl/liblisa/encoding/struct.Encoding) for how these semantics can be used.

# Features

- `z3`: adds the `z3` crate as a dependency, and enables the Z3 implementation for `smt::SmtSolver`.
- `x64-undef`: enables the `arch::x64::undef` namespace, which uses the XED disassembler library to provide definitions for undefined behavior.