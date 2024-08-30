# libLISA
`libLISA` is a library for automatically discovering and analyzing CPU instructions.
It relies on minimal human input: only a definition of CPU state and a CPU observer are required to be implemented.

## Results
We have analyzed 5 different x86-64 architectures.
You can download the generated semantics [here](https://osf.io/2hfq9/?view_only=a9fb6f0d639b46a287b0ade9f293b249).

## Using the semantics
The easiest way to use the semantics is to use the `liblisa-semantics-tool`.
This tool provides various ways to access the semantics.
One of these, the "semantics server", makes the semantics available over stdin/stdout.

The semantics server can be started with (assuming `encodings.json` is the path to the semantics):

```sh
cargo run -r --bin liblisa-semantics-tool -- server encodings.json
```

When writing a hexadecimal instruction followed by a newline to stdin, the semantics server will instantiate a matching encoding and output easy-to-parse JSON semantics for this specific instruction.

The semantics are stored as JSON files.
To aid parsing, the schema can be obtained by running `cargo run --bin liblisa-semantics-tool -- schema`.
Libraries are provided to load and manipulate the semantics using Rust.
The semantics can be loaded using the `serde_json` crate. This can be done as follows:

```rust
let file = BufReader::new(File::open("semantics.json")?);
let semantics: Vec<Encoding<X64Arch, SynthesizedComputation>> = serde_json::from_reader(file)?;
```

# Project structure
The project is split into several crates:

 * `liblisa`: definitions of CPU state, ISAs, encodings, dataflows and other core components of libLISA.
 * `liblisa-enc`: encoding analysis.
 * `liblisa-synth`: semantics synthesis.
 * `cli/liblisa-libcli`: the generic analysis CLI. It is instantiated by:
    * `cli/liblisa-x64`
 * `arch`: folder that contains architecture-specific observers.

# License
The code in this repository is licensed under the AGPLv3.