# The `liblisa-semantics-tool`
The `liblisa-semantics-tool` is a command-line program that can be used to query libLISA's semantics.
It requires the raw semantics that can be downloaded from [here](https://osf.io/2hfq9/?view_only=a9fb6f0d639b46a287b0ade9f293b249).

## Installation
Through [`cargo`](https://rustup.rs):
```
cargo +nightly install liblisa-semantics-tool
```

## Usage
Run the tool with the `--help` flag to see all possible commands.

### Semantics server
One of the main features of the `liblisa-semantics-tool` is the *semantics server*.
This allows semantics to be queried programmatically via stdin and stdout.
The semantics server *instantiates* semantics: it fills in the correct registers, flags and immediate values from parts in the encoding.
If you were using the raw semantics directly, you would have to implement this instantiation yourself.

You can start the server with:

```bash
liblisa-semantics-tool server amd-3900x.json
```

It may take a while to build the lookup table.
This process can be cached by passing the `--cache lookup-table.cache` flag.
However, note that no verification is performed to ensure that the loaded cache matches the original semantics.

In order to query the semantics, provide an instruction in hexadecimal form followed by a newline to stdin.
A JSON representation of the semantics will be printed to stdout.

The `--debug` flag enables printing of debugging information to `stderr`.
The JSON schema will be printed to `stderr` when the binary starts.
A human-readable representation of the queried semantics is also printed to `stderr`.

### Other examples
Obtaining the JSON schema of the raw semantics:
```bash
liblisa-semantics-tool schema
```

General statistics of the semantics:
```bash
liblisa-semantics-tool get amd-3900x.json stats
```

Print a single encoding:
```bash
liblisa-semantics-tool get amd-3900x.json encoding 00d3
```

Print *all* encodings (Note: this prints over a million lines of text):
```bash
liblisa-semantics-tool get amd-3900x.json full-encodings
```

Print only the bitpatterns of all encodings:
```bash
liblisa-semantics-tool get amd-3900x.json bitpatterns
```


## Building
Clone the repository and run:

```
cargo build --release --bin liblisa-semantics-tool
```