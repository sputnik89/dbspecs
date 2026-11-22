# dbspec

dbspec is a Verus library for specifying key-value store behavior. The functional
spec defines what `get`, `put`, and `delete` do to a map one call at a time.
The consistency specs describe which histories are valid when calls from
different sessions overlap. Each session can have one outstanding call.

| Model | Required replay |
| --- | --- |
| Linearizability | One replay that preserves every response that occurs before another call's invocation |
| Sequential consistency | One replay that preserves invocation order within each client session |
| Causal consistency | A replay for each operation that preserves a shared causal order containing session order |

All models explain the recorded replies of completed calls. A pending call can be
omitted or included with a proposed reply. In the causal model, each operation
replays exactly its causal predecessors and then itself. Only that operation's
reply is fixed in its view, so different views can order concurrent writes
differently.

## Compose a public KV API

The [example](examples/composed_kv/README.md) takes a JSON recipe and produces a
Verus API with a contract on each selected operation. Pick any subset of the
registered operations and one or more consistency models. Each contract connects
the call and its reply to the store's history and checks the selected models
against that history.
With the [toolchain](#toolchain) installed, run it from the repo root.

```sh
bash examples/composed_kv/run.sh examples/composed_kv/spec.json
```

The runner type-checks the generated API and saves it to `target/composed-kv/api.rs`.

## Toolchain

From the repo root, run:

```sh
bash tools/install.sh
```

The installer sets up Rustup if needed, installs the pinned Rust toolchain, and
fetches the dependencies in `Cargo.lock`. It installs Verus and its bundled Z3
solver under `.tools/` on macOS (Apple Silicon or Intel) and x86-64 Linux. Run the
export commands it prints to select those tools in your shell. The installer
requires `curl`, `unzip`, and either `sha256sum` or `shasum`. The composer uses
Python 3.

Use these versions together:

| Component | Version |
| --- | --- |
| Rust | `1.98.0` (selected by `rust-toolchain.toml`) |
| Verus and `cargo-verus` | `0.2026.09.06.8dea4a2` |
| `vstd` | `0.0.0-2026-09-06-0133` (exact dependency pin) |

For a manual install, download the matching [Verus release](https://github.com/verus-lang/verus/releases/tag/release%2F0.2026.09.06.8dea4a2)
for your platform and add its extracted directory to `PATH`. Both `verus` and
`cargo-verus` should come from that release. Rustup installs the Rust version and
components declared in `rust-toolchain.toml` when you run Cargo in this directory.

## Build and verify

```sh
cargo check --locked
cargo verus verify --locked --check-toolchain
```

`cargo check` checks the Rust build after ghost erasure. Run `cargo verus verify`
to check the specifications and proofs as well. The first run downloads the locked
dependencies; subsequent runs can use `--offline` if they are all cached.

## Version troubleshooting

Check the tools selected in your shell:

```sh
rustc --version
verus --version
cargo verus toolchain list
```

Rust should report `1.98.0`. If it reports another version, check for a
`RUSTUP_TOOLCHAIN` environment variable or a `rustup override` taking precedence
over the repository's toolchain file. Verus should report the release listed above;
check `PATH` if a different installation is selected.

Keep the Rust pin, Verus release, and `vstd` pin aligned when upgrading. Commit
`Cargo.lock` along with dependency changes. The `--check-toolchain` flag checks
Verus dependency compatibility. See the [Verus Cargo guide](https://verus-lang.github.io/verus/guide/cargo_verus.html).
