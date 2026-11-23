# dbspec

dbspec is a Verus library for specifying key-value stores. The functional spec
says what `get`, `put`, and `delete` return and what the map looks like afterward.
The consistency specs say which histories are valid when calls from different
sessions overlap. Each session can have one call in progress.

| Model | Required replay |
| --- | --- |
| Linearizability | Replay all selected calls in one order. If one call finished before another started, put it first. |
| Sequential consistency | Use one replay that keeps each session's calls in the order it issued them. |
| Causal consistency | Replay each selected call with its causal predecessors. Each replay respects the same causal order, which includes the order of calls within a session. |

Every model must account for the reply to each completed call. It can leave out
a pending call or include it with a proposed reply. In the causal model, a
call's view replays exactly its causal predecessors and then the call itself.
Only the final call's reply is fixed in that view. Two views can put concurrent
writes in different orders.

## Compose a public KV API

In the JSON recipe, pick the operations to expose and one or more consistency
models to require. The composer generates a Verus contract for each selected
operation. Sessions on the same store share one abstract history. When an
operation returns, the implementation must prove that the history includes the
actual call and reply and satisfies the selected models. For a concurrent Rust
map verified against these contracts, see the [example](examples/composed_kv/README.md).

Run the command from the repo root after installing the [toolchain](#toolchain).

```sh
bash examples/composed_kv/run.sh examples/composed_kv/spec.json
```

The script type-checks the generated API and saves it to `target/composed-kv/api.rs`.

## Reusable proofs

The [ProofLib prototype](src/prooflib/README.md) separates reusable lemmas from
the specification definitions. It is currently the `dbspec::prooflib` module
in this crate, organized into functional laws, history/replay facts, and
consistency lemmas. Concrete specification regression proofs remain in
`src/consistency/tests.rs`. Backend-specific proofs remain with their examples.

The three empty-history lemmas now live under
`dbspec::prooflib::consistency::<model>` instead of the specification modules.
See the ProofLib README for available lemmas, usage, and verification instructions.

## Toolchain

Run the installer from the repo root.

```sh
bash tools/install.sh
```

The script sets up Rustup if needed, installs the pinned Rust toolchain, and
fetches the dependencies in `Cargo.lock`. On macOS (Apple Silicon or Intel) and
x86-64 Linux, it installs Verus and its bundled Z3 solver under `.tools/`. Run
the export commands the script prints to select those tools in your shell.

The installer needs `curl`, `unzip`, and either `sha256sum` or `shasum`. You'll
also need Python 3 to run the composer.

| Component | Version |
| --- | --- |
| Rust | `1.98.0` (selected by `rust-toolchain.toml`) |
| Verus and `cargo-verus` | `0.2026.09.06.8dea4a2` |
| `vstd` | `0.0.0-2026-09-06-0133` (exact dependency pin) |

To install manually, download the build for your platform from the matching
[Verus release](https://github.com/verus-lang/verus/releases/tag/release%2F0.2026.09.06.8dea4a2).
Extract it and add its directory to `PATH` so `verus` and `cargo-verus` come
from the same release. When you run Cargo from the repo, Rustup installs the
Rust version and components listed in `rust-toolchain.toml`.

## Build and verify

```sh
cargo check --locked
cargo verus verify --locked --check-toolchain
```

`cargo check` checks the Rust code with ghost state erased. `cargo verus verify`
also checks the specs and proofs. The first run downloads the locked
dependencies. Once they're cached, you can use `--offline`.

## Version troubleshooting

Check which versions your shell is using.

```sh
rustc --version
verus --version
cargo verus toolchain list
```

Rust should report `1.98.0`. A `RUSTUP_TOOLCHAIN` environment variable or a
`rustup override` can take precedence over the repo's toolchain file. If Verus
reports a different release from the one above, check `PATH`.

When you upgrade, keep the Rust pin, Verus release, and `vstd` pin in sync.
Commit `Cargo.lock` with the dependency changes. Use `--check-toolchain` to
check that the Verus dependencies are compatible. See the [Verus Cargo guide](https://verus-lang.github.io/verus/guide/cargo_verus.html).

## Bug-fix log

### Composed KV histories could diverge across sessions (2026-11-23)

The old contract let each session extend its own history snapshot. If both
sessions started with empty snapshots, one could acknowledge a write and the
other could later return a miss for the same key. Both snapshots passed their
replay checks. The combined history violated linearizability.

The first fix gave each generated store one append-only recorder shared by its
sessions. The wrapper recorded the invocation before the backend ran. Before
returning, the backend checked the reply against the shared history and used
the call's tracked permission to append it. Calls from different sessions
could still overlap. That version used `KvStore::new(backend)` and `KvBackend`.

The generated API now uses `KvSession`. The shared history lives in ghost state
in the example's [refinement proof](examples/composed_kv/refinement.rs). Both
fixes use the same finite-history linearizability predicate. The combined
write-then-miss history has no valid linearization, as checked by the
[regression proof](src/consistency/tests.rs).
