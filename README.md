# dbspec

Verus specifications for a sequential key-value store and consistency models for its histories.

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

The [example recipe](examples/composed_kv/spec.json) selects the methods and
the guarantee on their shared history:

```json
{
  "functions": ["get", "put", "delete"],
  "consistency": "linearizability"
}
```

Pass the JSON file to the composer:

```sh
python3 tools/compose.py examples/composed_kv/spec.json -o examples/composed_kv/api.rs
```

The composer prints the API to stdout unless you pass `--output`. To type-check
the checked-in example, run:

```sh
cargo verus verify --locked --check-toolchain --example composed_kv -- --no-verify
```

The generated [`KvStore<K, V>`](examples/composed_kv/api.rs) trait contains
bodyless method declarations. Each method names the selected consistency
predicate in its `requires` and `ensures`, and its postcondition binds the
actual arguments and reply to the call added to the history. The selected
model applies the existing KV rules to that history from an empty map.

A function name such as `"get"` selects the KV spec with the same name.
To expose it under a different API name, use
`{"name": "lookup", "spec": "get"}` in the `functions` list.

The methods take `&mut self` so the contracts can describe the history before and
after each call. This interface describes exclusive calls on a handle.
The recipe also accepts `"sequential_consistency"` and `"causal_consistency"`.
The history may contain only operations selected by the recipe.

## Toolchain

Use these versions together:

| Component | Version |
| --- | --- |
| Rust | `1.98.0` (selected by `rust-toolchain.toml`) |
| Verus and `cargo-verus` | `0.2026.09.06.8dea4a2` |
| `vstd` | `0.0.0-2026-09-06-0133` (exact dependency pin) |

Install the matching [Verus release](https://github.com/verus-lang/verus/releases/tag/release%2F0.2026.09.06.8dea4a2)
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
