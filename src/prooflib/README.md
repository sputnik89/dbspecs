# ProofLib

ProofLib provides reusable Verus lemmas over SpecLib's abstract models and
semantics. It is available as `dbspec::prooflib` within the `dbspec` crate.

## Organization

Lemmas are grouped by the property they establish.

```text
prooflib/
├── mod.rs
├── functional/
│   ├── mod.rs
│   └── kv.rs                    Laws for abstract KV operations
├── history/
│   ├── mod.rs
│   └── replay.rs                Structural properties of legal replay
└── consistency/
    ├── mod.rs
    ├── linearizability.rs       Empty-history lemma
    ├── sequential_consistency.rs
    └── causal_consistency.rs
```

| Module | Purpose | Current coverage |
| --- | --- | --- |
| `functional` | Reusable properties of abstract operations | Read-after-write, read-after-delete, and preservation of other keys |
| `history` | Structural properties of histories and replay witnesses | Entries in a legal replay are invocations |
| `consistency` | Theorems about a particular consistency model | Empty-history lemmas for linearizability, sequential consistency, and causal consistency |

### Available lemmas

The library currently exposes eight proof functions.

| Module | Lemma | Property |
| --- | --- | --- |
| `functional::kv` | `get_after_put` | Reading a key after writing it returns the new value. |
| `functional::kv` | `get_after_delete` | Reading a key after deleting it returns `None`. |
| `functional::kv` | `put_preserves_other_key` | Writing one key preserves the lookup result for a distinct key. |
| `functional::kv` | `delete_preserves_other_key` | Deleting one key preserves the lookup result for a distinct key. |
| `history::replay` | `replay_entry_is_invocation` | An entry at a valid index in a legal replay is an invocation. |
| `consistency::linearizability` | `linearizable_empty` | An empty history is linearizable for any initial map. |
| `consistency::sequential_consistency` | `sequentially_consistent_empty` | An empty history is sequentially consistent for any initial map. |
| `consistency::causal_consistency` | `causally_consistent_empty` | An empty history is causally consistent for any initial map. |

## Usage

Import lemmas through their ProofLib paths, for example:

```rust
#[cfg(verus_only)]
use dbspec::prooflib::consistency::linearizability::linearizable_empty;
```

Call an imported lemma from proof code. The caller must establish its
preconditions; after the call, its postconditions are available to the proof.
The `cfg(verus_only)` attribute enables the import for Verus verification.

## Verification

Set up the [pinned toolchain](../../README.md#toolchain), ensure `verus` is on
`PATH`, and run from the repository root:

```sh
cargo check --locked --lib --example composed_kv
verus src/lib.rs --crate-type lib --crate-name dbspec --edition=2021 --cfg verus_only --no-cheating --num-threads 1 --rlimit 30
```

`cargo check` checks compilation. Verus verifies the library's lemmas and
specification regression proofs, not the complete KV example. Both commands
should succeed, with Verus reporting zero errors.
