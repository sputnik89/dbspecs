# Generate `api.rs` from JSON

The composer takes a JSON recipe and writes an `api.rs` file with a Verus store API with a contract on each selected method.

## Generate and check `api.rs`

1. From the repo root, install the [repo toolchain](../../README.md#toolchain)
   with `bash tools/install.sh` and run the export commands it prints. You'll
   also need Python 3.
2. Use [`examples/composed_kv/spec.json`](spec.json). This is the recipe for
   the concurrent demo. It specifies a linearizable store with `get`, `put`,
   and `delete`.

   ```json
   {
     "functions": ["get", "put", "delete"],
     "consistency": "linearizability"
   }
   ```

3. From the repo root, pass the recipe path to the runner.

   ```bash
   bash examples/composed_kv/run.sh examples/composed_kv/spec.json
   ```

4. Open `target/composed-kv/api.rs`. The runner generates the file, asks Verus
   to type-check it, and saves it there when the check passes. Look for
   `Type-checked API:` followed by the output path.

## Generate from your own recipe

Copy `examples/composed_kv/spec.json`, edit it, and pass the new path to the
same runner. Each successful run replaces `target/composed-kv/api.rs`.

```bash
bash examples/composed_kv/run.sh path/to/your-recipe.json
```

Pick at least one of `"get"`, `"put"`, and `"delete"` for `functions`. To
rename an operation, use an entry like `{"name": "lookup", "spec": "get"}`.
Set `consistency` to `"linearizability"`, `"sequential_consistency"`, or
`"causal_consistency"`. A list of model names requires every model in the list.

If you want to choose where `api.rs` goes, call the composer with `-o`. This
command writes `api.rs` in the current directory and skips the Verus type
check.

```bash
python3 tools/compose.py examples/composed_kv/spec.json -o api.rs
```

## Sessions and contracts

The default recipe generates a `KvSession` trait with contracts on `get`,
`put`, and `delete`. In the example, create a `Store` and call
`store.open_session()` once for each client. Methods borrow the session with
`&mut self`, so each session has one call at a time. Sessions on the same
store can run concurrently.

Each method must extend the session's previous snapshot of the shared history
with the actual invocation and reply. Calls from other sessions can appear
between those two events. The selected consistency models check the full
history up to that reply. `local_history()` keeps just that session's events
from the snapshot.

## Run the Rust demo

The [two-session demo](main.rs) imports the [checked-in `api.rs`](api.rs) for
the default recipe. Run it from the repo root.

```bash
cargo run --locked --example composed_kv
```

Both threads write to the same store using separate sessions. After joining,
each session reads what the other wrote. One lock protects the concrete map.
The global history, session histories, and proof state are erased from the
Rust build.

## Implement the generated API

Copy the generated `api.rs` into a crate that depends on `dbspec` and the
pinned `vstd`, then import it with `mod api;` and implement `KvSession<K, V>`.
Use `call_started` and `call_finished` to state how the actual calls and replies
extend one shared history. The method contracts check the actual reply and
the selected models against the session's history snapshot. Your refinement
proof establishes that every session's snapshot comes from the same store
execution.

In the sample, [`main.rs`](main.rs) runs each map operation and shows it matches
the functional spec. The [refinement proof](refinement.rs) uses the order in
which operations take effect under the map lock to prove that the shared
history is linearizable.

```bash
cargo verus verify --locked --check-toolchain --example composed_kv
```

This command verifies the backend and its proof against the checked-in API.

## Add a functional spec or consistency model

Operations and models have separate tables in
[`tools/compose.py`](../../tools/compose.py). For a new operation, add a
variant in `Op` and a rule in `step`. A new model needs a predicate that
takes a history and an initial map.
