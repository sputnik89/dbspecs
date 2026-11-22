# Generate `api.rs` from JSON

The composer takes a JSON recipe and writes an `api.rs` file with a Verus
trait and a contract on each selected method.

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
Set `consistency` to one of the model names in
[`tools/compose.py`](../../tools/compose.py).

If you want to choose where `api.rs` goes, call the composer with `-o`. This
command writes `api.rs` in the current directory and skips the Verus type
check.

```bash
python3 tools/compose.py examples/composed_kv/spec.json -o api.rs
```

## Sessions and contracts

The default recipe gives you these methods.

```rust
fn new() -> Self
fn open_session(&self) -> Self
fn get(&mut self, key: K) -> Option<V>
fn put(&mut self, key: K, value: V)
fn delete(&mut self, key: K)
```

`new` gives you the first handle to an empty store. Call `open_session` to get
another handle to the same store. With `&mut self`, each handle takes one call
at a time. Calls on different handles can overlap.

## Run the Rust demo

The [two-session demo](main.rs) imports the [checked-in `api.rs`](api.rs) for
the default recipe. Run it from the repo root.

```bash
cargo run --locked --example composed_kv
```

The demo implements the trait's Rust methods with two shards, each with its
own lock. Both handles share the shards through an `Arc`. Each thread borrows
its own handle mutably and writes to a different shard. Once the threads
finish, each handle reads what the other wrote.

## Implement the generated API

Copy the generated `api.rs` into a crate that depends on `dbspec` and the
pinned `vstd`, then import it with `mod api;`. Implement `KvStore<K, V>` and
add proofs that the handles see prefixes of one shared history and that the
recorded calls and replies match what the store does.

Each contract checks the selected consistency models against the history
before the call and at return. The return history keeps the earlier events
and records this call's arguments and actual reply. Events from other
sessions can appear between invocation and reply.

If you're implementing the default API in the checked-in example, run Verus
on that target once the implementation and its proofs are in place.

```bash
cargo verus verify --locked --check-toolchain --example composed_kv
```

## Add a functional spec or consistency model

Operations and models have separate tables in
[`tools/compose.py`](../../tools/compose.py). For a new operation, add a
variant in `Op` and a rule in `step`. A new model needs a predicate that
takes a history and an initial map.
