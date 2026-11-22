# Compose a KV API from JSON

Choose the methods you want to expose and the consistency rule they must follow.
The composer writes a Verus trait with a contract on each method. The
[default recipe](spec.json) describes a linearizable store with `get`, `put`,
and `delete`.

```json
{
  "functions": ["get", "put", "delete"],
  "consistency": "linearizability"
}
```

## Run the example

With Python 3 and the [repo toolchain](../../README.md#toolchain) installed, run
this from the repo root.

```bash
bash examples/composed_kv/run.sh examples/composed_kv/spec.json
```

The runner reads the JSON, generates the trait, and asks Verus to type-check it.
Open `target/composed-kv/api.rs` to see the last API that passed the check.
The [checked-in API](api.rs) shows the output for the default recipe.

## What the contract says

The generated `get` looks like this.

```rust
fn get(&mut self, key: K) -> (value: Option<V>)
    requires
        linearizable(old(self).history(), Map::empty()),
    ensures
        records_call(
            old(self).history(),
            final(self).history(),
            Op::Get(key),
            Reply::Value(value),
        ),
        linearizable(final(self).history(), Map::empty()),
;
```

Before the call, the history must already be linearizable. When `get` returns,
the history gains exactly one request and its matching reply. That reply carries
the value the method actually returned. The updated history must still have a
legal replay from an empty map that respects which calls finished before others
started. For example, if the only earlier call was a completed `Put(x, 7)`, a
later `Get(x)` must return `Some(7)`.

Each method takes `&mut self`, so calls through one handle are exclusive.
`old(self).history()` is the abstract history on entry, and
`final(self).history()` is the history on return.

## Use your own recipe

Copy `spec.json`, edit it, and pass its path to the same runner.

```bash
bash examples/composed_kv/run.sh path/to/your-recipe.json
```

The `functions` list accepts `"get"`, `"put"`, and `"delete"`. To expose an
operation under a different name, use an entry like
`{"name": "lookup", "spec": "get"}`. The `consistency` field accepts
`"linearizability"`, `"sequential_consistency"`, or `"causal_consistency"`.

The [sequential recipe](sequential.json) exposes `lookup` and `put`. Its
contracts call `sequentially_consistent` and restrict the history to reads and
writes.

```bash
bash examples/composed_kv/run.sh examples/composed_kv/sequential.json
```

If you only want to generate the source, call the composer directly.

```bash
python3 tools/compose.py path/to/your-recipe.json -o api.rs
```
