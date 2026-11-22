#!/usr/bin/env python3
"""Read a JSON recipe and emit a Verus API with a contract on every function."""

import argparse
import json
from pathlib import Path
import re


MODELS = {
    "linearizability": ("linearizability", "linearizable"),
    "sequential_consistency": ("sequential_consistency", "sequentially_consistent"),
    "causal_consistency": ("causal_consistency", "causally_consistent"),
}

FUNCTION_SPECS = {
    "get": ("key: {key}", "Get", "key", " -> (value: Option<{value}>)", "Reply::Value(value)"),
    "put": ("key: {key}, value: {value}", "Put", "key, value", "", "Reply::Ack"),
    "delete": ("key: {key}", "Delete", "key", "", "Reply::Ack"),
}

FUNCTION_NAME = re.compile(r"[a-z_][a-z0-9_]*")
RESERVED_NAMES = frozenset("""
    _ history new open_session session_id store_id
    as async await break const continue crate dyn else enum extern false fn for gen if
    impl in let loop match mod move mut pub ref return self static struct super trait true type
    unsafe use where while abstract become box do final macro override priv try typeof unsized
    virtual yield union exec proof spec open closed uninterp ghost tracked requires recommends
    ensures default_ensures returns decreases with opens_invariants invariant_except_break
    no_unwind invariant invariant_ensures assert assume reveal reveal_with_fuel hide implies by
    forall exists choose is isnt spec_fn proof_fn via when any none has hasnt global size_of
    layout matches broadcast group assume_specification atomically outer_mask inner_mask no_abort
""".split())


def resolve_functions(entries):
    if not isinstance(entries, list) or not entries:
        raise ValueError("'functions' must be a nonempty list")

    functions = {}
    for entry in entries:
        if isinstance(entry, str):
            name = spec = entry
        elif isinstance(entry, dict) and set(entry) == {"name", "spec"}:
            name, spec = entry["name"], entry["spec"]
        else:
            raise ValueError("each function must be a name or an object with 'name' and 'spec'")

        if not isinstance(name, str) or not FUNCTION_NAME.fullmatch(name) or name in RESERVED_NAMES:
            raise ValueError(f"invalid function name {name!r}")
        if not isinstance(spec, str) or spec not in FUNCTION_SPECS:
            raise ValueError(f"no functional spec for {spec!r}; choose from {', '.join(FUNCTION_SPECS)}")
        if name in functions:
            raise ValueError(f"duplicate function name {name!r}")
        functions[name] = spec
    return functions


def resolve_models(selection):
    if isinstance(selection, str):
        selection = [selection]
    if not isinstance(selection, list) or not selection:
        raise ValueError("'consistency' must be a model name or a nonempty list of model names")

    models = {}
    for name in selection:
        if not isinstance(name, str) or name not in MODELS:
            raise ValueError("consistency models must be chosen from " + ", ".join(MODELS))
        if name in models:
            raise ValueError(f"duplicate consistency model {name!r}")
        models[name] = MODELS[name]
    return models.values()


def render_method(name, spec):
    args, variant, inputs, result, reply = FUNCTION_SPECS[spec]
    args = args.format(key="K", value="V")
    result = result.format(value="V")
    return f"""
    fn {name}(&mut self, {args}){result}
        requires
            valid_history(old(self).history()),
        ensures
            // The handle keeps its store and session.
            final(self).store_id() == old(self).store_id(),
            final(self).session_id() == old(self).session_id(),
            // Match the operation and its actual reply in the shared history.
            records_call_since(
                old(self).history(),
                final(self).history(),
                old(self).session_id(),
                Op::{variant}({inputs}),
                {reply},
            ),
            // Check the selected consistency guarantees over the whole prefix.
            valid_history(final(self).history()),
    ;
"""


def render_api(functions, models):
    methods = "".join(render_method(name, spec) for name, spec in functions.items())
    operations = dict.fromkeys(functions.values())
    history_imports = "records_call_since, unused_session, History"
    model_imports = "\n".join(
        f"#[cfg(verus_only)]\nuse dbspec::consistency::{module}::{predicate};"
        for module, predicate in models
    )
    conditions = [
        f"    &&& {predicate}(history, Map::empty())" for _, predicate in models
    ]
    allowlist = ""
    if len(operations) < len(FUNCTION_SPECS):
        history_imports += ", Event"
        selected = " | ".join(f"Op::{FUNCTION_SPECS[spec][1]}(..)" for spec in operations)
        allowlist = f"""
    // Each recorded invocation uses an operation selected by the recipe.
    &&& forall |i: int| 0 <= i < history.len() ==> match #[trigger] history[i] {{
        Event::Invoke {{ op, .. }} => matches!(op, {selected}),
        Event::Respond {{ .. }} => true,
    }}"""
    checks = "\n".join(conditions)
    return f"""// Generated by tools/compose.py.

#[cfg(verus_only)]
use dbspec::consistency::history::{{{history_imports}}};
{model_imports}
#[cfg(verus_only)]
use dbspec::functional::{{Op, Reply}};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {{

/// Checks the selected models against the same history from an initially empty store.
pub open spec fn valid_history<K, V>(history: History<K, V>) -> bool {{
{checks}{allowlist}
}}

/// One client session on a store. Separate sessions can access the store concurrently.
pub trait KvStore<K, V>: Sized {{
    spec fn store_id(&self) -> Loc;
    spec fn session_id(&self) -> nat;

    /// A prefix of this store's shared invocation and response history.
    spec fn history(&self) -> History<K, V>;

    fn new() -> (handle: Self)
        ensures
            handle.history() == Seq::empty(),
            valid_history(handle.history()),
    ;

    /// Create a separate session on the same store, starting from this snapshot.
    fn open_session(&self) -> (handle: Self)
        requires valid_history(self.history()),
        ensures
            handle.store_id() == self.store_id(),
            handle.session_id() != self.session_id(),
            handle.history() == self.history(),
            unused_session(handle.history(), handle.session_id()),
            valid_history(handle.history()),
    ;
{methods}}}

}}
"""


def compose(recipe):
    """Resolve the recipe and return a Verus module with the composed contracts."""
    if not isinstance(recipe, dict) or set(recipe) != {"functions", "consistency"}:
        raise ValueError("expected an object with exactly 'functions' and 'consistency'")
    functions = resolve_functions(recipe["functions"])
    models = resolve_models(recipe["consistency"])
    return render_api(functions, models)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("recipe", type=Path, help="JSON file with 'functions' and 'consistency'")
    parser.add_argument("-o", "--output", type=Path, help="write the API to a file; defaults to stdout")
    args = parser.parse_args()

    try:
        if args.output is not None and args.output.resolve() == args.recipe.resolve():
            raise ValueError("the output path must differ from the recipe path")
        with args.recipe.open(encoding="utf-8") as recipe_file:
            api = compose(json.load(recipe_file))
        if args.output is None:
            print(api, end="")
        else:
            args.output.write_text(api, encoding="utf-8")
    except (OSError, ValueError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
