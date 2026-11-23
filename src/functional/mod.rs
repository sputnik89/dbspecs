//! Sequential specifications for a single-key KV store.

use vstd::prelude::*;

verus! {

pub enum Op<K, V> {
    Get(K),
    Put(K, V),
    Delete(K),
}

pub enum Reply<V> {
    Value(Option<V>),
    Ack,
}

/// Returns the value bound to `key`, or `None` if the key is absent.
pub open spec fn get<K, V>(state: Map<K, V>, key: K) -> Option<V> {
    if state.contains_key(key) {
        Some(state[key])
    } else {
        None
    }
}

/// Inserts a new binding or replaces the existing binding for `key`.
pub open spec fn put<K, V>(state: Map<K, V>, key: K, value: V) -> Map<K, V> {
    state.insert(key, value)
}

/// Removes the binding for `key` if present.
pub open spec fn delete<K, V>(state: Map<K, V>, key: K) -> Map<K, V> {
    state.remove(key)
}

/// Applies one operation and returns the resulting state and reply.
pub open spec fn step<K, V>(state: Map<K, V>, op: Op<K, V>) -> (Map<K, V>, Reply<V>) {
    match op {
        Op::Get(key) => (state, Reply::Value(get(state, key))),
        Op::Put(key, value) => (put(state, key, value), Reply::Ack),
        Op::Delete(key) => (delete(state, key), Reply::Ack),
    }
}

}
