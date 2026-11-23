//! Reusable lemmas about SpecLib's sequential consistency predicate.

#[cfg(verus_only)]
use crate::consistency::history::History;
#[cfg(verus_only)]
use crate::consistency::sequential_consistency::{sequentially_consistent, valid_sequential_order};
use vstd::prelude::*;

verus! {

/// The empty client history is valid for any initial map.
pub proof fn sequentially_consistent_empty<K, V>(initial: Map<K, V>)
    ensures sequentially_consistent(Seq::empty(), initial),
{
    let history: History<K, V> = Seq::empty();
    assert(valid_sequential_order(history, initial, Seq::empty()));
}

}
