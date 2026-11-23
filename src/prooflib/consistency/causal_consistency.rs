//! Reusable lemmas about SpecLib's causal consistency predicate.

#[cfg(verus_only)]
use crate::consistency::history::History;
#[cfg(verus_only)]
use crate::consistency::causal_consistency::{causally_consistent, valid_causal_execution};
use vstd::prelude::*;

verus! {

/// The empty client history is valid for any initial map.
pub proof fn causally_consistent_empty<K, V>(initial: Map<K, V>)
    ensures causally_consistent(Seq::empty(), initial),
{
    let history: History<K, V> = Seq::empty();
    assert(valid_causal_execution(history, initial, Map::empty(), Set::empty()));
}

}
