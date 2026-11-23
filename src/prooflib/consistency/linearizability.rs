//! Reusable lemmas about SpecLib's finite-history linearizability predicate.

#[cfg(verus_only)]
use crate::consistency::history::History;
#[cfg(verus_only)]
use crate::consistency::linearizability::{linearizable, valid_linearization};
use vstd::prelude::*;

verus! {

/// The empty client history is valid for any initial map.
pub proof fn linearizable_empty<K, V>(initial: Map<K, V>)
    ensures linearizable(Seq::empty(), initial),
{
    let history: History<K, V> = Seq::empty();
    assert(valid_linearization(history, initial, Seq::empty()));
}

}
