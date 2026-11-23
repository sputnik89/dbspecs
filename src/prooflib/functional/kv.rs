//! Basic Map laws, recovered from src/functional/mod.rs at commit 17e42f3.
//! Their contracts and proofs are unchanged; their new home is ProofLib.

#[cfg(verus_only)]
use crate::functional::{delete, get, put};
use vstd::prelude::*;

verus! {

/// A lookup after Put returns the newly written value.
pub proof fn get_after_put<K, V>(state: Map<K, V>, key: K, value: V)
    ensures
        get(put(state, key, value), key) == Some(value),
{
}

/// A lookup after Delete reports the key as absent.
pub proof fn get_after_delete<K, V>(state: Map<K, V>, key: K)
    ensures
        get(delete(state, key), key) == None::<V>,
{
}

/// Put leaves the lookup result for a distinct key unchanged, including when it is absent.
pub proof fn put_preserves_other_key<K, V>(state: Map<K, V>, key: K, other: K, value: V)
    requires
        key != other,
    ensures
        get(put(state, key, value), other) == get(state, other),
{
}

/// Delete leaves the lookup result for a distinct key unchanged, including when it is absent.
pub proof fn delete_preserves_other_key<K, V>(state: Map<K, V>, key: K, other: K)
    requires
        key != other,
    ensures
        get(delete(state, key), other) == get(state, other),
{
}

}
