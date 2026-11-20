//! Linearizability of finite histories against the sequential KV specification.

#[cfg(verus_only)]
use crate::consistency::history::{precedes, History};
#[cfg(verus_only)]
use crate::consistency::replay::valid_replay;
#[cfg(verus_only)]
pub use crate::consistency::replay::legal_replay;
pub use crate::consistency::replay::ReplayEntry;
use vstd::prelude::*;

verus! {

/// Checks a proposed order against the history and the initial KV state.
pub open spec fn valid_linearization<K, V>(
    history: History<K, V>,
    initial: Map<K, V>,
    order: Seq<ReplayEntry<K, V>>,
) -> bool {
    // The order must explain the recorded replies and replay legally from the initial state.
    &&& valid_replay(history, initial, order)
    // If one replayed call returned before another started, it must come first.
    &&& forall |i: int, j: int, p: int, q: int|
        #![trigger precedes(history, i, j), order[p], order[q]]
        precedes(history, i, j) && 0 <= p < order.len() && 0 <= q < order.len()
            && order[p].invocation == history[i] && order[q].invocation == history[j]
            ==> p < q
}

/// A history is linearizable when some order of its operations is a valid witness.
pub open spec fn linearizable<K, V>(history: History<K, V>, initial: Map<K, V>) -> bool {
    exists |order: Seq<ReplayEntry<K, V>>| valid_linearization(history, initial, order)
}

}
