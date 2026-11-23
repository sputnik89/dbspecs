//! Sequential consistency of finite histories.

#[cfg(verus_only)]
use crate::consistency::history::History;
#[cfg(verus_only)]
use crate::consistency::replay::{valid_replay, ReplayEntry};
use vstd::prelude::*;

verus! {

/// Checks that the order replays legally and preserves each session's invocation order.
pub open spec fn valid_sequential_order<K, V>(
    history: History<K, V>,
    initial: Map<K, V>,
    order: Seq<ReplayEntry<K, V>>,
) -> bool {
    // The order must explain the recorded replies and replay legally from the initial state.
    &&& valid_replay(history, initial, order)
    // Replayed calls from the same session must keep their original invocation order.
    &&& forall |i: int, j: int, p: int, q: int|
        #![trigger history[i], history[j], order[p], order[q]]
        0 <= i < j < history.len() && history[i].same_session(history[j])
            && 0 <= p < order.len() && 0 <= q < order.len()
            && order[p].invocation == history[i] && order[q].invocation == history[j]
            ==> p < q
}

/// A history is sequentially consistent if some replay preserves session order.
pub open spec fn sequentially_consistent<K, V>(history: History<K, V>, initial: Map<K, V>) -> bool {
    exists |order: Seq<ReplayEntry<K, V>>| valid_sequential_order(history, initial, order)
}

/// The empty client history is valid for any initial map.
pub proof fn sequentially_consistent_empty<K, V>(initial: Map<K, V>)
    ensures sequentially_consistent(Seq::empty(), initial),
{
    let history: History<K, V> = Seq::empty();
    assert(valid_sequential_order(history, initial, Seq::empty()));
}

}
