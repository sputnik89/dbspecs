//! Causal consistency with a separate view for each operation.

#[cfg(verus_only)]
use crate::consistency::history::{responds_to, well_formed, Event, History};
#[cfg(verus_only)]
use crate::consistency::replay::{legal_replay, ReplayEntry};
use vstd::prelude::*;

verus! {

/// The selected calls are keyed by invocation ID. All completed calls keep their recorded
/// replies. Pending calls can be omitted or included with a proposed reply.
pub open spec fn causal_calls_match_history<K, V>(
    history: History<K, V>,
    calls: Map<nat, ReplayEntry<K, V>>,
) -> bool {
    // Validate call pairing and session order before selecting calls.
    &&& well_formed(history)
    // Each map entry identifies an actual invocation by its original ID.
    &&& forall |id: nat| #[trigger] calls.contains_key(id) ==> {
        let invocation = calls[id].invocation;
        invocation is Invoke && invocation.id() == id && history.contains(invocation)
    }
    // Every invocation with a response must appear with that recorded reply.
    &&& forall |i: int, r: int| #[trigger] responds_to(history, i, r) ==> {
        let id = history[i].id();
        // Keep the original invocation and the reply recorded for it.
        &&& calls.contains_key(id)
        &&& calls[id].invocation == history[i]
        &&& match history[r] {
            Event::Respond { reply, .. } => calls[id].reply == reply,
            Event::Invoke { .. } => false,
        }
    }
}

/// A legal replay of exactly this call's causal predecessors followed by the call itself.
/// The final reply must match the selected call. Earlier replies are local to the view.
pub open spec fn valid_causal_view<K, V>(
    initial: Map<K, V>,
    calls: Map<nat, ReplayEntry<K, V>>,
    causal_order: Set<(nat, nat)>,
    target: nat,
    view: Seq<ReplayEntry<K, V>>,
) -> bool {
    // The target must be one of the selected calls.
    &&& calls.contains_key(target)
    // There must be a final entry to check.
    &&& view.len() > 0
    // The final entry fixes both the target invocation and its expected reply.
    &&& view.last() == calls[target]
    // The sequential KV spec must produce the replies shown in the view.
    &&& legal_replay(initial, view)
    // Every earlier entry must use the original invocation of a selected causal predecessor.
    &&& forall |p: int| 0 <= p < view.len() - 1 ==> {
        let invocation = #[trigger] view[p].invocation;
        let id = invocation.id();
        &&& calls.contains_key(id)
        &&& calls[id].invocation == invocation
        &&& causal_order.contains((id, target))
    }
    // Every causal predecessor must appear before the target.
    &&& forall |id: nat| #[trigger] causal_order.contains((id, target))
        ==> calls.contains_key(id) && (exists |p: int| #![trigger view[p]]
            0 <= p < view.len() - 1 && view[p].invocation == calls[id].invocation)
    // Each call appears once, and the replay must respect causal order.
    &&& forall |p: int, q: int| #![trigger view[p], view[q]]
        0 <= p < q < view.len() ==> {
            let first = view[p].invocation.id();
            let second = view[q].invocation.id();
            first != second && !causal_order.contains((second, first))
        }
}

/// Session order is part of the strict causal order. Each reply is explained by its own view.
pub open spec fn valid_causal_execution<K, V>(
    history: History<K, V>,
    initial: Map<K, V>,
    calls: Map<nat, ReplayEntry<K, V>>,
    causal_order: Set<(nat, nat)>,
) -> bool {
    // Use only calls from the history and preserve every completed call's reply.
    &&& causal_calls_match_history(history, calls)
    // Each edge connects two distinct selected calls.
    &&& forall |a: nat, b: nat| #[trigger] causal_order.contains((a, b))
        ==> a != b && calls.contains_key(a) && calls.contains_key(b)
    // A call inherits the causal predecessors of all its predecessors.
    &&& forall |a: nat, b: nat, c: nat|
        #![trigger causal_order.contains((a, b)), causal_order.contains((b, c))]
        causal_order.contains((a, b)) && causal_order.contains((b, c))
            ==> causal_order.contains((a, c))
    // Selected calls in the same session keep their invocation order.
    &&& forall |i: int, j: int| #![trigger history[i], history[j]]
        0 <= i < j < history.len() && history[i].same_session(history[j])
            && calls.contains_key(history[i].id()) && calls.contains_key(history[j].id())
            ==> causal_order.contains((history[i].id(), history[j].id()))
    // Every selected call needs a legal view that explains its reply.
    &&& forall |id: nat| #[trigger] calls.contains_key(id)
        ==> exists |view: Seq<ReplayEntry<K, V>>| valid_causal_view(
            initial, calls, causal_order, id, view,
        )
}

/// Causal sources are inferred by replay. A Get can see the initial binding or an update
/// to its key in its causal past, including a Delete that removes the binding.
pub open spec fn causally_consistent<K, V>(history: History<K, V>, initial: Map<K, V>) -> bool {
    exists |calls: Map<nat, ReplayEntry<K, V>>, causal_order: Set<(nat, nat)>|
        valid_causal_execution(history, initial, calls, causal_order)
}

}
