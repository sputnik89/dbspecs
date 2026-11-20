//! Sequential replay and history matching shared by consistency models.

use crate::consistency::history::Event;
#[cfg(verus_only)]
use crate::consistency::history::{responds_to, well_formed, History};
use crate::functional::Reply;
#[cfg(verus_only)]
use crate::functional::step;
use vstd::prelude::*;

verus! {

/// A witness entry carries the full invocation event from the original history.
/// Its reply is the recorded response for a completed call or a proposed reply for a pending one.
pub ghost struct ReplayEntry<K, V> {
    pub invocation: Event<K, V>,
    pub reply: Reply<V>,
}

/// Replaying the witness from the initial state produces all of its replies.
pub open spec fn legal_replay<K, V>(
    state: Map<K, V>,
    order: Seq<ReplayEntry<K, V>>,
) -> bool
    decreases order.len(),
{
    if order.len() == 0 {
        // An empty suffix has no replies left to check.
        true
    } else {
        let entry = order[0];
        match entry.invocation {
            Event::Invoke { op, .. } => {
                let (next, reply) = step(state, op);
                // Check this call's reply, then replay the rest from its resulting state.
                reply == entry.reply && legal_replay(next, order.skip(1))
            },
            // Only invocation events supply an operation to replay.
            Event::Respond { .. } => false,
        }
    }
}

/// Checks which calls and replies the order contains, and whether it replays legally.
pub open spec fn valid_replay<K, V>(
    history: History<K, V>,
    initial: Map<K, V>,
    order: Seq<ReplayEntry<K, V>>,
) -> bool {
    // The history must pair calls correctly and keep at most one open call per session.
    &&& well_formed(history)
    // The sequential KV spec must produce every reply in the proposed order.
    &&& legal_replay(initial, order)
    // Every replayed invocation comes from the original history.
    &&& forall |p: int| 0 <= p < order.len() ==> history.contains(#[trigger] order[p].invocation)
    // Every completed call appears with its recorded reply.
    &&& forall |i: int, r: int| #[trigger] responds_to(history, i, r)
        ==> exists |p: int| #![trigger order[p]]
            0 <= p < order.len() && order[p].invocation == history[i]
                && match history[r] {
                    Event::Respond { reply, .. } => order[p].reply == reply,
                    Event::Invoke { .. } => false,
                }
    // Each invocation appears at most once, including pending calls.
    &&& forall |p: int, q: int| #![trigger order[p], order[q]]
        0 <= p < q < order.len() ==> order[p].invocation != order[q].invocation
}

}
