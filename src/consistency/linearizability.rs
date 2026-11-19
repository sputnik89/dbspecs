//! Linearizability of finite histories against the sequential KV specification.

#[cfg(verus_only)]
use crate::consistency::history::{precedes, responds_to, well_formed, Event, History};
#[cfg(verus_only)]
use crate::functional::step;
use crate::functional::Reply;
use vstd::prelude::*;

verus! {

/// A witness entry identifies a call by its invocation index in the original history.
/// Its reply is the recorded response for a completed call or a proposed reply for a pending one.
pub ghost struct LinearizedOp<V> {
    pub invocation: int,
    pub reply: Reply<V>,
}

/// Replaying the witness from the initial state produces all of its replies.
pub open spec fn legal_replay<K, V>(
    history: History<K, V>,
    state: Map<K, V>,
    order: Seq<LinearizedOp<V>>,
) -> bool
    decreases order.len(),
{
    if order.len() == 0 {
        true
    } else {
        let entry = order[0];
        &&& 0 <= entry.invocation < history.len()
        &&& match history[entry.invocation] {
            Event::Invoke { op, .. } => {
                let (next, reply) = step(state, op);
                reply == entry.reply && legal_replay(history, next, order.skip(1))
            },
            Event::Respond { .. } => false,
        }
    }
}

/// Checks a proposed order against the history and the initial KV state.
pub open spec fn valid_linearization<K, V>(
    history: History<K, V>,
    initial: Map<K, V>,
    order: Seq<LinearizedOp<V>>,
) -> bool {
    &&& well_formed(history)
    &&& legal_replay(history, initial, order)
    // Every completed call appears with its recorded reply.
    &&& forall |i: int, r: int| #[trigger] responds_to(history, i, r)
        ==> exists |p: int| #![trigger order[p]]
            0 <= p < order.len() && order[p].invocation == i
                && match history[r] {
                    Event::Respond { reply, .. } => order[p].reply == reply,
                    Event::Invoke { .. } => false,
                }
    // Each invocation appears at most once, including pending calls.
    &&& forall |p: int, q: int| #![trigger order[p], order[q]]
        0 <= p < q < order.len() ==> order[p].invocation != order[q].invocation
    // The witness preserves response-before-invocation precedence.
    &&& forall |p: int, q: int| #![trigger order[p], order[q]]
        0 <= p < q < order.len() ==> !precedes(history, order[q].invocation, order[p].invocation)
}

/// A history is linearizable when some order of its operations is a valid witness.
pub open spec fn linearizable<K, V>(history: History<K, V>, initial: Map<K, V>) -> bool {
    exists |order: Seq<LinearizedOp<V>>| valid_linearization(history, initial, order)
}

}
