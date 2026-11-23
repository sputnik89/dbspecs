//! Replay facts shared by consistency proofs.

#[cfg(verus_only)]
use crate::consistency::history::Event;
#[cfg(verus_only)]
use crate::consistency::replay::{legal_replay, ReplayEntry};
#[cfg(verus_only)]
use crate::functional::step;
use vstd::prelude::*;

verus! {

/// Any entry of a legal sequential replay is an invocation, not a response.
/// Moved from consistency/tests.rs at commit 30acc2e; made public for reuse.
pub proof fn replay_entry_is_invocation<K, V>(initial: Map<K, V>, order: Seq<ReplayEntry<K, V>>, i: int)
    requires
        0 <= i < order.len(),
        legal_replay(initial, order),
    ensures
        order[i].invocation is Invoke,
    decreases order.len(),
{
    reveal(legal_replay);
    match order[0].invocation {
        Event::Invoke { op, .. } => {
            if i > 0 {
                replay_entry_is_invocation(step(initial, op).0, order.skip(1), i - 1);
            }
        },
        Event::Respond { .. } => {},
    }
}

}
