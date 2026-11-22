//! Finite client histories with at most one outstanding operation per session.

use crate::functional::{Op, Reply};
use vstd::prelude::*;

verus! {

pub ghost enum Event<K, V> {
    Invoke { id: nat, session: nat, op: Op<K, V> },
    Respond { id: nat, reply: Reply<V> },
}

pub type History<K, V> = Seq<Event<K, V>>;

impl<K, V> Event<K, V> {
    pub open spec fn id(self) -> nat {
        match self {
            Event::Invoke { id, .. } | Event::Respond { id, .. } => id,
        }
    }

    /// Only invocations carry session IDs.
    pub open spec fn same_session(self, other: Self) -> bool {
        match (self, other) {
            (Event::Invoke { session: first, .. }, Event::Invoke { session: second, .. }) =>
                first == second,
            _ => false,
        }
    }
}

/// Both arguments are event indices. A response matches an earlier invocation by ID.
pub open spec fn responds_to<K, V>(history: History<K, V>, invocation: int, response: int) -> bool {
    // Both events must be in bounds, with the response after the invocation.
    &&& 0 <= invocation < response < history.len()
    // The earlier event starts the call.
    &&& history[invocation] is Invoke
    // The later event returns from a call.
    &&& history[response] is Respond
    // Both events must refer to the same call.
    &&& history[invocation].id() == history[response].id()
}

/// Preserve the earlier history and append exactly this request and its reply.
pub open spec fn records_call<K, V>(
    before: History<K, V>,
    after: History<K, V>,
    operation: Op<K, V>,
    response: Reply<V>,
) -> bool {
    let invocation = before.len() as int;
    let reply_index = invocation + 1;
    // The recorded call adds exactly two events and preserves all earlier events.
    &&& after.len() == before.len() + 2
    &&& after.take(invocation) =~= before
    // The new events share a call ID and contain the operation and reply for this method.
    &&& responds_to(after, invocation, reply_index)
    &&& match (after[invocation], after[reply_index]) {
        (Event::Invoke { op, .. }, Event::Respond { reply, .. }) =>
            op == operation && reply == response,
        _ => false,
    }
}

/// A snapshot taken at this call's return extends the handle's previous snapshot.
pub open spec fn records_call_since<K, V>(
    before: History<K, V>,
    after: History<K, V>,
    session: nat,
    op: Op<K, V>,
    reply: Reply<V>,
) -> bool {
    // Preserve every event the handle has already observed.
    &&& before.len() + 2 <= after.len()
    &&& after.take(before.len() as int) == before
    // Match this invocation to the returned reply. Other sessions' events can intervene.
    &&& exists |i: int| #![trigger after[i]]
        before.len() <= i < after.len() - 1
            && (match after[i] {
                Event::Invoke { id, session: caller, op: called } =>
                    caller == session && called == op && after.last() == (Event::Respond { id, reply }),
                Event::Respond { .. } => false,
            })
            && (forall |j: int| #![trigger after[j]]
                before.len() <= j < after.len() && after[j].same_session(after[i]) ==> j == i)
}

/// The snapshot contains no invocation by the newly created session.
pub open spec fn unused_session<K, V>(history: History<K, V>, session: nat) -> bool {
    forall |i: int| 0 <= i < history.len() ==> match #[trigger] history[i] {
        Event::Invoke { session: recorded, .. } => recorded != session,
        Event::Respond { .. } => true,
    }
}

/// Both arguments are invocation indices. The first call returns before the second starts.
pub open spec fn precedes<K, V>(history: History<K, V>, first: int, second: int) -> bool {
    // The second call must start at an actual event in the history.
    &&& 0 <= second < history.len()
    &&& history[second] is Invoke
    // The first call must have a matching response before the second starts.
    &&& exists |r: int| #[trigger] responds_to(history, first, r) && r < second
}

/// Checks call pairing and session order. A finite prefix may end with pending calls.
pub open spec fn well_formed<K, V>(history: History<K, V>) -> bool {
    // A repeated ID can only pair one invocation with one later response.
    &&& forall |i: int, j: int| #![trigger history[i], history[j]]
        0 <= i < j < history.len() && history[i].id() == history[j].id()
            ==> (history[i] is Invoke && history[j] is Respond)
    // Each response belongs to a call. Invocations may remain pending.
    &&& forall |r: int| #![trigger history[r]]
        0 <= r < history.len() && history[r] is Respond
            ==> exists |i: int| #[trigger] responds_to(history, i, r)
    // A session must finish its previous call before starting another.
    &&& forall |i: int, j: int| #![trigger history[i], history[j]]
        0 <= i < j < history.len() && history[i].same_session(history[j])
            ==> precedes(history, i, j)
}

}
