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
    &&& 0 <= invocation < response < history.len()
    &&& history[invocation] is Invoke
    &&& history[response] is Respond
    &&& history[invocation].id() == history[response].id()
}

/// Both arguments are invocation indices. The first call returns before the second starts.
pub open spec fn precedes<K, V>(history: History<K, V>, first: int, second: int) -> bool {
    &&& 0 <= second < history.len()
    &&& history[second] is Invoke
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
