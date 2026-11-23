//! Refinement proof for the example's linearizable map.

#![cfg_attr(not(verus_only), allow(dead_code))]

#[cfg(verus_only)]
use crate::api;
#[cfg(verus_only)]
use dbspec::consistency::history::{precedes, records_call_since, responds_to, well_formed, Event};
use dbspec::consistency::history::History;
#[cfg(verus_only)]
use dbspec::consistency::linearizability::{linearizable, valid_linearization};
#[cfg(verus_only)]
use dbspec::consistency::replay::{legal_replay, valid_replay};
use dbspec::consistency::replay::ReplayEntry;
#[cfg(verus_only)]
use dbspec::functional::step;
use dbspec::functional::{Op, Reply};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
#[cfg(verus_only)]
use vstd::invariant::OpenInvariantCredit;
use vstd::prelude::*;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
use vstd::resource::map::{GhostMapAuth, GhostPointsTo};
use vstd::resource::Loc;

verus! {

pub(crate) type CallTicket<K, V> = GhostPointsTo<int, (Op<K, V>, Option<Reply<V>>, nat)>;
type SessionState<K, V> = (History<K, V>, Option<int>);
pub(crate) type SessionTicket<K, V> = GhostPointsTo<nat, SessionState<K, V>>;

// A session has observed a prefix, with at most its current call starting beyond it.
spec fn session_snapshot<K, V>(
    history: History<K, V>, session: nat, state: SessionState<K, V>,
) -> bool {
    let (snapshot, pending) = state;
    &&& snapshot.len() <= history.len()
    &&& history.take(snapshot.len() as int) == snapshot
    &&& pending is Some ==> snapshot.len() <= pending->Some_0 < history.len()
    &&& forall |i: int| snapshot.len() <= i < history.len() ==> match #[trigger] history[i] {
        Event::Invoke { session: caller, .. } => caller == session ==> pending == Some(i),
        Event::Respond { .. } => true,
    }
}

proof fn extend_snapshot<K, V>(
    history: History<K, V>, event: Event<K, V>, session: nat, state: SessionState<K, V>,
)
    requires
        session_snapshot(history, session, state),
        event is Invoke ==> event->Invoke_session != session,
    ensures
        session_snapshot(history.push(event), session, state),
{
    assert(history.push(event).take(state.0.len() as int) =~= history.take(state.0.len() as int));
}

spec fn pending_invocation<K, V>(history: History<K, V>, i: int) -> bool {
    &&& 0 <= i < history.len()
    &&& history[i] is Invoke
    &&& !(exists |r: int| #[trigger] responds_to(history, i, r))
}

/// Replaying the chosen order reaches exactly this map state and produces every reply.
spec fn replay_reaches<K, V>(
    initial: Map<K, V>, order: Seq<ReplayEntry<K, V>>, state: Map<K, V>,
) -> bool
    decreases order.len(),
{
    if order.len() == 0 {
        initial == state
    } else if let Event::Invoke { op, .. } = order[0].invocation {
        let (next, reply) = step(initial, op);
        reply == order[0].reply && replay_reaches(next, order.skip(1), state)
    } else {
        false
    }
}

proof fn replay_append<K, V>(
    initial: Map<K, V>, order: Seq<ReplayEntry<K, V>>, state: Map<K, V>, entry: ReplayEntry<K, V>,
    op: Op<K, V>,
)
    requires
        replay_reaches(initial, order, state),
        entry.invocation is Invoke,
        entry.invocation->Invoke_op == op,
        step(state, op).1 == entry.reply,
    ensures
        replay_reaches(initial, order.push(entry), step(state, op).0),
        legal_replay(initial, order.push(entry)),
    decreases order.len(),
{
    reveal_with_fuel(replay_reaches, 2);
    reveal_with_fuel(legal_replay, 2);
    let extended = order.push(entry);
    assert(extended.len() > 0);
    if order.len() == 0 {
        assert(order =~= Seq::empty());
        assert(initial == state);
        assert(extended[0] == entry);
        assert(extended.skip(1) =~= Seq::empty());
    } else {
        let head = order[0].invocation->Invoke_op;
        assert(extended[0] == order[0]);
        assert(extended.skip(1) =~= order.skip(1).push(entry));
        replay_append(step(initial, head).0, order.skip(1), state, entry, op);
    }
}

tracked struct CallHistory<K, V> {
    ghost history: History<K, V>,
    ghost order: Seq<ReplayEntry<K, V>>,
    ghost state: Map<K, V>,
    tickets: GhostMapAuth<int, (Op<K, V>, Option<Reply<V>>, nat)>,
    sessions: GhostMapAuth<nat, SessionState<K, V>>,
    ghost next_session: nat,
}

impl<K, V> CallHistory<K, V> {
    spec fn id(self) -> Loc { self.tickets.id() }
    spec fn events(self) -> History<K, V> { self.history }
    spec fn state(self) -> Map<K, V> { self.state }

    spec fn pending(self, i: int, op: Op<K, V>, reply: Option<Reply<V>>, session: nat) -> bool {
        &&& 0 <= i < self.history.len()
        &&& self.history[i] is Invoke
        &&& self.history[i].id() == i
        &&& self.history[i]->Invoke_op == op
        &&& self.history[i]->Invoke_session == session
        &&& forall |r: int| !#[trigger] responds_to(self.history, i, r)
        &&& match reply {
            None => forall |p: int| 0 <= p < self.order.len()
                ==> (#[trigger] self.order[p]).invocation != self.history[i],
            Some(reply) => exists |p: int| 0 <= p < self.order.len()
                && #[trigger] self.order[p] == (ReplayEntry { invocation: self.history[i], reply }),
        }
    }

    spec fn valid(self) -> bool {
        &&& valid_linearization(self.history, Map::empty(), self.order)
        &&& replay_reaches(Map::empty(), self.order, self.state)
        &&& forall |i: int| 0 <= i < self.history.len() ==> {
            let event = #[trigger] self.history[i];
            &&& event.id() <= i
            &&& event is Invoke ==> (event.id() == i && event->Invoke_session < self.next_session)
        }
        &&& forall |i: int| #[trigger] self.tickets@.contains_key(i)
            ==> self.pending(i, self.tickets@[i].0, self.tickets@[i].1, self.tickets@[i].2)
        &&& forall |session: nat| #[trigger] self.sessions@.contains_key(session)
            ==> session < self.next_session
                && session_snapshot(self.history, session, self.sessions@[session])
        &&& forall |i: int| #[trigger] pending_invocation(self.history, i) ==> {
            let session = self.history[i]->Invoke_session;
            self.sessions@.contains_key(session) && self.sessions@[session].1 == Some(i)
        }
    }

    proof fn new() -> (tracked log: Self)
        ensures log.valid(), log.events().len() == 0, log.state() == Map::empty(),
    {
        let tracked (tickets, _) = GhostMapAuth::new(Map::empty());
        let tracked (sessions, _) = GhostMapAuth::new(Map::empty());
        Self {
            history: Seq::empty(), order: Seq::empty(), state: Map::empty(),
            tickets, sessions, next_session: 0,
        }
    }

    proof fn open_session(tracked &mut self) -> (tracked session: SessionTicket<K, V>)
        requires old(self).valid(),
        ensures
            final(self).valid(), final(self).id() == old(self).id(),
            final(self).sessions.id() == old(self).sessions.id(),
            final(self).state() == old(self).state(),
            session.id() == final(self).sessions.id(), session.value() == (Seq::empty(), None),
    {
        let ghost before = *self;
        let ghost id = self.next_session;
        assert(!self.sessions@.contains_key(id));
        let tracked session = self.sessions.insert(id, (Seq::empty(), None));
        self.next_session = id + 1;
        assert(self.history.take(0) =~= Seq::empty());
        assert forall |i: int| 0 <= i < self.history.len() && #[trigger] self.history[i] is Invoke
            implies self.history[i]->Invoke_session != id by {
            assert(before.history[i]->Invoke_session < id);
        }
        assert(session_snapshot(self.history, id, (Seq::empty(), None)));
        assert(self.valid());
        session
    }

    #[verifier::rlimit(30)]
    proof fn begin(
        tracked &mut self, tracked session: &mut SessionTicket<K, V>, op: Op<K, V>,
    ) -> (tracked ticket: CallTicket<K, V>)
        requires
            old(self).valid(),
            old(session).id() == old(self).sessions.id(),
            old(session).value().1 is None,
            api::selected_op(op),

        ensures
            final(self).valid(),
            final(self).id() == old(self).id(),
            ticket.id() == final(self).id(),
            ticket.key() == old(self).events().len(),
            ticket.value() == (op, None, final(session).key()),
            final(self).sessions.id() == old(self).sessions.id(),
            final(session).id() == old(session).id(), final(session).key() == old(session).key(),
            final(session).value() == (old(session).value().0, Some(ticket.key())),
            api::call_started(
                old(self).events(), final(self).events(), ticket.key() as nat, final(session).key(), op,
            ),
            final(self).state() == old(self).state(),
    {
        session.agree(&self.sessions);
        let ghost session_id = session.key();
        let ghost before = *self;
        let ghost i = self.history.len() as int;
        assert(!self.tickets@.contains_key(i));
        let tracked ticket = self.tickets.insert(i, (op, None, session_id));
        let ghost event = Event::Invoke { id: i as nat, session: session_id, op };
        let ghost snapshot = session.value().0;
        assert(session_snapshot(before.history, session_id, (snapshot, None)));
        self.history = self.history.push(event);
        session.update(&mut self.sessions, (snapshot, Some(i)));
        assert forall |owner: nat| #[trigger] self.sessions@.contains_key(owner)
            implies session_snapshot(self.history, owner, self.sessions@[owner]) by {
            if owner == session_id {
                assert(self.history.take(snapshot.len() as int) =~= snapshot);
            } else {
                extend_snapshot(before.history, event, owner, before.sessions@[owner]);
            }
        }
        assert forall |p: int| 0 <= p < self.order.len() implies
            self.history.contains(#[trigger] self.order[p].invocation) by {
            let index = choose |j: int| 0 <= j < before.history.len()
                && before.history[j] == self.order[p].invocation;
            assert(self.history[index] == self.order[p].invocation);
        }
        assert forall |j: int, r: int| #[trigger] responds_to(self.history, j, r)
            implies responds_to(before.history, j, r) by {}
        assert forall |j: int, r: int| #[trigger] responds_to(before.history, j, r)
            implies responds_to(self.history, j, r) by {}
        assert forall |p: int, q: int| #![trigger self.history[p], self.history[q]]
            0 <= p < q < self.history.len() && self.history[p].id() == self.history[q].id()
            implies self.history[p] is Invoke && self.history[q] is Respond by {
            assert(before.history[p].id() <= p);
            assert(q < i);
        }
        assert forall |p: int, q: int| #![trigger self.history[p], self.history[q]]
            0 <= p < q < self.history.len() && self.history[p].same_session(self.history[q])
            implies precedes(self.history, p, q) by {
            if q == i {
                assert(before.history[p]->Invoke_session == session_id);
                assert(!pending_invocation(before.history, p));
            } else {
                assert(precedes(before.history, p, q));
            }
            let r = choose |r: int| responds_to(before.history, p, r) && r < q;
            assert(responds_to(self.history, p, r));
        }
        assert(well_formed(self.history));
        assert(valid_replay(self.history, Map::empty(), self.order));
        assert forall |j: int, k: int, p: int, q: int|
            #![trigger precedes(self.history, j, k), self.order[p], self.order[q]]
            precedes(self.history, j, k) && 0 <= p < self.order.len() && 0 <= q < self.order.len()
                && self.order[p].invocation == self.history[j]
                && self.order[q].invocation == self.history[k]
            implies p < q by {
            let index = choose |t: int| 0 <= t < before.history.len()
                && before.history[t] == self.order[q].invocation;
            assert(before.history[index].id() <= index);
            assert(k < i);
            let r = choose |r: int| responds_to(self.history, j, r) && r < k;
            assert(responds_to(before.history, j, r));
            assert(precedes(before.history, j, k));
        }
        assert(valid_linearization(self.history, Map::empty(), self.order));
        assert forall |j: int| #[trigger] self.tickets@.contains_key(j)
            implies self.pending(j, self.tickets@[j].0, self.tickets@[j].1, self.tickets@[j].2) by {
            if j == i {
                assert forall |p: int| 0 <= p < self.order.len()
                    implies (#[trigger] self.order[p]).invocation != self.history[j] by {
                    let index = choose |t: int| 0 <= t < before.history.len()
                        && before.history[t] == self.order[p].invocation;
                    assert(before.history[index].id() <= index);
                }
            } else {
                assert(before.tickets@.contains_key(j));
                assert(before.pending(j, self.tickets@[j].0, self.tickets@[j].1, self.tickets@[j].2));
            }
        }
        assert forall |j: int| #[trigger] pending_invocation(self.history, j) implies {
            let owner = self.history[j]->Invoke_session;
            self.sessions@.contains_key(owner) && self.sessions@[owner].1 == Some(j)
        } by {
            if j != i {
                assert(pending_invocation(before.history, j));
                assert(before.history[j]->Invoke_session != session_id);
            }
        }
        assert(self.valid());
        ticket
    }

    proof fn apply(tracked &mut self, tracked ticket: &mut CallTicket<K, V>, reply: Reply<V>)
        requires
            old(self).valid(),
            old(ticket).id() == old(self).id(),
            old(ticket).value().1 is None,
            reply == step(old(self).state(), old(ticket).value().0).1,
        ensures
            final(self).valid(),
            final(self).id() == old(self).id(),
            final(self).events() == old(self).events(),
            final(self).state() == step(old(self).state(), old(ticket).value().0).0,
            final(ticket).id() == old(ticket).id(),
            final(ticket).key() == old(ticket).key(),
            final(ticket).value() == (old(ticket).value().0, Some(reply), old(ticket).value().2),
            final(self).sessions == old(self).sessions,
    {
        let ghost before = *self;
        ticket.agree(&self.tickets);
        let ghost i = ticket.key();
        let ghost op = ticket.value().0;
        assert(self.pending(i, op, None, ticket.value().2));
        let ghost entry = ReplayEntry { invocation: self.history[i], reply };
        replay_append(Map::empty(), self.order, self.state, entry, op);
        let ghost p = self.order.len() as int;
        self.order = self.order.push(entry);
        self.state = step(self.state, op).0;
        ticket.update(&mut self.tickets, (op, Some(reply), ticket.value().2));
        assert(self.history.contains(entry.invocation));
        assert forall |k: int| 0 <= k < self.order.len() implies
            self.history.contains(#[trigger] self.order[k].invocation) by {}
        assert forall |j: int, r: int| #[trigger] responds_to(self.history, j, r)
            implies exists |k: int| #![trigger self.order[k]]
                0 <= k < self.order.len() && self.order[k].invocation == self.history[j]
                    && self.order[k].reply == self.history[r]->Respond_reply by {
            let k = choose |k: int| 0 <= k < before.order.len() && (#[trigger] before.order[k]).invocation
                == self.history[j] && before.order[k].reply == self.history[r]->Respond_reply;
            assert(self.order[k] == before.order[k]);
        }
        assert forall |j: int, k: int| #![trigger self.order[j], self.order[k]]
            0 <= j < k < self.order.len() implies self.order[j].invocation != self.order[k].invocation by {
            if k == p {
                assert(before.order[j].invocation != before.history[i]);
            }
        }
        assert(valid_replay(self.history, Map::empty(), self.order));
        assert forall |j: int, k: int, a: int, b: int|
            #![trigger precedes(self.history, j, k), self.order[a], self.order[b]]
            precedes(self.history, j, k) && 0 <= a < self.order.len() && 0 <= b < self.order.len()
                && self.order[a].invocation == self.history[j]
                && self.order[b].invocation == self.history[k]
            implies a < b by {
            if a == p {
                assert(self.history[j].id() == i);
                assert(j == i);
                let r = choose |r: int| responds_to(self.history, j, r) && r < k;
                assert(!responds_to(self.history, i, r));
            }
        }
        assert(valid_linearization(self.history, Map::empty(), self.order));
        assert forall |j: int| #[trigger] self.tickets@.contains_key(j)
            implies self.pending(j, self.tickets@[j].0, self.tickets@[j].1, self.tickets@[j].2) by {
            if j == i {
                assert(self.order[p] == entry);
            } else {
                assert(before.tickets@.contains_key(j));
                assert(before.pending(j, self.tickets@[j].0, self.tickets@[j].1, self.tickets@[j].2));
                assert(self.history[j].id() != self.history[i].id());
                match self.tickets@[j].1 {
                    Some(previous) => {
                        let k = choose |k: int| 0 <= k < before.order.len()
                            && before.order[k] == (ReplayEntry { invocation: self.history[j], reply: previous });
                        assert(self.order[k] == before.order[k]);
                    },
                    None => {
                        assert forall |k: int| 0 <= k < self.order.len() implies
                            (#[trigger] self.order[k]).invocation != self.history[j] by {}
                    },
                }
            }
        }
        assert(self.valid());
    }

    proof fn finish(
        tracked &mut self, tracked session: &mut SessionTicket<K, V>, tracked ticket: CallTicket<K, V>,
    )
        requires
            old(self).valid(),
            ticket.id() == old(self).id(),
            ticket.value().1 is Some,
            old(session).id() == old(self).sessions.id(),
            old(session).value().1 == Some(ticket.key()),
            old(session).key() == ticket.value().2,
        ensures
            final(self).valid(),
            final(self).id() == old(self).id(),
            final(self).sessions.id() == old(self).sessions.id(),
            final(session).id() == old(session).id(), final(session).key() == old(session).key(),
            final(session).value() == (final(self).events(), None),
            api::call_finished(
                old(self).events(), final(self).events(), ticket.key() as nat, ticket.value().1->Some_0,
            ),
            final(self).state() == old(self).state(),
            records_call_since(
                old(session).value().0, final(self).events(), final(session).key(),
                ticket.value().0, ticket.value().1->Some_0,
            ),
    {
        session.agree(&self.sessions);
        let ghost before = *self;
        ticket.agree(&self.tickets);
        let ghost i = ticket.key();
        let ghost op = ticket.value().0;
        let ghost reply = ticket.value().1->Some_0;
        assert(self.pending(i, op, Some(reply), ticket.value().2));
        let ghost r = self.history.len() as int;
        self.tickets.delete_points_to(ticket);
        assert(pending_invocation(before.history, i));
        assert(before.history[i]->Invoke_session == session.key());
        let ghost owner = session.key();
        let ghost snapshot = session.value().0;
        let ghost event = Event::Respond { id: i as nat, reply };
        assert(session_snapshot(before.history, owner, (snapshot, Some(i))));
        self.history = self.history.push(event);
        session.update(&mut self.sessions, (self.history, None));
        assert forall |other: nat| #[trigger] self.sessions@.contains_key(other)
            implies session_snapshot(self.history, other, self.sessions@[other]) by {
            if other == owner {
                assert(self.history.take(self.history.len() as int) =~= self.history);
            } else {
                extend_snapshot(before.history, event, other, before.sessions@[other]);
            }
        }
        assert(snapshot.len() <= i < r);
        assert(self.history.take(snapshot.len() as int) =~= snapshot);
        assert forall |j: int| snapshot.len() <= j < self.history.len()
            && #[trigger] self.history[j].same_session(self.history[i]) implies j == i by {
            assert(j < r);
        }
        assert(records_call_since(snapshot, self.history, owner, op, reply));
        assert(responds_to(self.history, i, r));
        assert forall |j: int, k: int| #[trigger] responds_to(self.history, j, k)
            implies responds_to(before.history, j, k) || (j == i && k == r) by {}
        assert forall |j: int, k: int| #[trigger] responds_to(before.history, j, k)
            implies responds_to(self.history, j, k) by {}
        assert forall |j: int, k: int| #[trigger] precedes(self.history, j, k)
            implies precedes(before.history, j, k) by {
            let response_index = choose |t: int| responds_to(self.history, j, t) && t < k;
            assert(k < r);
            assert(responds_to(before.history, j, response_index));
        }
        assert forall |p: int| 0 <= p < self.order.len() implies
            self.history.contains(#[trigger] self.order[p].invocation) by {
            let index = choose |j: int| 0 <= j < before.history.len()
                && before.history[j] == self.order[p].invocation;
            assert(self.history[index] == self.order[p].invocation);
        }
        assert forall |j: int| #[trigger] self.tickets@.contains_key(j)
            implies self.pending(j, self.tickets@[j].0, self.tickets@[j].1, self.tickets@[j].2) by {
            assert(before.tickets@.contains_key(j));
            assert(before.pending(j, self.tickets@[j].0, self.tickets@[j].1, self.tickets@[j].2));
        }
        assert forall |j: int| #[trigger] pending_invocation(self.history, j) implies {
            let owner = self.history[j]->Invoke_session;
            self.sessions@.contains_key(owner) && self.sessions@[owner].1 == Some(j)
        } by {
            assert(j != i);
            assert(pending_invocation(before.history, j));
            assert(before.history[j]->Invoke_session != session.key());
        }
        assert(self.valid());
        assert(linearizable(self.history, Map::empty()));
        assert(api::valid_history(self.history));
    }
}

pub(crate) type StoreModel<K, V> = GhostVar<Map<K, V>>;

pub(crate) ghost struct HistoryIds {
    pub(crate) calls: Loc,
    pub(crate) sessions: Loc,
    pub(crate) model: Loc,
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub(crate) tracked struct Journal<K, V> {
    trace: CallHistory<K, V>,
    model: GhostVarAuth<Map<K, V>>,
}

pub(crate) struct JournalPredicate;

impl<K, V> InvariantPredicate<HistoryIds, Journal<K, V>> for JournalPredicate {
    closed spec fn inv(ids: HistoryIds, journal: Journal<K, V>) -> bool {
        &&& journal.trace.id() == ids.calls
        &&& journal.trace.sessions.id() == ids.sessions
        &&& journal.model.id() == ids.model
        &&& journal.trace.valid()
        &&& journal.model@ == journal.trace.state()
    }
}

pub(crate) type SharedHistory<K, V> = AtomicInvariant<HistoryIds, Journal<K, V>, JournalPredicate>;

pub(crate) proof fn new<K, V>() -> (tracked result: (SharedHistory<K, V>, StoreModel<K, V>))
    ensures
        result.0.constant().model == result.1.id(),
        result.1@ == Map::empty(),
        result.0.namespace() == 0,
{
    let tracked trace = CallHistory::new();
    let tracked (authority, model) = GhostVarAuth::new(Map::empty());
    let ghost ids = HistoryIds { calls: trace.id(), sessions: trace.sessions.id(), model: authority.id() };
    (SharedHistory::new(ids, Journal { trace, model: authority }, 0), model)
}

pub(crate) proof fn open_session<K, V>(
    tracked log: &SharedHistory<K, V>, tracked credit: OpenInvariantCredit,
) -> (tracked token: SessionTicket<K, V>)
    ensures token.id() == log.constant().sessions, token.value() == (Seq::empty(), None),
    opens_invariants [log.namespace()]
{
    let tracked token;
    vstd::invariant::open_atomic_invariant_in_proof!(credit => log => journal => {
        token = journal.trace.open_session();
    });
    token
}

pub(crate) proof fn begin<K, V>(
    tracked log: &SharedHistory<K, V>, tracked credit: OpenInvariantCredit,
    tracked session: &mut SessionTicket<K, V>, op: Op<K, V>,
) -> (tracked ticket: CallTicket<K, V>)
    requires
        old(session).id() == log.constant().sessions, old(session).value().1 is None,
        api::selected_op(op),
    ensures
        final(session).id() == old(session).id(), final(session).key() == old(session).key(),
        final(session).value() == (old(session).value().0, Some(ticket.key())),
        ticket.id() == log.constant().calls,
        ticket.value() == (op, None, final(session).key()),
    opens_invariants [log.namespace()]
{
    let tracked ticket;
    vstd::invariant::open_atomic_invariant_in_proof!(credit => log => journal => {
        ticket = journal.trace.begin(session, op);
    });
    ticket
}

/// The sample calls this while it holds the data lock, at the abstract map step.
pub(crate) proof fn apply<K, V>(
    tracked log: &SharedHistory<K, V>, tracked credit: OpenInvariantCredit,
    tracked model: &mut StoreModel<K, V>, tracked ticket: &mut CallTicket<K, V>, reply: Reply<V>,
)
    requires
        old(model).id() == log.constant().model,
        old(ticket).id() == log.constant().calls, old(ticket).value().1 is None,
        reply == step(old(model)@, old(ticket).value().0).1,
    ensures
        final(model).id() == old(model).id(),
        final(model)@ == step(old(model)@, old(ticket).value().0).0,
        final(ticket).id() == old(ticket).id(), final(ticket).key() == old(ticket).key(),
        final(ticket).value() == (old(ticket).value().0, Some(reply), old(ticket).value().2),
    opens_invariants [log.namespace()]
{
    vstd::invariant::open_atomic_invariant_in_proof!(credit => log => journal => {
        journal.model.agree(model);
        journal.trace.apply(ticket, reply);
        journal.model.update(model, journal.trace.state());
    });
}

pub(crate) proof fn finish<K, V>(
    tracked log: &SharedHistory<K, V>, tracked credit: OpenInvariantCredit,
    tracked session: &mut SessionTicket<K, V>, tracked ticket: CallTicket<K, V>,
)
    requires
        old(session).id() == log.constant().sessions,
        old(session).key() == ticket.value().2,
        old(session).value().1 == Some(ticket.key()),
        ticket.id() == log.constant().calls, ticket.value().1 is Some,
    ensures
        final(session).id() == old(session).id(), final(session).key() == old(session).key(),
        final(session).value().1 is None,
        api::valid_history(final(session).value().0),
        records_call_since(
            old(session).value().0, final(session).value().0, final(session).key(),
            ticket.value().0, ticket.value().1->Some_0,
        ),
    opens_invariants [log.namespace()]
{
    vstd::invariant::open_atomic_invariant_in_proof!(credit => log => journal => {
        journal.trace.finish(session, ticket);
    });
}

}
