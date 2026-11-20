use crate::consistency::causal_consistency::{
    causally_consistent, valid_causal_execution, valid_causal_view,
};
use crate::consistency::history::{precedes, responds_to, Event};
use crate::consistency::linearizability::valid_linearization;
use crate::consistency::replay::{legal_replay, ReplayEntry};
use crate::consistency::sequential_consistency::valid_sequential_order;
use crate::functional::{Op, Reply};
use vstd::prelude::*;

verus! {

proof fn sequential_order_can_reorder_calls_from_different_sessions() {
    let initial = Map::<u64, u64>::empty();
    let get = Op::Get(0u64);
    let reply = Reply::Value(None);
    let first = Event::Invoke { id: 0, session: 0, op: get };
    let second = Event::Invoke { id: 1, session: 1, op: get };
    let history = seq![
        first, Event::Respond { id: 0, reply },
        second, Event::Respond { id: 1, reply },
    ];
    let reversed = seq![
        ReplayEntry { invocation: second, reply },
        ReplayEntry { invocation: first, reply },
    ];

    reveal_with_fuel(legal_replay, 3);
    assert(!initial.contains_key(0u64));
    assert(responds_to(history, 0, 1));
    assert(responds_to(history, 2, 3));
    assert(precedes(history, 0, 2));
    assert(valid_sequential_order(history, initial, reversed));
    assert(!valid_linearization(history, initial, reversed));
}

proof fn sequential_order_preserves_order_within_a_session() {
    let initial = Map::<u64, u64>::empty();
    let get = Op::Get(0u64);
    let reply = Reply::Value(None);
    let first = Event::Invoke { id: 0, session: 0, op: get };
    let second = Event::Invoke { id: 1, session: 0, op: get };
    let history = seq![
        first, Event::Respond { id: 0, reply },
        second, Event::Respond { id: 1, reply },
    ];
    let first_entry = ReplayEntry { invocation: first, reply };
    let second_entry = ReplayEntry { invocation: second, reply };
    let ordered = seq![first_entry, second_entry];
    let reversed = seq![second_entry, first_entry];

    reveal_with_fuel(legal_replay, 3);
    assert(!initial.contains_key(0u64));
    assert(responds_to(history, 0, 1));
    assert(responds_to(history, 2, 3));
    assert(precedes(history, 0, 2));
    assert(valid_sequential_order(history, initial, ordered));
    assert(!valid_sequential_order(history, initial, reversed));
}

proof fn causal_views_can_omit_concurrent_writes() {
    let initial = Map::<u64, u64>::empty();
    let put_x = Event::Invoke { id: 0, session: 0, op: Op::Put(0u64, 1u64) };
    let get_y = Event::Invoke { id: 1, session: 0, op: Op::Get(1u64) };
    let put_y = Event::Invoke { id: 2, session: 1, op: Op::Put(1u64, 1u64) };
    let get_x = Event::Invoke { id: 3, session: 1, op: Op::Get(0u64) };
    let history = seq![
        put_x, Event::Respond { id: 0, reply: Reply::Ack },
        put_y, Event::Respond { id: 2, reply: Reply::Ack },
        get_y, Event::Respond { id: 1, reply: Reply::Value(None) },
        get_x, Event::Respond { id: 3, reply: Reply::Value(None) },
    ];
    let write_x = ReplayEntry { invocation: put_x, reply: Reply::Ack };
    let read_y = ReplayEntry { invocation: get_y, reply: Reply::Value(None) };
    let write_y = ReplayEntry { invocation: put_y, reply: Reply::Ack };
    let read_x = ReplayEntry { invocation: get_x, reply: Reply::Value(None) };
    let calls = Map::<nat, ReplayEntry<u64, u64>>::empty()
        .insert(0, write_x).insert(1, read_y).insert(2, write_y).insert(3, read_x);
    let causal_order = set![(0nat, 1nat), (2nat, 3nat)];

    reveal_with_fuel(legal_replay, 3);
    assert(!initial.contains_key(0u64));
    assert(!initial.contains_key(1u64));
    assert(responds_to(history, 0, 1));
    assert(responds_to(history, 2, 3));
    assert(responds_to(history, 4, 5));
    assert(responds_to(history, 6, 7));
    assert forall |id: nat| #[trigger] calls.contains_key(id)
        implies exists |view: Seq<ReplayEntry<u64, u64>>|
            #[trigger] valid_causal_view(initial, calls, causal_order, id, view) by {
        let view = if id == 0 {
            seq![write_x]
        } else if id == 1 {
            seq![write_x, read_y]
        } else if id == 2 {
            seq![write_y]
        } else {
            seq![write_y, read_x]
        };
        assert(valid_causal_view(initial, calls, causal_order, id, view));
    }
    assert(valid_causal_execution(history, initial, calls, causal_order));
    assert(causally_consistent(history, initial));
}

proof fn causal_view_requires_all_predecessors_in_causal_order() {
    let initial = Map::<u64, u64>::empty().insert(1, 1);
    let put = ReplayEntry {
        invocation: Event::Invoke { id: 0, session: 0, op: Op::Put(0u64, 1u64) },
        reply: Reply::Ack,
    };
    let delete = ReplayEntry {
        invocation: Event::Invoke { id: 1, session: 0, op: Op::Delete(1u64) },
        reply: Reply::Ack,
    };
    let get = ReplayEntry {
        invocation: Event::Invoke { id: 2, session: 1, op: Op::Get(1u64) },
        reply: Reply::Value(None),
    };
    let calls = Map::<nat, ReplayEntry<u64, u64>>::empty()
        .insert(0, put).insert(1, delete).insert(2, get);
    let causal_order = set![(0nat, 1nat), (1nat, 2nat), (0nat, 2nat)];

    reveal_with_fuel(legal_replay, 4);
    assert(valid_causal_view(initial, calls, causal_order, 2, seq![put, delete, get]));
    // Both candidate replays produce the right reply and still violate causality.
    let missing_put = seq![delete, get];
    assert(legal_replay(initial, missing_put));
    assert(causal_order.contains((0nat, 2nat)));
    assert(!valid_causal_view(initial, calls, causal_order, 2, missing_put));
    let reversed_writes = seq![delete, put, get];
    assert(legal_replay(initial, reversed_writes));
    assert(causal_order.contains((0nat, 1nat)));
    assert(!valid_causal_view(initial, calls, causal_order, 2, reversed_writes));
}

}
