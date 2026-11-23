//! A KV store verified against the generated abstract history specification.

pub mod api;

mod refinement;

use api::KvSession;
#[cfg(verus_only)]
use dbspec::consistency::history::History;
use dbspec::functional::{Op, Reply};
#[cfg(verus_only)]
use dbspec::functional::step;
use refinement::{SessionTicket, SharedHistory, StoreModel};
use vstd::hash_map::HashMapWithView;
use vstd::invariant::create_open_invariant_credit;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {

struct Data {
    map: HashMapWithView<u64, u64>,
    model: Tracked<StoreModel<u64, u64>>,
}

#[cfg_attr(not(verus_only), allow(dead_code))]
struct DataPredicate {
    model_id: Ghost<Loc>,
}

impl RwLockPredicate<Data> for DataPredicate {
    closed spec fn inv(self, data: Data) -> bool {
        &&& data.model@.id() == self.model_id@
        &&& data.model@@ == data.map@
    }
}

pub struct Store {
    data: RwLock<Data, DataPredicate>,
    #[cfg_attr(not(verus_only), allow(dead_code))]
    history: Tracked<SharedHistory<u64, u64>>,
}

pub struct Session<'a> {
    store: &'a Store,
    #[cfg_attr(not(verus_only), allow(dead_code))]
    token: Tracked<SessionTicket<u64, u64>>,
}

impl Store {
    #[verifier::type_invariant]
    spec fn valid(self) -> bool {
        self.data.pred().model_id@ == self.history@.constant().model
    }

    pub fn new() -> (store: Self) {
        let map = HashMapWithView::new();
        let tracked initialized;
        proof { initialized = refinement::new::<u64, u64>(); }
        let tracked (history, model) = initialized;
        let ghost model_id = model.id();
        let data = RwLock::new(Data { map, model: Tracked(model) }, Ghost(DataPredicate {
            model_id: Ghost(model_id),
        }));
        Self { data, history: Tracked(history) }
    }

    pub fn open_session(&self) -> (session: Session<'_>)
        ensures
            session.ready(),
            session.store_id() == self.id(),
            session.history() == Seq::<dbspec::consistency::history::Event<u64, u64>>::empty(),
    {
        let Tracked(credit) = create_open_invariant_credit();
        let tracked token;
        proof { token = refinement::open_session(self.history.borrow(), credit); }
        Session { store: self, token: Tracked(token) }
    }

    pub closed spec fn id(&self) -> Loc {
        self.history@.constant().calls
    }
}

impl Session<'_> {
    fn execute(&mut self, op: Op<u64, u64>) -> (reply: Reply<u64>)
        requires old(self).ready(), api::selected_op(op),
        ensures
            final(self).ready(),
            final(self).store_id() == old(self).store_id(),
            final(self).session_id() == old(self).session_id(),
            dbspec::consistency::history::records_call_since(
                old(self).history(), final(self).history(), final(self).session_id(), op, reply,
            ),
            api::valid_history(final(self).history()),
            op is Get ==> reply is Value,
            !(op is Get) ==> reply == Reply::Ack,
    {
        let store = self.store;
        let Tracked(start) = create_open_invariant_credit();
        let tracked mut ticket;
        proof {
            use_type_invariant(store);
            ticket = refinement::begin(store.history.borrow(), start, self.token.borrow_mut(), op);
        }

        let (data, data_guard) = store.data.acquire_write();
        let mut map = data.map;
        let Tracked(mut model) = data.model;
        let ghost before = map@;
        let reply = match op {
            Op::Get(key) => Reply::Value(match map.get(&key) {
                Some(value) => Some(*value),
                None => None,
            }),
            Op::Put(key, value) => {
                map.insert(key, value);
                Reply::Ack
            },
            Op::Delete(key) => {
                let _removed = map.remove(&key);
                assert(map@ =~= before.remove(key));
                Reply::Ack
            },
        };

        // Relate the code that just ran to one abstract step under the data lock.
        let Tracked(effect) = create_open_invariant_credit();
        proof {
            assert((map@, reply) == step(before, op));
            refinement::apply(store.history.borrow(), effect, &mut model, &mut ticket, reply);
        }
        data_guard.release_write(Data { map, model: Tracked(model) });

        let Tracked(end) = create_open_invariant_credit();
        proof {
            refinement::finish(store.history.borrow(), end, self.token.borrow_mut(), ticket);
        }
        reply
    }
}

impl KvSession<u64, u64> for Session<'_> {
    closed spec fn ready(&self) -> bool {
        self.token@.id() == self.store.history@.constant().sessions && self.token@.value().1 is None
    }

    closed spec fn store_id(&self) -> Loc { self.store.id() }
    closed spec fn session_id(&self) -> nat { self.token@.key() }
    closed spec fn history(&self) -> History<u64, u64> { self.token@.value().0 }

    fn get(&mut self, key: u64) -> (value: Option<u64>) {
        match self.execute(Op::Get(key)) {
            Reply::Value(value) => value,
            Reply::Ack => unreachable!(),
        }
    }

    fn put(&mut self, key: u64, value: u64) {
        let _ = self.execute(Op::Put(key, value));
    }

    fn delete(&mut self, key: u64) {
        let _ = self.execute(Op::Delete(key));
    }
}

}

fn main() {
    #[cfg(not(verus_only))]
    {
        let store = Store::new();
        let mut first = store.open_session();
        let mut second = store.open_session();

        std::thread::scope(|scope| {
            scope.spawn(|| first.put(2, 20));
            scope.spawn(|| second.put(3, 30));
        });

        assert_eq!(first.get(3), Some(30));
        assert_eq!(second.get(2), Some(20));
        second.delete(2);
        assert_eq!(first.get(2), None);
        println!("Both sessions shared the store across concurrent calls.");
    }
}
