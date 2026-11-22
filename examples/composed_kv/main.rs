//! Two session handles using the same shared store.

pub mod api;

#[cfg(not(verus_only))]
mod demo {
    use super::api::KvStore;
    use std::collections::HashMap;
    use std::sync::{Arc, RwLock};
    use std::thread;

    type Shard = RwLock<HashMap<u64, u64>>;

    struct Session {
        shards: Arc<[Shard; 2]>,
    }

    impl Session {
        fn shard(&self, key: u64) -> &Shard {
            &self.shards[(key % 2) as usize]
        }
    }

    impl KvStore<u64, u64> for Session {
        fn new() -> Self {
            Self {
                shards: Arc::new(std::array::from_fn(|_| RwLock::new(HashMap::new()))),
            }
        }

        fn open_session(&self) -> Self {
            Self {
                shards: Arc::clone(&self.shards),
            }
        }

        fn get(&mut self, key: u64) -> Option<u64> {
            self.shard(key).read().unwrap().get(&key).copied()
        }

        fn put(&mut self, key: u64, value: u64) {
            self.shard(key).write().unwrap().insert(key, value);
        }

        fn delete(&mut self, key: u64) {
            self.shard(key).write().unwrap().remove(&key);
        }
    }

    pub fn run() {
        let mut first = Session::new();
        let mut second = first.open_session();

        thread::scope(|scope| {
            // Each thread mutably borrows its own handle and writes to a different shard.
            scope.spawn(|| first.put(2, 20));
            scope.spawn(|| second.put(3, 30));
        });

        // Reading through the other session shows that the two handles share the data.
        assert_eq!(first.get(3), Some(30));
        assert_eq!(second.get(2), Some(20));
        second.delete(2);
        assert_eq!(first.get(2), None);
        println!("Both sessions shared the store across concurrent writes.");
    }
}

fn main() {
    #[cfg(not(verus_only))]
    demo::run();
}
