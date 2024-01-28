//! My implementation of Rust's [`HashMap`](std::collections::HashMap)/[`BTreeMap`](std::collections::BTreeMap).
//!
//! Implemented methods should behave exactly like the original.


pub mod stupidmap {
    //! Implementation of Map using a sorted Vec.
    //! 
    //! Not efficient at all, just a proof of concept.
    
    /// Implementation of a Map using a sorted Vec.
    ///
    /// Only more efficient than a BTreeMap for small maps of less than 500 elements.
    pub struct StupidMap<K, V> {
        len: usize,
        buffer: Vec<(K, V)>,
    }

    impl<K, V> StupidMap<K, V> {
        /// Creates a new, empty `StupidMap`.
        pub const fn new() -> Self {
            Self {
                len: 0,
                buffer: Vec::new(),
            }
        }
        /// Creates a new, empty `StupidMap` with the specified capacity.
        pub fn with_capacity(capacity: usize) -> Self {
            Self {
                len: 0,
                buffer: Vec::with_capacity(capacity),
            }
        }
        fn with_buffer(buffer: Vec<(K, V)>) -> Self {
            Self {
                len: buffer.len(),
                buffer,
            }
        }
        /// Returns the number of elements in the map.
        pub const fn len(&self) -> usize {
            self.len
        }
        /// Returns `true` if the map contains no elements.
        pub const fn is_empty(&self) -> bool {
            self.len == 0
        }
        /// Inserts a key-value pair into the map.
        /// 
        /// If the map already contains the key, the value is updated.
        /// 
        /// # Examples
        /// ```
        /// use mycollections::StupidMap;
        /// 
        /// let mut map = StupidMap::new();
        /// map.insert("foo", 42);
        /// map.insert("bar", 1337);
        /// map.insert("baz", 69);
        /// 
        /// assert_eq!(map, &[("bar", 1337), ("baz", 69), ("foo", 42)]);
        /// 
        /// map.insert("foo", 55);
        /// assert_eq!(map, &[("bar", 1337), ("baz", 69), ("foo", 55)]);
        /// ```
        pub fn insert(&mut self, key: K, value: V) where K: std::cmp::Ord {
            match self.buffer.binary_search_by_key(&&key, |(k, _)| k) {
                Ok(found) => self.buffer[found].1 = value,
                Err(i) => { 
                    self.buffer.insert(i, (key, value));
                    self.len += 1;
                }
            }
        }
        /// Returns an iterator over the map's entries.
        /// 
        pub fn entries(&self) -> impl Iterator<Item = &(K, V)> {
            self.buffer.iter()
        }
        
        /// Returns an iterator over the map's entries, consuming the map.
        /// 
        /// # Examples
        /// ```
        /// use mycollections::StupidMap;
        /// 
        /// let mut map = StupidMap::new();
        /// map.insert("foo", 42);
        /// map.insert("bar", 1337);
        /// map.insert("baz", 69);
        /// 
        /// assert_eq!(map.into_entries().collect::<Vec<_>>(), &[("bar", 1337), ("baz", 69), ("foo", 42)]);
        /// ```
        pub fn into_entries(self) -> impl Iterator<Item = (K, V)> {
            self.buffer.into_iter()
        }
        /// Returns an iterator over the map's keys.
        pub fn keys(&self) -> impl Iterator<Item = &K> {
            self.buffer.iter().map(|(k, _)| k)
        }
        /// Returns an iterator over the map's values.
        pub fn values(&self) -> impl Iterator<Item = &V> {
            self.buffer.iter().map(|(_, v)| v)
        }
    }

    impl<K, V> FromIterator<(K, V)> for StupidMap<K, V> where K: std::cmp::Ord {
        fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
            let mut buffer = iter.into_iter().collect::<Vec<_>>();
            buffer.sort_unstable_by(|(k1, _), (k2, _)| k1.cmp(k2));
            Self::with_buffer(buffer)
        }
    }

    impl<K, V> Extend<(K, V)> for StupidMap<K, V> where K: std::cmp::Ord {
        fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
            self.buffer.extend(iter);
            self.buffer.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
        }
    }

    impl<K, V> PartialEq for StupidMap<K, V> where K: PartialEq, V: PartialEq {
        fn eq(&self, other: &Self) -> bool {
            self.buffer == other.buffer
        }
    }
    
    impl<K, V, Rhs> PartialEq<Rhs> for StupidMap<K, V> where K: PartialEq + Clone, V: PartialEq + Clone, K: Ord, for<'a> &'a Rhs: IntoIterator<Item = &'a (K, V)> {
        fn eq(&self, other: &Rhs) -> bool {
            let mut other = other.into_iter().cloned().collect::<Vec<_>>();
            other.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
            self.buffer.as_slice() == other.as_slice()
        }
    }
    
    impl<K, V> std::fmt::Debug for StupidMap<K, V> where K: std::fmt::Debug, V: std::fmt::Debug {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_map()
            // We map our vec so each entries' first field will become
            // the "key".
            .entries(self.buffer.iter().map(|(k, v)| (k, v)))
            .finish()
        }
    }
}

mod treemap {
    pub struct TreeMap<K, V> {
        len: usize,
        buckets: Vec<Vec<(K, V)>>,
    }

    impl<K, V> TreeMap<K, V> {
        pub const fn new() -> Self {
            Self {
                len: 0,
                buckets: Vec::new(),
            }
        }

        pub fn insert(&mut self, key: K, value: V) where K: std::cmp::PartialOrd {
            let bucket = self.buckets.get(self.buckets.len() / 2) else {
                self.buckets.push(vec![(key, value)]);
                self.len += 1;
                return;
            };



        }
    }
}