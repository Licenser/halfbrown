//! Halfbrown is a hashmap implementation that provides
//! high performance for both small and large maps by
//! dymaically switching between different backend.
//!
//! The basic idea is that hash maps are expensive to
//! insert and lookup for small numbers of entries
//! but effective for lager numbers.
//!
//! So for smaller maps, we picked 32 entries as a rule
//! of thumb, we simply store data in a list of tuples.
//! Looking those up and iterating over them is still
//! faster then hasing strings on every lookup.
//!
//! Once we pass the 32 entires we transition the
//! backend to a `HashMap`.
//!
//! Note: Most of the documentation is taken from
//! rusts hashmap.rs and should be considered under
//! their copyright.

#![forbid(warnings)]
#![warn(unused_extern_crates)]
#![cfg_attr(
    feature = "cargo-clippy",
    deny(
        clippy::all,
        clippy::result_unwrap_used,
        clippy::unnecessary_unwrap,
        clippy::pedantic
    ),
    // We might want to revisit inline_always
    allow(clippy::module_name_repetitions, clippy::inline_always)
)]
#![deny(missing_docs)]

mod entry;
mod iter;
mod macros;
#[cfg(feature = "serde")]
mod serde;
mod vecmap;

pub use crate::entry::*;
pub use crate::iter::*;
use crate::vecmap::VecMap;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
pub use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::{self, HashMap as HashBrown};
use std::default::Default;
use std::ops::Index;

//const VEC_LOWER_LIMIT: usize = 32;
const VEC_LIMIT_UPPER: usize = 32;

/// `HashMap` implementation that alternates between a vector
/// and a hashmap to improve performance for low key counts.
#[derive(Clone, Debug, Default)]
pub struct HashMap<K: Eq + Hash, V, S: BuildHasher + Default = DefaultHashBuilder>(
    HashMapInt<K, V, S>,
);

#[derive(Clone, Debug)]
enum HashMapInt<K, V, S = DefaultHashBuilder>
where
    S: BuildHasher + Default,
    K: Eq + Hash,
{
    Map(HashBrown<K, V, S>),
    Vec(VecMap<K, V>),
    None,
}

impl<K, V, S> Default for HashMapInt<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    #[inline]
    fn default() -> Self {
        Self::Vec(VecMap::new())
    }
}

impl<K, V> HashMap<K, V, DefaultHashBuilder>
where
    K: Eq + Hash,
{
    /// Creates an empty `HashMap`.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self(HashMapInt::Vec(VecMap::new()))
    }

    /// Creates an empty `HashMap` with the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::with_capacity(10);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(if capacity > VEC_LIMIT_UPPER {
            HashMapInt::Map(HashBrown::with_capacity_and_hasher(
                capacity,
                DefaultHashBuilder::default(),
            ))
        } else {
            HashMapInt::Vec(VecMap::with_capacity(capacity))
        })
    }

    /// Same as with capacity with the difference that it, despite of the
    /// requested size always returns a vector. This allows quicker generation
    /// when used in combination with `insert_nocheck`.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::vec_with_capacity(128);
    /// assert!(map.is_vec());
    /// ```
    #[inline]
    pub fn vec_with_capacity(capacity: usize) -> Self {
        Self(HashMapInt::Vec(VecMap::with_capacity(capacity)))
    }
}

impl<K, V, S> HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    /// Creates an empty `HashMap` with the specified capacity, using `hash_builder`
    /// to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = HashMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self(HashMapInt::Map(HashBrown::with_capacity_and_hasher(
            capacity,
            hash_builder,
        )))
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `HashMap<K, V>` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        match &self.0 {
            HashMapInt::Map(m) => m.capacity(),
            HashMapInt::Vec(m) => m.capacity(),
            HashMapInt::None => unimplemented!(),
        }
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    ///
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        match &self.0 {
            HashMapInt::Map(m) => IterInt::Map(m.iter()).into(),
            HashMapInt::Vec(m) => IterInt::Vec(m.iter()).into(),
            HashMapInt::None => unreachable!(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        match &mut self.0 {
            HashMapInt::Map(m) => IterMutInt::Map(m.iter_mut()).into(),
            HashMapInt::Vec(m) => IterMutInt::Vec(m.iter_mut()).into(),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        match &self.0 {
            HashMapInt::Map(m) => m.len(),
            HashMapInt::Vec(m) => m.len(),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        match &self.0 {
            HashMapInt::Map(m) => m.is_empty(),
            HashMapInt::Vec(m) => m.is_empty(),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// for (k, v) in a.drain().take(1) {
    ///     assert!(k == 1 || k == 2);
    ///     assert!(v == "a" || v == "b");
    /// }
    ///
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<K, V> {
        match &mut self.0 {
            HashMapInt::Map(m) => Drain(DrainInt::Map(m.drain())),
            HashMapInt::Vec(m) => Drain(DrainInt::Vec(m.drain())),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        match &mut self.0 {
            HashMapInt::Map(m) => m.clear(),
            HashMapInt::Vec(m) => m.clear(),
            HashMapInt::None => unreachable!(),
        }
    }
}

impl<K, V, S> HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `HashMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// [`usize`]: ../../std/primitive.usize.html
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::new();
    /// map.reserve(10);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        match &mut self.0 {
            HashMapInt::Map(m) => m.reserve(additional),
            HashMapInt::Vec(m) => m.reserve(additional),
            HashMapInt::None => unreachable!(),
        }
    }

    /*
    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `HashMap<K,V>`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(try_reserve)]
    /// use halfbrown::HashMap;
    /// let mut map: HashMap<&str, isize> = HashMap::new();
    /// map.try_reserve(10).expect("why is the test harness OOMing on 10 bytes?");
    /// ```
    #[unstable(feature = "try_reserve", reason = "new API", issue = "48043")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr> {
        match &self.0 {
            HashMap::Map(m) => m.try_reserve(additional),
            HashMap::Vec(m) => m.try_reserve(additional),
            HashMap::None => unreachable!(),
        }
    }
     */

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map: HashMap<i32, i32> = HashMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        match &mut self.0 {
            HashMapInt::Map(m) => m.shrink_to_fit(),
            HashMapInt::Vec(m) => m.shrink_to_fit(),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut letters = HashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<K, V, S> {
        match &mut self.0 {
            HashMapInt::Map(m) => m.entry(key).into(),
            HashMapInt::Vec(m) => m.entry(key).into(),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: ../../std/cmp/trait.Eq.html
    /// [`Hash`]: ../../std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[inline]
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match &self.0 {
            HashMapInt::Map(m) => m.get(k),
            HashMapInt::Vec(m) => m.get(k),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: ../../std/cmp/trait.Eq.html
    /// [`Hash`]: ../../std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match &self.0 {
            HashMapInt::Map(m) => m.contains_key(k),
            HashMapInt::Vec(m) => m.contains_key(k),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: ../../std/cmp/trait.Eq.html
    /// [`Hash`]: ../../std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```

    #[inline]
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match &mut self.0 {
            HashMapInt::Map(m) => m.get_mut(k),
            HashMapInt::Vec(m) => m.get_mut(k),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        match &mut self.0 {
            HashMapInt::Map(m) => m.insert(k, v),
            HashMapInt::Vec(m) => {
                if m.len() >= VEC_LIMIT_UPPER {
                    let r;
                    self.0 = match std::mem::replace(&mut self.0, HashMapInt::None) {
                        HashMapInt::Vec(mut m) => {
                            let mut m1: HashBrown<K, V, S> = m.drain().collect();
                            r = m1.insert(k, v);
                            HashMapInt::Map(m1)
                        }
                        _ => unreachable!(),
                    };
                    r
                } else {
                    m.insert(k, v)
                }
            }
            HashMapInt::None => unreachable!(),
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: ../../std/cmp/trait.Eq.html
    /// [`Hash`]: ../../std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use halfbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match &mut self.0 {
            HashMapInt::Map(m) => m.remove(k),
            HashMapInt::Vec(m) => m.remove(k),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Inserts element, this ignores check in the vector
    /// map if keys are present - it's a fast way to build
    /// a new map when uniqueness is known ahead of time.
    #[inline]
    pub fn insert_nocheck(&mut self, k: K, v: V) {
        match &mut self.0 {
            HashMapInt::Map(m) => {
                m.insert(k, v);
            }
            HashMapInt::Vec(m) => m.insert_nocheck(k, v),
            HashMapInt::None => unreachable!(),
        }
    }

    /// Checks if the current backend is a map, if so returns
    /// true.
    pub fn is_map(&self) -> bool {
        match &self.0 {
            HashMapInt::Map(_m) => true,
            HashMapInt::Vec(_m) => false,
            HashMapInt::None => unreachable!(),
        }
    }

    /// Checks if the current backend is a vector, if so returns
    /// true.
    pub fn is_vec(&self) -> bool {
        match &self.0 {
            HashMapInt::Map(_m) => false,
            HashMapInt::Vec(_m) => true,
            HashMapInt::None => unreachable!(),
        }
    }
}

impl<K, Q: ?Sized, V, S> Index<&Q> for HashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    S: BuildHasher + Default,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `HashMap`.
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

// Taken from hashbrown
impl<K, V, S> PartialEq for HashMap<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher + Default,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

//#[derive(Clone)]
/// Iterator over the keys
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<(&'a K)> {
        self.inner.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

//#[derive(Clone)]
/// Iterator over the values
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}
impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<(&'a V)> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

//#[derive(Clone)]
/// Mutable iterator over the values
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<(&'a mut V)> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// Drains the map
pub struct Drain<'a, K, V>(DrainInt<'a, K, V>);

enum DrainInt<'a, K, V> {
    Map(hashbrown::hash_map::Drain<'a, K, V>),
    Vec(std::vec::Drain<'a, (K, V)>),
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            DrainInt::Map(m) => m.next(),
            DrainInt::Vec(m) => m.next(),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            DrainInt::Map(m) => m.size_hint(),
            DrainInt::Vec(m) => m.size_hint(),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scale_up() {
        let mut v = HashMap::new();
        assert!(v.is_vec());
        for i in 1..33 {
            // 32 entries
            v.insert(i, i);
            assert!(v.is_vec());
        }
        v.insert(33, 33);
        assert!(v.is_map());
    }

    #[test]
    fn str_key() {
        let mut v: HashMap<String, u32> = HashMap::new();
        v.insert("hello".to_owned(), 42);
        assert_eq!(v["hello"], 42);
    }

    #[test]
    fn add_remove() {
        let mut v = HashMap::new();
        v.insert(1, 1);
        v.insert(2, 2);
        v.insert(3, 3);
        assert_eq!(v.get(&1), Some(&1));
        assert_eq!(v.get(&2), Some(&2));
        assert_eq!(v.get(&3), Some(&3));
        v.remove(&2);
        assert_eq!(v.get(&1), Some(&1));
        assert_eq!(v.get(&2), None);
        assert_eq!(v.get(&3), Some(&3));
    }
}
