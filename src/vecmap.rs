///! A vector based map data structure, mostly for internal use
mod entry;
mod iter;
mod raw_entry;

pub(crate) use self::entry::*;
pub(crate) use self::raw_entry::*;
use crate::DefaultHashBuilder;
use std::borrow::Borrow;

#[derive(Debug, Clone)]
pub(crate) struct VecMap<K, V, S = DefaultHashBuilder> {
    v: Vec<(K, V)>,
    hash_builder: S,
}

impl<K, V> Default for VecMap<K, V, DefaultHashBuilder> {
    #[inline]
    fn default() -> Self {
        Self {
            v: Vec::new(),
            hash_builder: DefaultHashBuilder::default(),
        }
    }
}

impl<K1, V1, K2, V2> PartialEq<VecMap<K2, V2>> for VecMap<K1, V1>
where
    K1: Eq,
    K2: Eq + Borrow<K1>,
    V1: PartialEq,
    V2: Borrow<V1>,
{
    fn eq(&self, other: &VecMap<K2, V2>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| value == v.borrow()))
    }
}

impl<K, V> VecMap<K, V, DefaultHashBuilder> {
    #[inline]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            v: Vec::with_capacity(capacity),
            hash_builder: DefaultHashBuilder::default(),
        }
    }
}

impl<K, V, S> VecMap<K, V, S> {
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        let mut new = Vec::new();
        std::mem::swap(&mut new, &mut self.v);
        self.v = new
            .into_iter()
            .filter_map(|(k, mut v)| if f(&k, &mut v) { Some((k, v)) } else { None })
            .collect();
    }

    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.v.capacity()
    }

    #[inline]
    pub(crate) fn iter(&self) -> std::slice::Iter<'_, (K, V)> {
        self.v.iter()
    }

    #[inline]
    pub(crate) fn iter_mut(&mut self) -> std::slice::IterMut<'_, (K, V)> {
        self.v.iter_mut()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.v.len()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.v.is_empty()
    }

    #[inline]
    pub(crate) fn drain(&mut self) -> std::vec::Drain<(K, V)> {
        self.v.drain(..)
    }

    #[inline]
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.v.reserve(additional);
    }

    #[inline]
    pub(crate) fn shrink_to_fit(&mut self) {
        self.v.shrink_to_fit();
    }
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.v.clear();
    }
}
impl<K, V, S> VecMap<K, V, S> {
    #[inline]
    pub(crate) fn hasher(&self) -> &S {
        &self.hash_builder
    }
    #[inline]
    pub(crate) fn insert(&mut self, k: K, mut v: V) -> Option<V>
    where
        K: Eq,
    {
        for (ak, av) in &mut self.v {
            if &k == ak {
                std::mem::swap(av, &mut v);
                return Some(v);
            }
        }
        self.insert_idx(k, v);
        None
    }

    #[inline]
    pub(crate) fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.remove_entry(k).map(|e| e.1)
    }

    #[inline]
    pub(crate) fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut i = 0;
        while i != self.v.len() {
            let (ak, _) = unsafe { self.v.get_unchecked(i) };
            if k == ak.borrow() {
                unsafe {
                    return Some(self.remove_idx(i));
                }
            }
            i += 1;
        }
        None
    }

    #[inline]
    pub(crate) fn insert_nocheck(&mut self, k: K, v: V) {
        self.v.push((k, v));
    }

    pub(crate) fn entry(&mut self, key: K) -> Entry<K, V, S>
    where
        K: Eq,
    {
        for (idx, (ak, _v)) in self.v.iter().enumerate() {
            if &key == ak {
                return Entry::Occupied(OccupiedEntry::new(idx, key, self));
            }
        }
        Entry::Vacant(VacantEntry::new(key, self))
    }
    #[inline]
    pub(crate) fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        for (ak, v) in &self.v {
            if k == ak.borrow() {
                return Some(v);
            }
        }
        None
    }

    #[inline]
    pub(crate) fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        for (ak, _v) in &self.v {
            if k == ak.borrow() {
                return true;
            }
        }
        false
    }

    #[inline]
    pub(crate) fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        for (ak, v) in &mut self.v {
            if k.eq((*ak).borrow()) {
                return Some(v);
            }
        }
        None
    }

    /// Creates a raw entry builder for the `HashMap`.
    ///
    /// Raw entries provide the lowest level of control for searching and
    /// manipulating a map. They must be manually initialized with a hash and
    /// then manually searched. After this, insertions into a vacant entry
    /// still require an owned key to be provided.
    ///
    /// Raw entries are useful for such exotic situations as:
    ///
    /// * Hash memoization
    /// * Deferring the creation of an owned key until it is known to be required
    /// * Using a search key that doesn't work with the Borrow trait
    /// * Using custom comparison logic without newtype wrappers
    ///
    /// Because raw entries provide much more low-level control, it's much easier
    /// to put the `HashMap` into an inconsistent state which, while memory-safe,
    /// will cause the map to produce seemingly random results. Higher-level and
    /// more foolproof APIs like `entry` should be preferred when possible.
    ///
    /// In particular, the hash used to initialized the raw entry must still be
    /// consistent with the hash of the key that is ultimately stored in the entry.
    /// This is because implementations of `HashMap` may need to recompute hashes
    /// when resizing, at which point only the keys are available.
    ///
    /// Raw entries give mutable access to the keys. This must not be used
    /// to modify how the key would compare or hash, as the map will not re-evaluate
    /// where the key should go, meaning the keys may become "lost" if their
    /// location does not reflect their state. For instance, if you change a key
    /// so that the map now contains keys which compare equal, search may start
    /// acting erratically, with two keys randomly masking each other. Implementations
    /// are free to assume this doesn't happen (within the limits of memory-safety).
    #[inline]
    pub fn raw_entry_mut(&mut self) -> RawEntryBuilderMut<'_, K, V, S> {
        RawEntryBuilderMut { map: self }
    }

    /// Creates a raw immutable entry builder for the `HashMap`.
    ///
    /// Raw entries provide the lowest level of control for searching and
    /// manipulating a map. They must be manually initialized with a hash and
    /// then manually searched.
    ///
    /// This is useful for
    /// * Hash memoization
    /// * Using a search key that doesn't work with the Borrow trait
    /// * Using custom comparison logic without newtype wrappers
    ///
    /// Unless you are in such a situation, higher-level and more foolproof APIs like
    /// `get` should be preferred.
    ///
    /// Immutable raw entries have very limited use; you might instead want `raw_entry_mut`.
    #[inline]
    pub fn raw_entry(&self) -> RawEntryBuilder<'_, K, V, S> {
        RawEntryBuilder { map: self }
    }

    /// Removes an element from a given position
    #[inline]
    unsafe fn remove_idx(&mut self, idx: usize) -> (K, V) {
        self.v.swap_remove(idx)
    }

    /// inserts a non existing element and returns it's position
    #[inline]
    fn insert_idx(&mut self, k: K, v: V) -> usize {
        let pos = self.v.len();
        self.v.push((k, v));
        pos
    }
    /// inserts a non existing element and returns it's position
    #[inline]
    unsafe fn get_mut_idx(&mut self, idx: usize) -> (&mut K, &mut V) {
        let r = self.v.get_unchecked_mut(idx);
        (&mut r.0, &mut r.1)
    }
}
