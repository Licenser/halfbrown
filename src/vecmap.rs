mod entry;
mod iter;

pub(crate) use self::entry::*;
use std::borrow::Borrow;
#[derive(Default, Debug, Clone)]
pub(crate) struct VecMap<K, V> {
    v: Vec<(K, V)>,
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
        };
        for (k1, v1) in &self.v {
            if let Some(v2) = other.get(k1.borrow()) {
                if v1 != v2.borrow() {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }
}

impl<K, V> VecMap<K, V>
where
    K: Eq,
{
    #[inline]
    pub(crate) fn new() -> Self {
        Self { v: Vec::new() }
    }

    #[inline]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            v: Vec::with_capacity(capacity),
        }
    }
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.v.capacity()
    }

    #[inline]
    pub(crate) fn insert(&mut self, k: K, mut v: V) -> Option<V> {
        for (ak, av) in &mut self.v {
            if k == *ak {
                std::mem::swap(av, &mut v);
                return Some(v);
            }
        }
        self.v.push((k, v));
        None
    }

    #[inline]
    pub(crate) fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut i = 0;
        while i != self.v.len() {
            let (ak, _) = unsafe { self.v.get_unchecked(i) };
            if k == ak.borrow() {
                let (_, v) = self.v.swap_remove(i);
                return Some(v);
            }
            i += 1;
        }
        None
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
        self.v.reserve(additional)
    }

    #[inline]
    pub(crate) fn shrink_to_fit(&mut self) {
        self.v.shrink_to_fit()
    }

    #[inline]
    pub(crate) fn insert_nocheck(&mut self, k: K, v: V) {
        self.v.push((k, v));
    }

    pub(crate) fn entry(&mut self, key: K) -> Entry<K, V> {
        for (idx, (ak, _v)) in self.v.iter().enumerate() {
            if &key == ak.borrow() {
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
                return Some(&v);
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

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.v.clear()
    }
}
