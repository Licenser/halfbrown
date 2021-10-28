use super::{HashMap, HashMapInt};
use core::hash::{BuildHasher, Hash};
use std::iter::{FromIterator, IntoIterator};

/// Iterator over the key value pairs of a Halfbrown map
pub struct Iter<'a, K, V>(IterInt<'a, K, V>);

impl<'a, K, V> From<IterInt<'a, K, V>> for Iter<'a, K, V> {
    fn from(i: IterInt<'a, K, V>) -> Self {
        Self(i)
    }
}
pub(crate) enum IterInt<'a, K, V> {
    Map(hashbrown::hash_map::Iter<'a, K, V>),
    Vec(std::slice::Iter<'a, (K, V)>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IterInt::Map(m) => m.next(),
            IterInt::Vec(m) => {
                if let Some((k, v)) = m.next() {
                    Some((k, v))
                } else {
                    None
                }
            }
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IterInt::Map(m) => m.size_hint(),
            IterInt::Vec(m) => m.size_hint(),
        }
    }
}

/// Into iterator for a Halfbrown map
pub struct IntoIter<K, V>(IntoIterInt<K, V>);
enum IntoIterInt<K, V> {
    Map(hashbrown::hash_map::IntoIter<K, V>),
    Vec(std::vec::IntoIter<(K, V)>),
}
impl<K, V> IntoIter<K, V> {
    /// The length of this iterator
    #[must_use]
    pub fn len(&self) -> usize {
        match &self.0 {
            IntoIterInt::Map(i) => i.len(),
            IntoIterInt::Vec(i) => i.len(),
        }
    }
    /// If this iteratoris empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IntoIterInt::Map(m) => m.next(),
            IntoIterInt::Vec(m) => m.next(),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IntoIterInt::Map(m) => m.size_hint(),
            IntoIterInt::Vec(m) => m.size_hint(),
        }
    }
}

impl<K, V, S> IntoIterator for HashMap<K, V, S>
where
    K: Eq + Hash,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        match self.0 {
            HashMapInt::Map(m) => IntoIter(IntoIterInt::Map(m.into_iter())),
            HashMapInt::Vec(m) => IntoIter(IntoIterInt::Vec(m.into_iter())),
            HashMapInt::None => unreachable!(),
        }
    }
}

impl<'a, K, V, S> IntoIterator for &'a HashMap<K, V, S>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<K, V, S> FromIterator<(K, V)> for HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity_and_hasher(iter.size_hint().0, S::default());
        iter.for_each(|(k, v)| {
            map.insert(k, v);
        });
        map
    }
}

/// Mutable iterator over the key value pairs
pub struct IterMut<'a, K, V>(IterMutInt<'a, K, V>);

impl<'a, K, V> From<IterMutInt<'a, K, V>> for IterMut<'a, K, V> {
    fn from(i: IterMutInt<'a, K, V>) -> Self {
        Self(i)
    }
}

pub(crate) enum IterMutInt<'a, K, V> {
    Map(hashbrown::hash_map::IterMut<'a, K, V>),
    Vec(std::slice::IterMut<'a, (K, V)>),
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        match &mut self.0 {
            IterMutInt::Map(m) => m.next(),
            IterMutInt::Vec(m) => m.next().map(|(k, v)| (k as &K, v)),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IterMutInt::Map(m) => m.size_hint(),
            IterMutInt::Vec(m) => m.size_hint(),
        }
    }
}
