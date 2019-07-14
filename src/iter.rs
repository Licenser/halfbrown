use crate::HashMap;
use core::hash::{BuildHasher, Hash};
use hashbrown;
use std::iter::{FromIterator, IntoIterator};

pub enum Iter<'a, K, V> {
    Map(hashbrown::hash_map::Iter<'a, K, V>),
    Vec(std::slice::Iter<'a, (K, V)>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Iter::Map(m) => m.next(),
            Iter::Vec(m) => {
                if let Some((k, v)) = m.next() {
                    Some((&k, &v))
                } else {
                    None
                }
            }
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Iter::Map(m) => m.size_hint(),
            Iter::Vec(m) => m.size_hint(),
        }
    }
}

pub enum IntoIter<K, V> {
    Map(hashbrown::hash_map::IntoIter<K, V>),
    Vec(std::vec::IntoIter<(K, V)>),
}
impl<K, V> IntoIter<K, V> {
    pub fn len(&self) -> usize {
        match self {
            IntoIter::Map(i) => i.len(),
            IntoIter::Vec(i) => i.len(),
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IntoIter::Map(m) => m.next(),
            IntoIter::Vec(m) => m.next(),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IntoIter::Map(m) => m.size_hint(),
            IntoIter::Vec(m) => m.size_hint(),
        }
    }
}

impl<K, V, S> IntoIterator for HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        match self {
            HashMap::Map(m) => IntoIter::Map(m.into_iter()),
            HashMap::Vec(m) => IntoIter::Vec(m.into_iter()),
            HashMap::None => unreachable!(),
        }
    }
}

impl<'a, K, V, S> IntoIterator for &'a HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
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

//#[derive(Clone)]
pub enum IterMut<'a, K, V> {
    Map(hashbrown::hash_map::IterMut<'a, K, V>),
    Vec(std::slice::IterMut<'a, (K, V)>),
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        match self {
            IterMut::Map(m) => m.next(),
            IterMut::Vec(m) => m.next().map(|(k, v)| (k as &K, v)),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IterMut::Map(m) => m.size_hint(),
            IterMut::Vec(m) => m.size_hint(),
        }
    }
}
