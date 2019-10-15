use super::VecMap;

impl<K, V, S> IntoIterator for VecMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = std::vec::IntoIter<(K, V)>;

    #[inline]
    fn into_iter(self) -> std::vec::IntoIter<(K, V)> {
        self.v.into_iter()
    }
}
