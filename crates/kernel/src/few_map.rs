//! A map for memos that almost always hold a handful of entries.
//!
//! The kernel's per-call memos (a substitution's shared nodes, a syntactic
//! equality's equal pairs, a substitution's lifted payloads) are keyed by
//! addresses and live for one call. Most calls record one or two entries, a
//! few record thousands. A hash table serves the second kind and taxes the
//! first: it allocates at the first insert and rehashes at the next few, and
//! a table kept between calls to avoid that is emptied at the cost of its
//! capacity, which is the largest call's, not this one's
//! (`issues/per-call-memos-pay-table-capacity.md`).
//!
//! So the first [`FEW`] entries are an array in the map itself, compared one
//! by one, and only an entry past them goes to a [`PtrMap`]. A map that
//! stays small allocates nothing and is dropped by dropping what it holds; a
//! map that grows pays the table from its fifth entry on, in proportion to
//! what it then stores.
//!
//! Two invariants, both local to [`FewMap::insert`]: the array is filled from
//! the front (so the first empty slot ends a search, and the table is empty
//! unless the array is full), and a key is in at most one of the two.

use crate::value::PtrMap;

/// Entries held in the map itself.
pub(crate) const FEW: usize = 4;

pub(crate) struct FewMap<K, V> {
    few: [Option<(K, V)>; FEW],
    many: PtrMap<K, V>,
}

impl<K, V> Default for FewMap<K, V> {
    fn default() -> FewMap<K, V> {
        FewMap { few: [const { None }; FEW], many: PtrMap::default() }
    }
}

impl<K: Copy + Eq + std::hash::Hash, V> FewMap<K, V> {
    #[inline]
    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        for slot in &self.few {
            match slot {
                Some((k, v)) if k == key => return Some(v),
                Some(_) => {}
                None => return None,
            }
        }
        if self.many.is_empty() {
            return None;
        }
        self.many.get(key)
    }

    #[inline]
    pub(crate) fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Bind `key` to `value`, returning what it was bound to.
    #[inline]
    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        for slot in &mut self.few {
            match slot {
                Some((k, v)) if *k == key => return Some(std::mem::replace(v, value)),
                Some(_) => {}
                None => {
                    *slot = Some((key, value));
                    return None;
                }
            }
        }
        self.many.insert(key, value)
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.few.iter().flatten().count() + self.many.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_map_answers_as_a_hash_map_does_at_every_size() {
        // Past the array as well as inside it, with rebinding at both.
        let mut few: FewMap<(usize, u32), u64> = FewMap::default();
        let mut reference = std::collections::HashMap::new();
        let mut state = 0x2545_f491_4f6c_dd1du64;
        for round in 0..400u64 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            // Keys from a small range, so that rebinding is common.
            let key = ((state % 23) as usize, (state >> 32) as u32 % 2);
            assert_eq!(few.get(&key), reference.get(&key));
            assert_eq!(few.contains_key(&key), reference.contains_key(&key));
            assert_eq!(few.insert(key, round), reference.insert(key, round));
            assert_eq!(few.len(), reference.len());
        }
        for (key, value) in &reference {
            assert_eq!(few.get(key), Some(value));
        }
        assert!(reference.len() > FEW, "the test must reach the table");
    }

    #[test]
    fn a_small_map_never_reaches_the_table() {
        let mut few: FewMap<usize, usize> = FewMap::default();
        for k in 0..FEW {
            assert_eq!(few.insert(k, k), None);
            assert_eq!(few.insert(k, k + 10), Some(k));
        }
        assert!(few.many.is_empty());
        assert_eq!(few.get(&FEW), None);
        assert_eq!(few.insert(FEW, 0), None);
        assert_eq!(few.many.len(), 1);
        // A key in the array is rebound there, not shadowed in the table.
        assert_eq!(few.insert(0, 7), Some(10));
        assert_eq!(few.many.len(), 1);
        assert_eq!(few.get(&0), Some(&7));
    }

    #[test]
    fn dropping_a_map_drops_what_it_holds_in_both_parts() {
        let token = std::rc::Rc::new(());
        let mut few: FewMap<usize, std::rc::Rc<()>> = FewMap::default();
        for k in 0..3 * FEW {
            few.insert(k, std::rc::Rc::clone(&token));
        }
        assert_eq!(std::rc::Rc::strong_count(&token), 1 + 3 * FEW);
        drop(few);
        assert_eq!(std::rc::Rc::strong_count(&token), 1);
    }
}
