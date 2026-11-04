//! A persistent snoc list: the shape of every per-binder column of [`Cx`].
//!
//! [`Cx`] is cloned wherever elaboration forks (a probe, a retry, a checking
//! attempt, a diagnostic's context), and each of its columns used to be a
//! `Vec`, so every clone copied every binder's name, alias and type variable
//! afresh (issues/elab-cx-persistent-binders.md). The kernel's `CtxEntries`
//! made the same move for Γ (issues/context-representation-clones.md); this
//! is the elaborator's half: a clone is one refcount bump, a push allocates
//! one node and shares the rest.
//!
//! Positions are counted from the **outermost** end, as they were when the
//! columns were vectors, so `spine[i]` still names the binder `gamma.entries[i]`
//! does. What changed is cost: positional access and outermost-first
//! iteration walk the spine (O(|spine|), the latter collecting references
//! first), while the innermost-first walk ([`Spine::iter_inner`]), which is
//! what shadowing lookups want, allocates nothing.
//!
//! [`Cx`]: crate::context::Cx

use std::sync::Arc as Rc;

pub(crate) struct Spine<T>(Option<Rc<Node<T>>>);

struct Node<T> {
    item: T,
    /// Length of the spine ending at this node: `rest.len() + 1`.
    len: u32,
    rest: Spine<T>,
}

impl<T> Clone for Spine<T> {
    fn clone(&self) -> Self {
        Spine(self.0.clone())
    }
}

impl<T> Default for Spine<T> {
    fn default() -> Self {
        Spine(None)
    }
}

impl<T> Drop for Spine<T> {
    /// Iterative, so dropping the last handle on a long spine does not
    /// recurse once per node.
    fn drop(&mut self) {
        let mut cur = self.0.take();
        while let Some(node) = cur {
            match Rc::try_unwrap(node) {
                Ok(mut node) => cur = node.rest.0.take(),
                Err(_) => break,
            }
        }
    }
}

impl<T> Spine<T> {
    pub(crate) fn new() -> Self {
        Spine(None)
    }

    pub(crate) fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.len as usize)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// `self, item`: O(1), sharing `self`.
    pub(crate) fn push(&mut self, item: T) {
        let len = self.len() as u32 + 1;
        let rest = Spine(self.0.take());
        self.0 = Some(Rc::new(Node { item, len, rest }));
    }

    pub(crate) fn clear(&mut self) {
        *self = Spine::new();
    }

    /// Whether the two are one spine (the same allocation, or both empty):
    /// an O(1) sufficient condition for equality.
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(a), Some(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// Innermost first, without allocating: the order a shadowing lookup
    /// wants.
    pub(crate) fn iter_inner(&self) -> InnerIter<'_, T> {
        InnerIter(self)
    }

    /// Outermost first, as `Vec::iter` was. Collects the references first,
    /// since the spine runs the other way.
    pub(crate) fn iter(&self) -> std::vec::IntoIter<&T> {
        let mut v: Vec<&T> = self.iter_inner().collect();
        v.reverse();
        v.into_iter()
    }

    /// The item at position `i` from the outermost end.
    pub(crate) fn get(&self, i: usize) -> Option<&T> {
        let n = self.len();
        if i >= n {
            return None;
        }
        self.iter_inner().nth(n - 1 - i)
    }

    /// The position (from the outermost end) of the innermost item `pred`
    /// accepts: `Vec::iter().rposition`, without the allocation.
    pub(crate) fn rposition(&self, mut pred: impl FnMut(&T) -> bool) -> Option<usize> {
        let n = self.len();
        self.iter_inner().position(|x| pred(x)).map(|k| n - 1 - k)
    }

    /// Cut back to the outermost `k` items, sharing them. Like
    /// `Vec::truncate`, a `k` past the end leaves the spine as it is.
    pub(crate) fn truncate(&mut self, k: usize) {
        let mut cur = self.clone();
        while cur.len() > k {
            let rest = cur.0.as_ref().expect("length is cached").rest.clone();
            cur = rest;
        }
        *self = cur;
    }

    /// The outermost `k` items (all of them if `k` is past the end).
    pub(crate) fn prefix(&self, k: usize) -> Self {
        let mut out = self.clone();
        out.truncate(k);
        out
    }
}

impl<T: Clone> Spine<T> {
    /// Outermost first, owned.
    pub(crate) fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }
}

pub(crate) struct InnerIter<'a, T>(&'a Spine<T>);

impl<'a, T> Iterator for InnerIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let node = self.0.0.as_ref()?;
        self.0 = &node.rest;
        Some(&node.item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.0.len();
        (n, Some(n))
    }
}

impl<T> ExactSizeIterator for InnerIter<'_, T> {}

impl<T> std::ops::Index<usize> for Spine<T> {
    type Output = T;

    fn index(&self, i: usize) -> &T {
        self.get(i).unwrap_or_else(|| panic!("spine position {i} out of range for length {}", self.len()))
    }
}

impl<T> FromIterator<T> for Spine<T> {
    /// From an outermost-first iterator.
    fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Self {
        let mut s = Spine::new();
        s.extend(it);
        s
    }
}

impl<T> Extend<T> for Spine<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, it: I) {
        for x in it {
            self.push(x);
        }
    }
}

impl<T> From<Vec<T>> for Spine<T> {
    fn from(v: Vec<T>) -> Self {
        v.into_iter().collect()
    }
}

impl<T: PartialEq> PartialEq for Spine<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && (self.ptr_eq(other) || self.iter_inner().zip(other.iter_inner()).all(|(a, b)| a == b))
    }
}

impl<T: PartialEq, const N: usize, U> PartialEq<[U; N]> for Spine<T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &[U; N]) -> bool {
        self.len() == N && self.iter().zip(other.iter()).all(|(a, b)| *a == *b)
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Spine<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// One binder's surface data, parallel to its `gamma.entries` entry: the
/// name it was written under and the implicitness skeleton of its written
/// type, where it had one (docs/implicit-binders-design.md §3.1).
pub(crate) struct Binder {
    pub(crate) name: Rc<str>,
    pub(crate) skel: Option<Rc<crate::Skel>>,
}

impl Clone for Binder {
    fn clone(&self) -> Self {
        Binder { name: Rc::clone(&self.name), skel: self.skel.clone() }
    }
}

/// [`Cx`]'s binder column: names and skeletons on one [`Spine`], read
/// through name-shaped accessors so that `cx.names[i]` is still the `i`-th
/// binder's name (outermost first) and a lookup still compares names.
///
/// [`Cx`]: crate::context::Cx
#[derive(Clone, Default)]
pub(crate) struct Binders(Spine<Binder>);

impl Binders {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn push(&mut self, name: impl Into<Rc<str>>, skel: Option<Rc<crate::Skel>>) {
        self.0.push(Binder { name: name.into(), skel });
    }

    pub(crate) fn truncate(&mut self, k: usize) {
        self.0.truncate(k);
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    /// Drop the innermost binder: O(1).
    pub(crate) fn pop(&mut self) {
        self.0.truncate(self.len().saturating_sub(1));
    }

    /// The name `i` binders out from the innermost one: the binder
    /// `LocalVar(i)` refers to. Walks `i` nodes.
    pub(crate) fn nth_inner(&self, i: usize) -> Option<&str> {
        self.iter_inner().nth(i)
    }

    /// The `i`-th binder's name, outermost first.
    pub(crate) fn get(&self, i: usize) -> Option<&str> {
        self.0.get(i).map(|b| &*b.name)
    }

    /// The `i`-th binder's skeleton.
    pub(crate) fn skel(&self, i: usize) -> Option<&Rc<crate::Skel>> {
        self.0.get(i).and_then(|b| b.skel.as_ref())
    }

    /// Names, outermost first (collects references; see [`Spine::iter`]).
    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &str> + ExactSizeIterator {
        self.0.iter().map(|b| &*b.name)
    }

    /// Names, innermost first, without allocating.
    pub(crate) fn iter_inner(&self) -> impl Iterator<Item = &str> + ExactSizeIterator {
        self.0.iter_inner().map(|b| &*b.name)
    }

    /// Whether some binder is named `name`.
    pub(crate) fn contains(&self, name: &str) -> bool {
        self.iter_inner().any(|n| n == name)
    }

    /// The position of the innermost binder named `name`: the binder a use
    /// of `name` refers to.
    pub(crate) fn lookup(&self, name: &str) -> Option<usize> {
        self.0.rposition(|b| &*b.name == name)
    }

    /// The same binders with each name passed through `f` (one rebuild of
    /// the spine).
    pub(crate) fn renamed(&self, mut f: impl FnMut(&str) -> String) -> Binders {
        Binders(self.0.iter().map(|b| Binder { name: f(&b.name).into(), skel: b.skel.clone() }).collect())
    }
}

impl std::ops::Index<usize> for Binders {
    type Output = str;

    fn index(&self, i: usize) -> &str {
        &self.0[i].name
    }
}

impl<const N: usize> PartialEq<[&str; N]> for Binders {
    fn eq(&self, other: &[&str; N]) -> bool {
        self.len() == N && self.iter().zip(other.iter()).all(|(a, b)| a == *b)
    }
}

impl std::fmt::Debug for Binders {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_count_from_the_outermost_end() {
        let mut s: Spine<u32> = (0..5).collect();
        assert_eq!(s.len(), 5);
        assert_eq!(s[0], 0);
        assert_eq!(s[4], 4);
        assert_eq!(s.iter().copied().collect::<Vec<_>>(), [0, 1, 2, 3, 4]);
        assert_eq!(s.iter_inner().copied().collect::<Vec<_>>(), [4, 3, 2, 1, 0]);
        assert_eq!(s.rposition(|x| *x < 3), Some(2));
        let shared = s.clone();
        s.truncate(2);
        assert_eq!(s.to_vec(), [0, 1]);
        assert_eq!(shared.len(), 5);
        s.push(9);
        assert_eq!(s.to_vec(), [0, 1, 9]);
        assert!(s.prefix(2).ptr_eq(&shared.prefix(2)));
    }

    #[test]
    fn a_lookup_finds_the_innermost_shadowing_binder() {
        let mut b = Binders::default();
        b.push("x", None);
        b.push("y", None);
        b.push("x", None);
        assert_eq!(b.lookup("x"), Some(2));
        assert_eq!(b.lookup("y"), Some(1));
        assert_eq!(b.lookup("z"), None);
        assert_eq!(&b[0], "x");
        assert!(b.contains("y"));
    }

    #[test]
    fn dropping_a_long_spine_does_not_recurse() {
        let s: Spine<u32> = (0..1_000_000).collect();
        drop(s);
    }
}
