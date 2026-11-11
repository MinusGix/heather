//! The shared pointer syntax is held by: `std::sync::Arc`, with a few words
//! beside the value for what the kernel has computed about the node.
//!
//! A syntax node is immutable and shared, and several questions about it are
//! pure functions of the subtree under it that every traversal asks again:
//! which local variables it reads, whether a weakening tail shows in its
//! scope, which global variables it mentions (`bounds.rs`). The answers
//! used to live in tables keyed by the node's address. A table has to be
//! found by hashing, misses the cache that the node itself is in, forgets
//! what it evicts, and needs a weak reference per entry so that an address
//! stays its node's. Here the answer is in the node: [`Head`], written at
//! most once per question by the function that computes it and never by a
//! construction site. `Rc::new` makes an empty head, and that is the whole
//! of what building a node has to do with it.
//!
//! **What keeps an answer true.** The value under an `Rc` is reached mutably
//! only through [`Rc::make_mut`] and [`Rc::get_mut`], and both empty the head
//! first. Every other path to the value is `&T`, and syntax has no interior
//! mutability (DESIGN.md §Representation). So a head describes the value
//! beside it.
//!
//! **Threads.** A head is atomics, and two threads that answer the same
//! question about one node write the same answer. The flag that says an
//! answer is there is written last and read first ([`Head::set_local`]).
//!
//! The API is `Arc`'s, as associated functions, for the part of it the
//! compiler uses. An unsized payload (`[T]`, `str`, `dyn Trait`) stays a
//! plain `Arc`: no question is asked of one.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicU8, Ordering};
use std::sync::Arc;

pub struct Rc<T>(Arc<Node<T>>);

struct Node<T> {
    head: Head,
    value: T,
}

impl<T: Clone> Clone for Node<T> {
    /// A copy is another node: its head is its own to fill.
    fn clone(&self) -> Node<T> {
        Node { head: Head::default(), value: self.value.clone() }
    }
}

/// What has been computed about a node. Read and written by `bounds.rs`.
#[derive(Default)]
pub(crate) struct Head {
    uses: AtomicU64,
    bound: AtomicU32,
    global: AtomicU32,
    state: AtomicU8,
}

const LOCAL: u8 = 1;
const HAS_WK: u8 = 2;
const GLOBAL: u8 = 4;

impl Head {
    /// The node's local use, if it has been computed: its bound, whether a
    /// weakening tail shows, and its mask of used indices.
    #[inline]
    pub(crate) fn local(&self) -> Option<(u32, bool, u64)> {
        let state = self.state.load(Ordering::Acquire);
        if state & LOCAL == 0 {
            return None;
        }
        Some((self.bound.load(Ordering::Relaxed), state & HAS_WK != 0, self.uses.load(Ordering::Relaxed)))
    }

    /// The flag goes last and is released, so a reader that sees it sees
    /// the two words written before it.
    #[inline]
    pub(crate) fn set_local(&self, bound: u32, has_wk: bool, uses: u64) {
        self.bound.store(bound, Ordering::Relaxed);
        self.uses.store(uses, Ordering::Relaxed);
        self.state.fetch_or(LOCAL | if has_wk { HAS_WK } else { 0 }, Ordering::Release);
    }

    #[inline]
    pub(crate) fn global(&self) -> Option<u32> {
        if self.state.load(Ordering::Acquire) & GLOBAL == 0 {
            return None;
        }
        Some(self.global.load(Ordering::Relaxed))
    }

    #[inline]
    pub(crate) fn set_global(&self, bound: u32) {
        self.global.store(bound, Ordering::Relaxed);
        self.state.fetch_or(GLOBAL, Ordering::Release);
    }
}

impl<T> Rc<T> {
    #[inline]
    pub fn new(value: T) -> Rc<T> {
        Rc(Arc::new(Node { head: Head::default(), value }))
    }

    #[inline]
    pub fn ptr_eq(this: &Rc<T>, other: &Rc<T>) -> bool {
        Arc::ptr_eq(&this.0, &other.0)
    }

    /// The value's address: one per node, for as long as the node lives.
    #[inline]
    pub fn as_ptr(this: &Rc<T>) -> *const T {
        &this.0.value
    }

    #[inline]
    pub fn strong_count(this: &Rc<T>) -> usize {
        Arc::strong_count(&this.0)
    }

    #[inline]
    pub(crate) fn head(this: &Rc<T>) -> &Head {
        &this.0.head
    }

    /// The value, to change. Whatever was known about the node is forgotten
    /// first: it was known of the value as it was.
    #[inline]
    pub fn make_mut(this: &mut Rc<T>) -> &mut T
    where
        T: Clone,
    {
        let node = Arc::make_mut(&mut this.0);
        node.head = Head::default();
        &mut node.value
    }

    /// [`Rc::make_mut`] when no one else holds the node.
    #[inline]
    pub fn get_mut(this: &mut Rc<T>) -> Option<&mut T> {
        let node = Arc::get_mut(&mut this.0)?;
        node.head = Head::default();
        Some(&mut node.value)
    }

    #[inline]
    pub fn try_unwrap(this: Rc<T>) -> Result<T, Rc<T>> {
        Arc::try_unwrap(this.0).map(|node| node.value).map_err(Rc)
    }

    #[inline]
    pub fn unwrap_or_clone(this: Rc<T>) -> T
    where
        T: Clone,
    {
        Arc::try_unwrap(this.0).map(|node| node.value).unwrap_or_else(|shared| shared.value.clone())
    }
}

impl<T> Clone for Rc<T> {
    #[inline]
    fn clone(&self) -> Rc<T> {
        Rc(Arc::clone(&self.0))
    }
}

impl<T> Deref for Rc<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        &self.0.value
    }
}

impl<T> AsRef<T> for Rc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0.value
    }
}

impl<T> std::borrow::Borrow<T> for Rc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &self.0.value
    }
}

impl<T> From<T> for Rc<T> {
    #[inline]
    fn from(value: T) -> Rc<T> {
        Rc::new(value)
    }
}

impl<T: Default> Default for Rc<T> {
    fn default() -> Rc<T> {
        Rc::new(T::default())
    }
}

/// As the value prints, so a term's budgeted `Debug` is the node's.
impl<T: fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

/// One node is equal to itself without a look (`T: Eq`, so equality is
/// reflexive), as `Arc`'s comparison has it: comparing two dags that share
/// is then the size of what they do not share.
impl<T: Eq> PartialEq for Rc<T> {
    #[inline]
    fn eq(&self, other: &Rc<T>) -> bool {
        Rc::ptr_eq(self, other) || **self == **other
    }
}

impl<T: Eq> Eq for Rc<T> {}

impl<T: PartialOrd + Eq> PartialOrd for Rc<T> {
    fn partial_cmp(&self, other: &Rc<T>) -> Option<std::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: Ord> Ord for Rc<T> {
    fn cmp(&self, other: &Rc<T>) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash> Hash for Rc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_changed_value_has_an_empty_head() {
        // Unshared: changed in place, at the same address.
        let mut a = Rc::new(3u32);
        Rc::head(&a).set_local(7, true, 5);
        Rc::head(&a).set_global(2);
        let at = Rc::as_ptr(&a);
        *Rc::make_mut(&mut a) = 4;
        assert_eq!(Rc::as_ptr(&a), at);
        assert_eq!(Rc::head(&a).local(), None);
        assert_eq!(Rc::head(&a).global(), None);
        Rc::head(&a).set_local(1, false, 1);
        *Rc::get_mut(&mut a).expect("unshared") = 5;
        assert_eq!(Rc::head(&a).local(), None);

        // Shared: the copy is a new node and the original keeps its head.
        Rc::head(&a).set_local(7, true, 5);
        let b = Rc::clone(&a);
        let mut c = Rc::clone(&a);
        *Rc::make_mut(&mut c) = 6;
        assert!(!Rc::ptr_eq(&b, &c));
        assert_eq!(Rc::head(&b).local(), Some((7, true, 5)));
        assert_eq!(Rc::head(&c).local(), None);
        assert_eq!((*b, *c), (5, 6));
    }

    #[test]
    fn a_head_answers_each_question_once_it_is_set() {
        let a = Rc::new(());
        assert_eq!(Rc::head(&a).local(), None);
        assert_eq!(Rc::head(&a).global(), None);
        Rc::head(&a).set_global(9);
        assert_eq!(Rc::head(&a).local(), None);
        assert_eq!(Rc::head(&a).global(), Some(9));
        Rc::head(&a).set_local(0, false, 0);
        assert_eq!(Rc::head(&a).local(), Some((0, false, 0)));
        assert_eq!(Rc::head(&a).global(), Some(9));
    }

    /// The head is what a node costs over an `Arc`'s two counts.
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn a_head_is_three_words() {
        assert_eq!(std::mem::size_of::<Head>(), 24);
        assert_eq!(std::mem::size_of::<Rc<u8>>(), 8);
        assert_eq!(std::mem::size_of::<Option<Rc<u8>>>(), 8);
    }
}
