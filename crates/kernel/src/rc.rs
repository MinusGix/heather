//! The shared pointer syntax is held by: `std::sync::Arc`, with a few words
//! beside the value for what the kernel has computed about the node.
//!
//! A syntax node is immutable and shared, and several questions about it are
//! pure functions of the subtree under it that every traversal asks again:
//! which local variables it reads, whether a weakening tail shows in its
//! scope, which global variables it mentions (`bounds.rs`). Not a table
//! keyed by the node's address: a table has to be found by hashing, misses the cache that the node itself is in, forgets
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
//! **Size.** A head is two words, and with `Arc`'s two counts a node is four
//! words over its value. The flags have no word of their own: they are the
//! top bits of the word that holds the mask of used indices, the one part of
//! an answer that is about cost and not about scope (`bounds::LocalUse`), so
//! nothing a traversal decides is squeezed to make room for them.
//!
//! The API is `Arc`'s, as associated functions, for the part of it the
//! compiler uses. An unsized payload (`[T]`, `str`, `dyn Trait`) stays a
//! plain `Arc`: no question is asked of one.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
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
    /// The mask of used indices in the low [`USES_BITS`] bits, the flags
    /// above them.
    state: AtomicU64,
    bound: AtomicU32,
    global: AtomicU32,
}

/// How many indices a head's mask of used indices covers.
pub(crate) const USES_BITS: u32 = 60;

const USES: u64 = (1 << USES_BITS) - 1;
const LOCAL: u64 = 1 << 60;
const HAS_WK: u64 = 1 << 61;
const GLOBAL: u64 = 1 << 62;

/// A property of a node's value that a client of the kernel has established
/// and wants not to establish again: one bit of the head, set by
/// [`Rc::mark`] and read by [`Rc::marked`].
///
/// The kernel reads no mark, so nothing it decides depends on one. What a
/// mark means is its client's, and the client's obligation is the head's
/// own: the property is a function of the value under the node and of
/// nothing else (no context, no registry, no environment), so that it is
/// true of the node for as long as the value is the one it was computed
/// from. A changed value has an empty head ([`Rc::make_mut`]).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Mark(u64);

impl Mark {
    /// The elaborator's "nothing under this type is the decoding of a code
    /// literal" (`heather_elab::inductive::decode_deep`).
    pub const DECODED: Mark = Mark(1 << 63);
}

impl Head {
    /// The node's local use, if it has been computed: its bound, whether a
    /// weakening tail shows, and its mask of used indices.
    #[inline]
    pub(crate) fn local(&self) -> Option<(u32, bool, u64)> {
        let state = self.state.load(Ordering::Acquire);
        if state & LOCAL == 0 {
            return None;
        }
        Some((self.bound.load(Ordering::Relaxed), state & HAS_WK != 0, state & USES))
    }

    /// The flag goes last and is released, with the mask in the same write,
    /// so a reader that sees it sees the bound written before it. `uses`
    /// names indices below [`USES_BITS`] only.
    #[inline]
    pub(crate) fn set_local(&self, bound: u32, has_wk: bool, uses: u64) {
        debug_assert!(uses & !USES == 0);
        self.bound.store(bound, Ordering::Relaxed);
        self.state.fetch_or(LOCAL | if has_wk { HAS_WK } else { 0 } | (uses & USES), Ordering::Release);
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

    /// Whether `mark` has been set on this node since its value was last
    /// changed.
    #[inline]
    pub fn marked(this: &Rc<T>, mark: Mark) -> bool {
        this.0.head.state.load(Ordering::Relaxed) & mark.0 != 0
    }

    /// Record that `mark`'s property holds of this node's value.
    #[inline]
    pub fn mark(this: &Rc<T>, mark: Mark) {
        this.0.head.state.fetch_or(mark.0, Ordering::Relaxed);
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
        // Every bit of each part, with the others beside it.
        let b = Rc::new(());
        Rc::head(&b).set_local(u32::MAX, false, USES);
        assert_eq!(Rc::head(&b).local(), Some((u32::MAX, false, USES)));
        assert_eq!(Rc::head(&b).global(), None);
        assert!(!Rc::marked(&b, Mark::DECODED));
        Rc::head(&b).set_global(u32::MAX);
        assert_eq!(Rc::head(&b).local(), Some((u32::MAX, false, USES)));
        assert_eq!(Rc::head(&b).global(), Some(u32::MAX));
        let c = Rc::new(());
        Rc::head(&c).set_local(0, true, 0);
        assert_eq!(Rc::head(&c).local(), Some((0, true, 0)));
        assert_eq!(Rc::head(&c).global(), None);
    }

    #[test]
    fn a_mark_stays_until_the_value_changes_and_is_no_answer() {
        let mut a = Rc::new(3u32);
        assert!(!Rc::marked(&a, Mark::DECODED));
        Rc::mark(&a, Mark::DECODED);
        assert!(Rc::marked(&a, Mark::DECODED));
        // A mark is not one of the kernel's answers, nor they a mark.
        assert_eq!(Rc::head(&a).local(), None);
        assert_eq!(Rc::head(&a).global(), None);
        Rc::head(&a).set_local(7, true, 5);
        Rc::head(&a).set_global(2);
        assert!(Rc::marked(&a, Mark::DECODED));
        assert_eq!(Rc::head(&a).local(), Some((7, true, 5)));
        let shared = Rc::clone(&a);
        assert!(Rc::marked(&shared, Mark::DECODED));
        *Rc::make_mut(&mut a) = 4;
        assert!(!Rc::marked(&a, Mark::DECODED));
        assert!(Rc::marked(&shared, Mark::DECODED));
        let b = Rc::new(0u32);
        Rc::head(&b).set_local(0, true, 0);
        Rc::head(&b).set_global(0);
        assert!(!Rc::marked(&b, Mark::DECODED));
    }

    /// The head is what a node costs over an `Arc`'s two counts.
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn a_head_is_two_words() {
        assert_eq!(std::mem::size_of::<Head>(), 16);
        assert_eq!(std::mem::size_of::<Rc<u8>>(), 8);
        assert_eq!(std::mem::size_of::<Option<Rc<u8>>>(), 8);
    }
}
