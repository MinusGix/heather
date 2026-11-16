//! Deferred premises (docs/kernel/deep-term-walks-design.md §3.3–3.4): the one
//! discipline conversion ([`crate::conv`]) and the checker
//! ([`crate::typing`]) share for walking a deep term without a native frame
//! per level.
//!
//! A rule's premises answer only yes or no, so they are a conjunction whose
//! order is free. A premise met [`SPINE_ITERATE_AT`] frames above the depth
//! the queue is drained at is queued instead of descended into, and every
//! queued premise is judged before any verdict leaves. A long list or vector
//! compared or checked element by element is then a loop.
//!
//! The state this module owns, and the phases it moves through, were eight
//! fields in `Conv` and four in `Tc`, each pair of copies kept in step by
//! hand (docs/kernel/kernel-implicit-state-review.md §2). Two defects happened
//! while they were built, both an order or threshold field read at one site
//! and not another; here each phase is a call:
//!
//! - **Walking.** [`PremiseQueue::should_defer`] at every premise.
//! - **A context** (the root, a popped premise, a speculative attempt)
//!   begins at the queue's length, its *floor*. Once anything is queued
//!   past the floor, every later premise in the context is queued too
//!   ([`PremiseQueue::past_floor`]), so the queue holds them in the order
//!   they were met.
//! - **Draining** ([`PremiseQueue::begin_drain`], [`PremiseQueue::pop`],
//!   [`PremiseQueue::judged`], [`PremiseQueue::end_drain`]) judges the
//!   premises past a mark from the drain's own depth, which becomes the
//!   threshold's base, and judges each premise's own queued premises before
//!   its next sibling: the recursive walk's order exactly. The order
//!   matters to the cost: a conjunction stops at its first failure, and
//!   judging a cheap failing premise after an expensive one can turn a
//!   refusal into running out of fuel.
//! - **An attempt** ([`PremiseQueue::open_attempt`],
//!   [`PremiseQueue::close_attempt`]) is a verdict of its own: its premises
//!   are drained before it counts as a success, and dropped with it when it
//!   fails.
//!
//! A memo `true` made while premises are queued stands on them. Conversion
//! keeps such entries in a [`VerdictMemo`], which records them as
//! provisional and takes them back when their queue is dropped. The checker
//! forgets its memos wholesale after a refusal that queued anything
//! (`Tc::forget_after_refusal`), which a refusal ending the gate makes
//! cheap.
//!
//! Everything here is `#[inline]` field reads on the hottest path of both
//! walks; the drain is cold.

use std::hash::Hash;

use crate::term::SPINE_ITERATE_AT;

/// The queue of deferred premises and where its current context and drain
/// begin.
pub(crate) struct PremiseQueue<I> {
    /// Queued premises. Within a drain, a stack in walk order: each
    /// premise's own queued premises are reversed onto the top as it
    /// finishes, so the first of them is popped next.
    items: Vec<I>,
    /// How many premises have ever been queued: a verdict whose subtree
    /// queued one stands on premises not yet judged ([`Self::queued_since`]).
    pushed: u64,
    /// The queue's length when the current context began (module docs).
    floor: usize,
    /// The depth the queue is being drained at: premises are queued
    /// [`SPINE_ITERATE_AT`] frames above it. A drain inside an attempt runs
    /// at the attempt's depth, and a threshold counted from zero there
    /// would queue each popped premise straight back.
    base: u32,
    /// Whether a drain at depth zero is running: a premise it popped that
    /// returns to depth zero leaves the rest to that loop, which keeps the
    /// drain one native frame instead of one per item.
    draining_at_top: bool,
}

/// What [`PremiseQueue::begin_drain`] replaced, for
/// [`PremiseQueue::end_drain`] to restore.
#[must_use]
pub(crate) struct Drain {
    mark: usize,
    floor: usize,
    base: u32,
    draining_at_top: bool,
}

/// What [`PremiseQueue::open_attempt`] replaced, for
/// [`PremiseQueue::close_attempt`] to restore.
#[must_use]
pub(crate) struct Attempt {
    mark: usize,
    floor: usize,
}

impl Attempt {
    /// The queue's length when the attempt began: its premises are the ones
    /// past it.
    pub(crate) fn mark(&self) -> usize {
        self.mark
    }
}

impl<I> PremiseQueue<I> {
    pub(crate) fn new() -> PremiseQueue<I> {
        PremiseQueue { items: Vec::new(), pushed: 0, floor: 0, base: 0, draining_at_top: false }
    }

    /// Whether a premise met at `depth` is queued rather than descended
    /// into: it is too deep, or something earlier in its context already
    /// was, and it waits its turn behind it.
    #[inline]
    pub(crate) fn should_defer(&self, depth: u32) -> bool {
        depth >= self.base + SPINE_ITERATE_AT || self.past_floor()
    }

    /// Whether anything was queued in the current context.
    #[inline]
    pub(crate) fn past_floor(&self) -> bool {
        self.items.len() > self.floor
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// The push count, to ask [`Self::queued_since`] about later.
    #[inline]
    pub(crate) fn epoch(&self) -> u64 {
        self.pushed
    }

    /// Whether a premise was queued since `epoch`.
    #[inline]
    pub(crate) fn queued_since(&self, epoch: u64) -> bool {
        self.pushed != epoch
    }

    /// Whether a drain at depth zero is running.
    #[inline]
    pub(crate) fn draining_at_top(&self) -> bool {
        self.draining_at_top
    }

    /// Queue a premise.
    #[cold]
    #[inline(never)]
    pub(crate) fn defer(&mut self, item: I) {
        self.items.push(item);
        self.pushed += 1;
    }

    /// Drop every premise past `mark`: the verdict they were premises of
    /// failed.
    pub(crate) fn drop_past(&mut self, mark: usize) {
        self.items.truncate(mark);
    }

    /// Begin judging the premises past `mark` at `depth`.
    pub(crate) fn begin_drain(&mut self, mark: usize, depth: u32) -> Drain {
        let saved = Drain { mark, floor: self.floor, base: self.base, draining_at_top: self.draining_at_top };
        self.base = depth;
        self.draining_at_top = self.draining_at_top || depth == 0;
        self.items[mark..].reverse();
        saved
    }

    /// The next premise to judge, as a context of its own, and the length to
    /// pass to [`Self::judged`] once it is. `None` once the drain's
    /// premises are all judged.
    pub(crate) fn pop(&mut self, drain: &Drain) -> Option<(I, usize)> {
        if self.items.len() <= drain.mark {
            return None;
        }
        let item = self.items.pop().expect("longer than the mark");
        let start = self.items.len();
        self.floor = start;
        Some((item, start))
    }

    /// A popped premise was judged a success: its own queued premises,
    /// past `start`, go next, in the order they were met.
    pub(crate) fn judged(&mut self, start: usize) {
        self.items[start..].reverse();
    }

    /// End a drain, successful or not; a failed one drops its premises.
    pub(crate) fn end_drain(&mut self, drain: Drain, ok: bool) {
        if !ok {
            self.items.truncate(drain.mark);
        }
        self.floor = drain.floor;
        self.base = drain.base;
        self.draining_at_top = drain.draining_at_top;
    }

    /// Begin a speculative attempt: a context of its own.
    pub(crate) fn open_attempt(&mut self) -> Attempt {
        let mark = self.items.len();
        Attempt { mark, floor: std::mem::replace(&mut self.floor, mark) }
    }

    /// End an attempt; a failed one drops its premises.
    pub(crate) fn close_attempt(&mut self, attempt: Attempt, ok: bool) {
        self.floor = attempt.floor;
        if !ok {
            self.items.truncate(attempt.mark);
        }
    }
}

/// Verdicts reached in one run, with the `true`s that stand on queued
/// premises recorded as **provisional**: each holds as long as its premises
/// do, which is until the queue they sit in is dropped. A failed attempt
/// takes back the ones made inside it, a refusal at depth zero takes back
/// all, and a successful drain at depth zero with no attempt open makes
/// them all final. (Not memoizing them at all would judge a shared subterm
/// once per occurrence.)
pub(crate) struct VerdictMemo<K> {
    /// Keyed by the domain's own closures (addresses and scope lengths at
    /// the value domain), so hashed as the arena's caches are.
    map: crate::value::PtrMap<K, bool>,
    /// The provisional entries, in the order they were made.
    provisional: Vec<K>,
    /// Attempts open: while any is, a successful drain at depth zero keeps
    /// the provisional log, since the attempt may still fail and take back
    /// the entries made after its mark.
    attempts_open: u32,
}

/// What [`VerdictMemo::open_attempt`] recorded.
#[must_use]
pub(crate) struct MemoAttempt {
    provisional: usize,
}

impl<K: Hash + Eq + Clone> VerdictMemo<K> {
    pub(crate) fn new() -> VerdictMemo<K> {
        VerdictMemo { map: Default::default(), provisional: Vec::new(), attempts_open: 0 }
    }

    #[inline]
    pub(crate) fn get(&self, key: &K) -> Option<bool> {
        self.map.get(key).copied()
    }

    /// Record a refusal: final, since no queued premise can turn a refusal
    /// into a success.
    pub(crate) fn refused(&mut self, key: K) {
        self.map.insert(key, false);
    }

    /// Record a success, provisionally when `provisional` (its subtree
    /// queued premises, or any are queued at all — it may stand on a
    /// provisional entry's memo hit, whose premises are still waiting).
    pub(crate) fn succeeded(&mut self, key: K, provisional: bool) {
        if provisional {
            self.provisional.push(key.clone());
        }
        self.map.insert(key, true);
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    #[inline]
    pub(crate) fn has_provisional(&self) -> bool {
        !self.provisional.is_empty()
    }

    pub(crate) fn open_attempt(&mut self) -> MemoAttempt {
        self.attempts_open += 1;
        MemoAttempt { provisional: self.provisional.len() }
    }

    /// End an attempt; a failed one takes back the provisional entries made
    /// inside it.
    pub(crate) fn close_attempt(&mut self, attempt: MemoAttempt, ok: bool) {
        self.attempts_open -= 1;
        if !ok {
            self.take_back(attempt.provisional);
        }
    }

    /// The queue settled at depth zero: a refusal takes back every
    /// provisional entry; a success makes them final unless an attempt is
    /// still open around it.
    pub(crate) fn settle_at_top(&mut self, ok: bool) {
        if !ok {
            self.take_back(0);
        } else if self.attempts_open == 0 {
            self.provisional.clear();
        }
    }

    fn take_back(&mut self, mark: usize) {
        if self.provisional.len() <= mark {
            return;
        }
        for key in self.provisional.drain(mark..) {
            self.map.remove(&key);
        }
    }
}
