//! Succinct programs for repeated one-hole constructor contexts.
//!
//! A program denotes a context, not a materialized constructor tree.  `Run`
//! stores at most `u64::MAX` repetitions; overflowing adjacent runs remain a
//! shared `Compose` instead of growing an unbounded counter.  Nothing here
//! knows which inductive or constructor a context belongs to.

use std::collections::HashMap;
use std::fmt;
use std::num::NonZeroU64;
use std::sync::Arc as Rc;

use heather_numeral::Numeral;

use crate::fmt::node;

/// A shared straight-line program for one-hole constructor contexts.
pub enum ContextProgram<C> {
    Run { context: C, count: NonZeroU64 },
    /// `outer(inner[-])`. Built only by [`ContextProgram::compose`], which
    /// fills in the two summaries every walk would otherwise recompute:
    /// `len`, how many contexts the composition holds, and `uniform`, the
    /// one context every run below repeats, when there is one. A wide
    /// number is a uniform program, so its length is read here, not counted
    /// over its graph.
    Compose {
        outer: Rc<ContextProgram<C>>,
        inner: Rc<ContextProgram<C>>,
        len: Numeral,
        uniform: Option<C>,
    },
}

/// Residual programs after cancelling an equal outer prefix.
pub struct CancelledPrefix<C> {
    pub left: Option<Rc<ContextProgram<C>>>,
    pub right: Option<Rc<ContextProgram<C>>>,
    /// The prefix both sides lost, as a program over the shared fragments
    /// it was made of: a fold that produces `q` constructors per cancelled
    /// pair (`max`) iterates its algebra over exactly this.
    pub cancelled: Option<Rc<ContextProgram<C>>>,
    pub changed: bool,
    /// Unique program-pair and cursor nodes inspected. Callers charge this
    /// against their ordinary reduction/conversion budget.
    pub inspected: u64,
}

/// The caller's bound was reached before cancellation could justify a
/// residual. This is exhaustion, not evidence that the programs differ.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CancellationExhausted;

struct InspectionBudget {
    remaining: u64,
    inspected: u64,
}

impl InspectionBudget {
    fn new(limit: u64) -> Self {
        Self { remaining: limit, inspected: 0 }
    }

    fn spend(&mut self) -> Result<(), CancellationExhausted> {
        if self.remaining == 0 {
            return Err(CancellationExhausted);
        }
        self.remaining -= 1;
        self.inspected += 1;
        Ok(())
    }
}

type ProgramPair = (usize, usize);

/// A bounded sufficient equivalence test for two independently allocated
/// program DAGs with the same sharing construction. Pair memoization makes a
/// depth-N doubling DAG cost O(N), not O(2^N). A shape mismatch is merely
/// `false`: the cursor can still find denotationally equal prefixes across
/// different associations and run boundaries.
struct Bisimulation<C> {
    memo: HashMap<ProgramPair, bool>,
    retained: Vec<Rc<ContextProgram<C>>>,
}

impl<C: Clone + Eq> Bisimulation<C> {
    fn new() -> Self {
        Self { memo: HashMap::new(), retained: Vec::new() }
    }

    fn key(left: &Rc<ContextProgram<C>>, right: &Rc<ContextProgram<C>>) -> ProgramPair {
        // The memo retains both nodes for every inserted key, so allocator
        // reuse cannot alias it. Addresses are identity tokens only; they are
        // never dereferenced.
        (Rc::as_ptr(left) as usize, Rc::as_ptr(right) as usize)
    }

    fn equivalent(
        &mut self,
        left: &Rc<ContextProgram<C>>,
        right: &Rc<ContextProgram<C>>,
        budget: &mut InspectionBudget,
    ) -> Result<bool, CancellationExhausted> {
        if ContextProgram::equivalent_fast(left, right) {
            return Ok(true);
        }

        enum Visit<C> {
            Enter(Rc<ContextProgram<C>>, Rc<ContextProgram<C>>),
            Finish(ProgramPair, ProgramPair, ProgramPair),
        }

        let root = Self::key(left, right);
        if let Some(result) = self.memo.get(&root) {
            return Ok(*result);
        }
        let mut work = vec![Visit::Enter(Rc::clone(left), Rc::clone(right))];
        while let Some(visit) = work.pop() {
            match visit {
                Visit::Enter(left, right) => {
                    let key = Self::key(&left, &right);
                    if self.memo.contains_key(&key) {
                        continue;
                    }
                    if ContextProgram::equivalent_fast(&left, &right) {
                        self.retained.extend([Rc::clone(&left), Rc::clone(&right)]);
                        self.memo.insert(key, true);
                        continue;
                    }
                    budget.spend()?;
                    self.retained.extend([Rc::clone(&left), Rc::clone(&right)]);
                    // Programs of different lengths denote different
                    // contexts, whatever their shapes.
                    if left.len() != right.len() {
                        self.memo.insert(key, false);
                        continue;
                    }
                    match (&*left, &*right) {
                        (
                            ContextProgram::Run { context: lc, count: ln },
                            ContextProgram::Run { context: rc, count: rn },
                        ) => {
                            self.memo.insert(key, lc == rc && ln == rn);
                        }
                        (
                            ContextProgram::Compose { outer: lo, inner: li, .. },
                            ContextProgram::Compose { outer: ro, inner: ri, .. },
                        ) => {
                            let outer = Self::key(lo, ro);
                            let inner = Self::key(li, ri);
                            work.push(Visit::Finish(key, outer, inner));
                            if !self.memo.contains_key(&inner) {
                                work.push(Visit::Enter(Rc::clone(li), Rc::clone(ri)));
                            }
                            if !self.memo.contains_key(&outer) {
                                work.push(Visit::Enter(Rc::clone(lo), Rc::clone(ro)));
                            }
                        }
                        _ => {
                            self.memo.insert(key, false);
                        }
                    }
                }
                Visit::Finish(key, outer, inner) => {
                    let result = self.memo.get(&outer).copied().unwrap_or(false)
                        && self.memo.get(&inner).copied().unwrap_or(false);
                    self.memo.insert(key, result);
                }
            }
        }
        Ok(self.memo.get(&root).copied().unwrap_or(false))
    }
}

/// `a + b` over counts.
fn count_add(a: &Numeral, b: &Numeral) -> Numeral {
    if let (Some(a), Some(b)) = (a.as_u64(), b.as_u64()) {
        if let Some(sum) = a.checked_add(b) {
            return Numeral::from_u64(sum);
        }
    }
    let (a, b) = (a.limbs(), b.limbs());
    let mut out = Vec::with_capacity(a.len().max(b.len()) + 1);
    let mut carry = false;
    for i in 0..a.len().max(b.len()) {
        let (x, c1) = a.get(i).copied().unwrap_or(0).overflowing_add(b.get(i).copied().unwrap_or(0));
        let (x, c2) = x.overflowing_add(u64::from(carry));
        out.push(x);
        carry = c1 || c2;
    }
    out.push(u64::from(carry));
    Numeral::from_limbs(out)
}

/// `a - b` over counts, for `b <= a`.
fn count_sub(a: &Numeral, b: &Numeral) -> Numeral {
    debug_assert!(b <= a);
    if let (Some(a), Some(b)) = (a.as_u64(), b.as_u64()) {
        return Numeral::from_u64(a - b);
    }
    let (a, b) = (a.limbs(), b.limbs());
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = false;
    for (i, &x) in a.iter().enumerate() {
        let (x, b1) = x.overflowing_sub(b.get(i).copied().unwrap_or(0));
        let (x, b2) = x.overflowing_sub(u64::from(borrow));
        out.push(x);
        borrow = b1 || b2;
    }
    debug_assert!(!borrow);
    Numeral::from_limbs(out)
}

/// A cursor's front once it is known to repeat one context: the program
/// standing for it, a run or a uniform composition, and its length.
///
/// Two numbers built by different routes are not bisimilar node for node,
/// and a cursor that opened them fragment by fragment paid their value over
/// the largest run (`issues/kernel-wide-run-comparison.md`). A uniform
/// front is never opened: everything about it is its context and its
/// length, so two such fronts cancel by one subtraction, and only the
/// longer one is cut, along one path.
struct Front<C> {
    context: C,
    program: Rc<ContextProgram<C>>,
    len: Numeral,
}

struct Cursor<C> {
    pending: Vec<Rc<ContextProgram<C>>>,
    run: Option<Front<C>>,
}

impl<C: Clone + Eq> Cursor<C> {
    fn new(program: Rc<ContextProgram<C>>) -> Self {
        Self { pending: vec![program], run: None }
    }

    fn front(&self) -> Option<&Rc<ContextProgram<C>>> {
        if self.run.is_none() { self.pending.last() } else { None }
    }

    fn pop_front(&mut self) {
        debug_assert!(self.run.is_none());
        self.pending.pop();
    }

    /// Make the next piece the front when it repeats one context, a run or
    /// a uniform composition alike, and open a mixed composition otherwise.
    fn step(&mut self, budget: &mut InspectionBudget) -> Result<(), CancellationExhausted> {
        if self.run.is_some() {
            return Ok(());
        }
        let Some(program) = self.pending.pop() else { return Ok(()) };
        budget.spend()?;
        if let Some(context) = program.uniform() {
            let (context, len) = (context.clone(), program.len());
            self.run = Some(Front { context, program, len });
            return Ok(());
        }
        let ContextProgram::Compose { outer, inner, .. } = &*program else {
            unreachable!("a run repeats its context")
        };
        self.pending.push(Rc::clone(inner));
        self.pending.push(Rc::clone(outer));
        Ok(())
    }

    /// Absorb the following piece into the front when it repeats the
    /// front's context; `false` when it does not, or there is none.
    fn widen(&mut self) -> bool {
        let front = self.run.as_mut().expect("widen follows step");
        let Some(next) = self.pending.last() else { return false };
        if next.uniform() != Some(&front.context) {
            return false;
        }
        let next = self.pending.pop().unwrap();
        front.len = count_add(&front.len, &next.len());
        front.program = ContextProgram::append(Rc::clone(&front.program), next);
        true
    }

    /// Drop `k` contexts, at most the front's length, from the front.
    fn consume(&mut self, k: &Numeral, budget: &mut InspectionBudget) -> Result<(), CancellationExhausted> {
        let front = self.run.as_mut().expect("consume follows step");
        if *k == front.len {
            self.run = None;
            return Ok(());
        }
        front.program = ContextProgram::drop_prefix(&front.program, k.clone(), budget)?;
        front.len = count_sub(&front.len, k);
        Ok(())
    }

    fn remainder(mut self) -> Option<Rc<ContextProgram<C>>> {
        let mut pieces = Vec::with_capacity(self.pending.len() + usize::from(self.run.is_some()));
        if let Some(front) = self.run.take() {
            pieces.push(front.program);
        }
        while let Some(piece) = self.pending.pop() {
            pieces.push(piece);
        }
        let mut pieces = pieces.into_iter().rev();
        let mut result = pieces.next()?;
        for outer in pieces {
            result = ContextProgram::compose(outer, result);
        }
        Some(result)
    }

    fn exhausted(&self) -> bool {
        self.run.is_none() && self.pending.is_empty()
    }
}

impl<C: fmt::Debug> fmt::Debug for ContextProgram<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            ContextProgram::Run { context, count } => {
                write!(f, "run({context:?}; {count})")
            }
            ContextProgram::Compose { outer, inner, .. } => {
                write!(f, "compose({outer:?}; {inner:?})")
            }
        })
    }
}

impl<C> ContextProgram<C> {
    /// How many contexts `program` holds.
    pub fn len(&self) -> Numeral {
        match self {
            ContextProgram::Run { count, .. } => Numeral::from_u64(count.get()),
            ContextProgram::Compose { len, .. } => len.clone(),
        }
    }

    /// The context every run below repeats, when there is one.
    pub fn uniform(&self) -> Option<&C> {
        match self {
            ContextProgram::Run { context, .. } => Some(context),
            ContextProgram::Compose { uniform, .. } => uniform.as_ref(),
        }
    }

    /// The exact number of contexts represented by `program`, provided it is
    /// at most `limit`; read off the node, whatever the size of its graph.
    /// `None` means only "larger than the bound".
    pub fn repetition_count_up_to(program: &Rc<Self>, limit: u64) -> Option<u64> {
        match &**program {
            ContextProgram::Run { count, .. } => Some(count.get()).filter(|n| *n <= limit),
            ContextProgram::Compose { len, .. } => len.as_u64().filter(|n| *n <= limit),
        }
    }
}

impl<C: Clone + Eq> ContextProgram<C> {
    pub fn run(context: C, count: NonZeroU64) -> Rc<Self> {
        Rc::new(ContextProgram::Run { context, count })
    }

    /// Put `count` copies of `context` outside `inner`, merging one adjacent
    /// run only when its `u64` count does not overflow.
    pub fn prepend(context: C, count: NonZeroU64, inner: Rc<Self>) -> Rc<Self> {
        if let ContextProgram::Run { context: next, count: n } = &*inner {
            if *next == context {
                if let Some(sum) = count.get().checked_add(n.get()) {
                    return Self::run(context, NonZeroU64::new(sum).unwrap());
                }
            }
        }
        Self::compose(Self::run(context, count), inner)
    }

    pub fn compose(outer: Rc<Self>, inner: Rc<Self>) -> Rc<Self> {
        let len = count_add(&outer.len(), &inner.len());
        let uniform = match (outer.uniform(), inner.uniform()) {
            (Some(o), Some(i)) if o == i => Some(o.clone()),
            _ => None,
        };
        Rc::new(ContextProgram::Compose { outer, inner, len, uniform })
    }

    /// `outer` outside `inner`, merged into one saturated run when both are
    /// runs of the same context whose `u64` counts add without overflow, and
    /// composed otherwise. This is the construction-time counterpart of
    /// [`ContextProgram::prepend`]: a fold that maps a run onto a tail which
    /// turns out to be another run keeps one fragment, not a chain of them.
    pub fn append(outer: Rc<Self>, inner: Rc<Self>) -> Rc<Self> {
        if let (
            ContextProgram::Run { context, count },
            ContextProgram::Run { context: next, count: n },
        ) = (&*outer, &*inner)
        {
            if context == next {
                if let Some(sum) = count.get().checked_add(n.get()) {
                    return Self::run(context.clone(), NonZeroU64::new(sum).unwrap());
                }
            }
        }
        Self::compose(outer, inner)
    }

    /// A cheap sufficient test that two programs denote the same context.
    /// Object identity remains the broadest constant-time case; independently
    /// allocated runs are just as easy because their whole denotation is the
    /// pair `(context, count)`. The composed case deliberately stops at shared
    /// children rather than walking a potentially exponential DAG.
    pub fn equivalent_fast(left: &Rc<Self>, right: &Rc<Self>) -> bool {
        Rc::ptr_eq(left, right)
            || match (&**left, &**right) {
                (
                    ContextProgram::Run { context: lc, count: ln },
                    ContextProgram::Run { context: rc, count: rn },
                ) => lc == rc && ln == rn,
                (
                    ContextProgram::Compose { outer: lo, inner: li, .. },
                    ContextProgram::Compose { outer: ro, inner: ri, .. },
                ) => Rc::ptr_eq(lo, ro) && Rc::ptr_eq(li, ri),
                _ => false,
            }
    }

    /// `context` repeated `n` times, for `n > 0`, in the canonical shape:
    /// doubling from the top bit, [`ContextProgram::append`] merging runs
    /// while their counts add in a `u64` and composing them, shared, past
    /// that, so the top 64 bits become one run and each further bit adds at
    /// most two nodes — `O(bits)`, the shape arithmetic that overflows a
    /// run already produces.
    pub fn of_count(context: C, n: &Numeral) -> Rc<Self> {
        if let Some(count) = n.as_u64() {
            return Self::run(context, NonZeroU64::new(count).expect("a nonzero count"));
        }
        let one = || Self::run(context.clone(), NonZeroU64::MIN);
        let mut acc: Option<Rc<Self>> = None;
        for i in (0..n.bits()).rev() {
            acc = acc.map(|a| Self::append(Rc::clone(&a), a));
            if n.bit(i) {
                acc = Some(match acc {
                    None => one(),
                    Some(a) => Self::append(one(), a),
                });
            }
        }
        acc.expect("a nonzero count has a set bit")
    }

    /// `program` without its outer `k` contexts, for `0 < k < len(program)`
    /// over a uniform `program`. One path is descended and rebuilt, so the
    /// residual shares every subprogram off that path; each composition on
    /// the path is one inspection.
    fn drop_prefix(
        program: &Rc<Self>,
        mut k: Numeral,
        budget: &mut InspectionBudget,
    ) -> Result<Rc<Self>, CancellationExhausted> {
        let mut current = Rc::clone(program);
        let mut inners = Vec::new();
        let mut rest = loop {
            if k.is_zero() {
                break current;
            }
            match &*current {
                ContextProgram::Run { context, count } => {
                    let k = k.as_u64().expect("k is below this run's count");
                    break Self::run(context.clone(), NonZeroU64::new(count.get() - k).unwrap());
                }
                ContextProgram::Compose { outer, inner, .. } => {
                    budget.spend()?;
                    let skipped = outer.len();
                    let (outer, inner) = (Rc::clone(outer), Rc::clone(inner));
                    if k >= skipped {
                        k = count_sub(&k, &skipped);
                        current = inner;
                    } else {
                        inners.push(inner);
                        current = outer;
                    }
                }
            }
        };
        while let Some(inner) = inners.pop() {
            rest = Self::append(rest, inner);
        }
        Ok(rest)
    }

    /// Cancel an equal sequence of outer contexts without visiting its
    /// represented constructor nodes. Bisimilar DAG fronts are skipped by
    /// unique node pairs; the fallback walk is over run/composition fragments.
    /// Residual fragments retain the original shared subprograms. A differing
    /// context is a hard boundary, not a claim about it. All structural work
    /// shares `inspection_limit`; exhaustion returns no verdict or residual.
    pub fn cancel_matching_prefix(
        left: Rc<Self>,
        right: Rc<Self>,
        inspection_limit: u64,
    ) -> Result<CancelledPrefix<C>, CancellationExhausted> {
        let mut budget = InspectionBudget::new(inspection_limit);
        if Self::equivalent_fast(&left, &right) {
            return Ok(CancelledPrefix {
                left: None,
                right: None,
                cancelled: Some(left),
                changed: true,
                inspected: 0,
            });
        }
        let mut left = Cursor::new(left);
        let mut right = Cursor::new(right);
        let mut bisimulation = Bisimulation::new();
        let mut changed = false;
        // The cancelled fragments, outermost first.
        let mut cancelled: Vec<Rc<Self>> = Vec::new();
        loop {
            while left.run.is_none() && right.run.is_none() {
                let (Some(l), Some(r)) = (left.front(), right.front()) else {
                    break;
                };
                // Two fronts that each repeat one context, the same one,
                // are compared by length below, which decides everything a
                // bisimulation would and costs their graphs, not their
                // product.
                if let (Some(lc), Some(rc)) = (l.uniform(), r.uniform()) {
                    if lc == rc {
                        break;
                    }
                }
                if !bisimulation.equivalent(l, r, &mut budget)? {
                    break;
                }
                cancelled.push(Rc::clone(l));
                left.pop_front();
                right.pop_front();
                changed = true;
            }
            if left.run.is_none() && !left.exhausted() {
                left.step(&mut budget)?;
            }
            if right.run.is_none() && !right.exhausted() {
                right.step(&mut budget)?;
            }
            if (left.run.is_none() && !left.exhausted())
                || (right.run.is_none() && !right.exhausted())
            {
                continue;
            }
            let (Some(l), Some(r)) = (&left.run, &right.run) else {
                break;
            };
            if l.context != r.context {
                break;
            }
            // Widen the shorter front while it is the shorter one: only
            // the common length is cancelled, so the longer side is never
            // analysed past it, and a short number against a wide one
            // costs the short one.
            loop {
                let (l, r) = (left.run.as_ref().unwrap(), right.run.as_ref().unwrap());
                let grew = match l.len.cmp(&r.len) {
                    std::cmp::Ordering::Less => left.widen(),
                    std::cmp::Ordering::Greater => right.widen(),
                    std::cmp::Ordering::Equal => false,
                };
                if !grew {
                    break;
                }
            }
            let (l, r) = (left.run.as_ref().unwrap(), right.run.as_ref().unwrap());
            // The shorter front is exactly the cancelled stretch.
            let shorter = if l.len <= r.len { l } else { r };
            let count = shorter.len.clone();
            cancelled.push(Rc::clone(&shorter.program));
            left.consume(&count, &mut budget)?;
            right.consume(&count, &mut budget)?;
            changed = true;
        }
        let cancelled = cancelled
            .into_iter()
            .rev()
            .reduce(|inner, outer| Self::append(outer, inner));
        Ok(CancelledPrefix {
            left: left.remainder(),
            right: right.remainder(),
            cancelled,
            changed,
            inspected: budget.inspected,
        })
    }

    /// The outer constructor and a shared program for everything beneath it.
    /// `None` for the remainder means the caller has reached the program's
    /// hole. The rebuilding walk is iterative so a hostile composition spine
    /// does not consume the native stack.
    pub fn uncons(program: &Rc<Self>) -> (&C, Option<Rc<Self>>) {
        let mut current = program;
        let mut inners = Vec::new();
        loop {
            match &**current {
                ContextProgram::Run { context, count } => {
                    let mut rest = NonZeroU64::new(count.get() - 1)
                        .map(|n| Self::run(context.clone(), n));
                    while let Some(inner) = inners.pop() {
                        rest = Some(match rest {
                            Some(outer) => Self::compose(outer, inner),
                            None => inner,
                        });
                    }
                    return (context, rest);
                }
                ContextProgram::Compose { outer, inner, .. } => {
                    inners.push(Rc::clone(inner));
                    current = outer;
                }
            }
        }
    }
}

impl ContextProgram<()> {
    /// The same count in the canonical `O(bits)` shape
    /// ([`ContextProgram::of_count`]) when `program`'s graph has grown past
    /// it, and `program` itself otherwise.
    ///
    /// Arithmetic over runs keeps sharing but not shape: iterating an
    /// algebra over a program builds the result's graph from the input's,
    /// so a chain of folds (`half` of `half` of …) can grow the graph of
    /// a 150-bit number to thousands of nodes, and every later fold, walk
    /// or cancellation pays for each one. Over `()` a program is nothing
    /// but its count, so rebuilding it from the count is the same value —
    /// a representation change whose adequacy argument is that equality.
    /// The check stops one node past the canonical size.
    pub fn compact(program: &Rc<Self>) -> Rc<Self> {
        let ContextProgram::Compose { len, .. } = &**program else {
            return Rc::clone(program);
        };
        // The canonical shape has at most two nodes per bit.
        let bound = (2 * len.bits() + 2) as usize;
        // The root retains the whole DAG while this runs, so no key is
        // freed and reused underneath the set.
        let mut seen = std::collections::HashSet::new();
        let mut work = vec![program];
        while let Some(node) = work.pop() {
            if !seen.insert(Rc::as_ptr(node)) {
                continue;
            }
            if seen.len() > bound {
                return Self::of_count((), len);
            }
            if let ContextProgram::Compose { outer, inner, .. } = &**node {
                work.push(outer);
                work.push(inner);
            }
        }
        Rc::clone(program)
    }
}

#[cfg(test)]
mod tests {
    use super::ContextProgram;
    use std::num::NonZeroU64;
    use std::sync::Arc as Rc;

    fn n(value: u64) -> NonZeroU64 {
        NonZeroU64::new(value).unwrap()
    }

    fn doubling(context: char, depth: u32) -> Rc<ContextProgram<char>> {
        let mut program = ContextProgram::run(context, n(1));
        for _ in 0..depth {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        program
    }

    #[test]
    fn adjacent_runs_merge_until_the_u64_boundary() {
        let two = ContextProgram::run('s', n(2));
        let five = ContextProgram::prepend('s', n(3), two);
        assert!(matches!(&*five, ContextProgram::Run { count, .. } if count.get() == 5));

        let full = ContextProgram::run('s', n(u64::MAX));
        let two_to_64 = ContextProgram::prepend('s', n(1), Rc::clone(&full));
        assert!(matches!(&*two_to_64, ContextProgram::Compose { inner, .. }
            if Rc::ptr_eq(inner, &full)));
    }

    #[test]
    fn bounded_repetition_count_reuses_shared_compositions() {
        let mut program = ContextProgram::run((), n(1));
        for _ in 0..63 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        assert_eq!(ContextProgram::repetition_count_up_to(&program, 1_000_000), None);

        let seven = ContextProgram::compose(
            ContextProgram::run((), n(3)),
            ContextProgram::run((), n(4)),
        );
        assert_eq!(ContextProgram::repetition_count_up_to(&seven, 7), Some(7));
        assert_eq!(ContextProgram::repetition_count_up_to(&seven, 6), None);
    }

    #[test]
    fn shared_composition_exposes_virtual_constructors_without_expansion() {
        let mut program = ContextProgram::run('s', n(1));
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        let (context, rest) = ContextProgram::uncons(&program);
        assert_eq!(*context, 's');
        assert!(rest.is_some());
    }

    #[test]
    fn independently_allocated_saturated_runs_compare_without_expansion() {
        let left = ContextProgram::run('s', n(u64::MAX));
        let right = ContextProgram::run('s', n(u64::MAX));
        assert!(!Rc::ptr_eq(&left, &right));
        assert!(ContextProgram::equivalent_fast(&left, &right));
        assert!(!ContextProgram::equivalent_fast(
            &left,
            &ContextProgram::run('s', n(u64::MAX - 1)),
        ));
    }

    #[test]
    fn matching_run_prefixes_cancel_arithmetically() {
        let left = ContextProgram::run('s', n(u64::MAX));
        let right = ContextProgram::run('s', n(u64::MAX - 7));
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 16).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.right.is_none());
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 7));
    }

    #[test]
    fn the_cancelled_prefix_is_returned_as_a_program() {
        let full = ContextProgram::run('s', n(u64::MAX));
        let left = ContextProgram::compose(ContextProgram::run('s', n(3)), Rc::clone(&full));
        let right = ContextProgram::compose(ContextProgram::run('s', n(1)), full);
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 32).unwrap();
        // One saturated run, then the shared fragment: `u64::MAX + 1`,
        // composed because it does not fit one run.
        let program = cancelled.cancelled.expect("something cancelled");
        assert_eq!(ContextProgram::repetition_count_up_to(&program, u64::MAX), None);
        let (_, rest) = ContextProgram::uncons(&program);
        assert_eq!(
            ContextProgram::repetition_count_up_to(&rest.unwrap(), u64::MAX),
            Some(u64::MAX),
        );

        let seven = ContextProgram::run('s', n(7));
        let three = ContextProgram::run('s', n(3));
        let cancelled = ContextProgram::cancel_matching_prefix(seven, three, 8).unwrap();
        assert!(matches!(cancelled.cancelled.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 3));
    }

    #[test]
    fn cancellation_crosses_composed_saturated_runs_and_stops_at_mismatch() {
        let full = ContextProgram::run('s', n(u64::MAX));
        let left = ContextProgram::compose(ContextProgram::run('s', n(3)), Rc::clone(&full));
        let right = ContextProgram::compose(ContextProgram::run('s', n(1)), full);
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 32).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.right.is_none());
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 2));

        let left = ContextProgram::compose(
            ContextProgram::run('s', n(2)),
            ContextProgram::run('x', n(4)),
        );
        let right = ContextProgram::compose(
            ContextProgram::run('s', n(1)),
            ContextProgram::run('y', n(4)),
        );
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 32).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.left.is_some());
        assert!(cancelled.right.is_some());
    }

    #[test]
    fn one_shared_exponential_program_cancels_without_traversal() {
        let mut program = ContextProgram::run('s', n(1));
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        let cancelled =
            ContextProgram::cancel_matching_prefix(Rc::clone(&program), program, 1).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.left.is_none());
        assert!(cancelled.right.is_none());
    }

    /// Two uniform DAGs are compared by length: one visit per node of
    /// each graph, never one per represented constructor.
    #[test]
    fn independently_allocated_exponential_dags_cancel_in_their_graph_size() {
        let left = doubling('s', 64);
        let right = doubling('s', 64);
        assert!(!Rc::ptr_eq(&left, &right));
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 256).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.left.is_none());
        assert!(cancelled.right.is_none());
        assert!(cancelled.inspected <= 2 * 65 + 2, "{}", cancelled.inspected);
    }

    /// Mixed programs, whose fronts do not each repeat one context, still
    /// skip a common DAG prefix by bisimulation.
    #[test]
    fn mixed_programs_cancel_a_bisimilar_prefix() {
        let mixed = |depth| {
            let mut program = ContextProgram::compose(
                ContextProgram::run('s', n(1)),
                ContextProgram::run('x', n(1)),
            );
            for _ in 0..depth {
                program = ContextProgram::compose(Rc::clone(&program), program);
            }
            program
        };
        let left = ContextProgram::compose(mixed(64), ContextProgram::run('x', n(3)));
        let right = ContextProgram::compose(mixed(64), ContextProgram::run('y', n(3)));
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 1_000).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.inspected <= 400, "{}", cancelled.inspected);
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { context: 'x', count }) if count.get() == 3));
        assert!(matches!(cancelled.right.as_deref(),
            Some(ContextProgram::Run { context: 'y', count }) if count.get() == 3));
    }

    #[test]
    fn exponential_prefix_leaves_compact_unequal_residuals() {
        let left = ContextProgram::compose(
            doubling('s', 64),
            ContextProgram::run('x', n(u64::MAX)),
        );
        let right = ContextProgram::compose(
            doubling('s', 64),
            ContextProgram::run('y', n(u64::MAX)),
        );
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 400).unwrap();
        assert!(cancelled.inspected <= 3 * 67 + 8, "{}", cancelled.inspected);
        assert!(cancelled.changed);
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { context: 'x', count }) if count.get() == u64::MAX));
        assert!(matches!(cancelled.right.as_deref(),
            Some(ContextProgram::Run { context: 'y', count }) if count.get() == u64::MAX));
    }

    /// `n` as a program the way a wide literal is built: doubling from the
    /// top bit, merging runs while they fit a `u64`.
    fn by_bits(context: char, n: &[u64]) -> Rc<ContextProgram<char>> {
        let n = heather_numeral::Numeral::from_limbs(n.to_vec());
        let one = || ContextProgram::run(context, n_(1));
        let mut acc: Option<Rc<ContextProgram<char>>> = None;
        for i in (0..n.bits()).rev() {
            acc = acc.map(|a| ContextProgram::append(Rc::clone(&a), a));
            if n.bit(i) {
                acc = Some(match acc {
                    None => one(),
                    Some(a) => ContextProgram::append(one(), a),
                });
            }
        }
        acc.unwrap()
    }

    fn n_(value: u64) -> NonZeroU64 {
        n(value)
    }

    /// Two numbers built by different routes are not bisimilar node for
    /// node; their common prefix still cancels by counting, in work
    /// proportional to their graphs, not to their value over `2^63`.
    #[test]
    fn differently_built_wide_numbers_cancel_by_their_counts() {
        // 2^200 + 1 against 2^200: off by one at the outermost run, so no
        // pair of nodes lines up after the first fragment.
        let left = by_bits('s', &[1, 0, 0, 1 << 8]);
        let right = by_bits('s', &[0, 0, 0, 1 << 8]);
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 2_000).unwrap();
        assert!(cancelled.right.is_none());
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 1));
        assert!(cancelled.inspected < 1_000, "{}", cancelled.inspected);

        // The same 2^148 as a literal and as one successor on 2^148 - 1:
        // misaligned by one at every level, but bisimilar in places, the
        // walk that opened fronts node by node visited the value's tree.
        let left = by_bits('s', &[0, 0, 1 << 20]);
        let right = ContextProgram::compose(
            ContextProgram::run('s', n_(1)),
            by_bits('s', &[u64::MAX, u64::MAX, (1 << 20) - 1]),
        );
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 1 << 20).unwrap();
        assert!(cancelled.left.is_none() && cancelled.right.is_none());
        assert!(cancelled.inspected < 2_000, "{}", cancelled.inspected);

        // Doubling against a literal's construction of the same 2^64,
        // and a residual deep inside the longer one.
        let left = doubling('s', 64);
        let right = by_bits('s', &[3, 1]);
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 1_000).unwrap();
        assert!(cancelled.left.is_none());
        assert_eq!(
            ContextProgram::repetition_count_up_to(&cancelled.right.unwrap(), 8),
            Some(3),
        );
        assert_eq!(
            ContextProgram::repetition_count_up_to(&cancelled.cancelled.unwrap(), u64::MAX),
            None,
        );
    }

    /// The denotation, as a string of contexts, outermost first.
    fn expand(program: &Rc<ContextProgram<char>>) -> String {
        match &**program {
            ContextProgram::Run { context, count } => {
                std::iter::repeat_n(*context, count.get() as usize).collect()
            }
            ContextProgram::Compose { outer, inner, .. } => expand(outer) + &expand(inner),
        }
    }

    /// Against the specification on small programs: the residuals and the
    /// cancelled prefix denote exactly the longest common prefix split,
    /// over random shapes, mixed contexts and shared subprograms.
    #[test]
    fn cancellation_agrees_with_expansion() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        let random = |next: &mut dyn FnMut(u64) -> u64| {
            let mut pool: Vec<Rc<ContextProgram<char>>> = Vec::new();
            for _ in 0..1 + next(8) {
                let program = if pool.is_empty() || next(3) == 0 {
                    let context = if next(4) == 0 { 'x' } else { 's' };
                    ContextProgram::run(context, n(1 + next(5)))
                } else {
                    let outer = Rc::clone(&pool[next(pool.len() as u64) as usize]);
                    let inner = Rc::clone(&pool[next(pool.len() as u64) as usize]);
                    ContextProgram::compose(outer, inner)
                };
                pool.push(program);
            }
            pool.pop().unwrap()
        };
        for case in 0..4_000 {
            let left = random(&mut next);
            let right = random(&mut next);
            let (l, r) = (expand(&left), expand(&right));
            let common = l.chars().zip(r.chars()).take_while(|(a, b)| a == b).count();
            let cancelled = ContextProgram::cancel_matching_prefix(left, right, 1 << 20).unwrap();
            let show = |p: &Option<Rc<ContextProgram<char>>>| p.as_ref().map_or(String::new(), expand);
            assert_eq!(show(&cancelled.left), l[common..], "case {case}");
            assert_eq!(show(&cancelled.right), r[common..], "case {case}");
            assert_eq!(show(&cancelled.cancelled), l[..common], "case {case}");
            assert_eq!(cancelled.changed, common > 0, "case {case}");
        }
    }

    #[test]
    fn hostile_near_match_exhausts_its_bound_without_a_verdict() {
        let left = doubling('s', 64);
        let right = doubling('x', 64);
        assert!(matches!(
            ContextProgram::cancel_matching_prefix(left, right, 16),
            Err(super::CancellationExhausted),
        ));
    }

}
