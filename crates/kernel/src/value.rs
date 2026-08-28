//! The **value domain**: weak head normal forms with environments and
//! closures (docs/nbe-conversion-design.md §3).
//!
//! A value is a term (or type) reduced to weak head normal form, with every
//! sub-structure kept as an *environment plus syntax* rather than as a
//! substituted term. That is the whole point of the round: an eliminator's β
//! extends an environment instead of copying a branch
//! (`issues/whnf-sharing-term-growth.md`).
//!
//! The domain is shaped so that the kernel's invariants are
//! **unrepresentable**, not merely unviolated:
//!
//! - [`Type::El`] has no value: it either decodes (and the value is the
//!   decoded former) or its encoding is stuck, in which case the value is
//!   [`VNeTy::El`]. Ch. 06's normal-form grammar `V := U^δ | El^l ν`, made
//!   structural.
//! - [`VTy::Vec`] / [`VTy::Fin`] exist only over a **non-canonical** length:
//!   at a canonical one they step, so the evaluator never builds them.
//! - `box` values ([`Val::BoxTy`], [`Val::BoxTm`]) carry raw syntax with
//!   **no environment**, so there is no environment in which the payload
//!   *could* be evaluated. Ch. 06's "reduction never enters a box", made
//!   structural (design §3.5).
//! - Variables have a two-part identity ([`Head::Var`] / [`Head::BaseVar`]):
//!   a de Bruijn **level** into the concrete entries of Γ, and a **depth**
//!   into the abstract prefix `g` of a [`CtxBase::Var`] context. Both are
//!   stable under pushing binders on the right, which is the only thing
//!   conversion ever does (design §3.2).
//!
//! Three namespaces, treated differently (design §3.1): locals go through
//! the environment; universe levels and globals stay **syntax**. A global
//! variable becomes a *glued* neutral ([`VNeutral::unfold`]).
//!
//! **Forcing is fallible everywhere.** There is no `Deref`, no infallible
//! accessor, no `unwrap`: laziness introduces new places an `OutOfFuel` can
//! originate and each one must be able to propagate (design §6). All forcing
//! lives in [`crate::eval`], which owns the fuel.
//!
//! `Debug` on every recursive type here is budget-bounded through
//! [`crate::fmt`]'s `node()` gate, per `CLAUDE.md`: an accidental `{:?}` on
//! a value must not OOM the machine. Closures print their *body syntax*
//! (itself bounded) and never force anything.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::rc::Rc;
use typed_arena::Arena;

use crate::fmt::node;
use crate::level::Level;
use crate::term::{Branches, CtxBase, GlobalVar, LocalCtx, Motives, SubstTail, Term, Type};

pub mod shift;

// ---------------------------------------------------------------------------
// Environments
// ---------------------------------------------------------------------------

/// A local environment: one entry per **concrete** binder in scope,
/// innermost first, as a region-backed persistent list so that pushing a
/// binder is one allocation and capturing it in a closure is a pointer copy.
///
/// De Bruijn *indices* resolve against it from the inside; anything past the
/// end is a variable of the abstract prefix `g` (see [`Lookup`]). Because
/// the list only ever grows on the right, the *level* `len - 1 - i` assigned
/// to an entry never changes — which is exactly why closures need no
/// shifting.
#[derive(Clone, Copy)]
pub struct Env<'v> {
    arena: &'v ValueArena<'v>,
    node: Option<&'v EnvNode<'v>>,
    len: u32,
}

struct EnvNode<'v> {
    val: &'v TmClo<'v>,
    rest: Env<'v>,
}

/// The result of resolving a de Bruijn index against an [`Env`].
pub enum Lookup<'v> {
    /// A concrete entry.
    Bound(&'v TmClo<'v>),
    /// A variable of the abstract prefix, at `depth` counted from the
    /// prefix's inner end.
    Base(u32),
}

impl<'v> Env<'v> {
    pub fn empty(arena: &'v ValueArena<'v>) -> Env<'v> {
        Env { arena, node: None, len: 0 }
    }

    /// The number of concrete entries.
    pub fn len(&self) -> u32 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn arena(&self) -> &'v ValueArena<'v> {
        self.arena
    }

    /// Object identity: the same spine (both empty, or one shared head
    /// node). Two identical environments answer every lookup identically,
    /// so a closure body evaluated under either denotes the same value.
    pub fn ptr_eq(a: &Env<'v>, b: &Env<'v>) -> bool {
        a.len == b.len
            && match (&a.node, &b.node) {
                (None, None) => true,
                (Some(x), Some(y)) => std::ptr::eq(*x, *y),
                _ => false,
            }
    }

    /// Pointwise object identity of two environment spines. Shared tails end
    /// the walk immediately; otherwise every corresponding captured value
    /// must be the same arena-owned closure. This is stronger than semantic
    /// equality but cheaper than conversion, and is stable for the lifetime
    /// of the query's arena.
    pub fn values_ptr_eq(a: &Env<'v>, b: &Env<'v>) -> bool {
        if a.len != b.len {
            return false;
        }
        let (mut x, mut y) = (a, b);
        loop {
            match (x.node, y.node) {
                (None, None) => return true,
                (Some(nx), Some(ny)) if std::ptr::eq(nx, ny) => return true,
                (Some(nx), Some(ny)) if std::ptr::eq(nx.val, ny.val) => {
                    x = &nx.rest;
                    y = &ny.rest;
                }
                _ => return false,
            }
        }
    }

    /// `ρ, v` — one more binder, innermost.
    pub fn push(&self, val: &'v TmClo<'v>) -> Env<'v> {
        #[cfg(feature = "value-metrics")]
        if let Some(m) = self.arena.metrics {
            ValueMetrics::bump(&m.inner.env_nodes);
        }
        Env {
            arena: self.arena,
            node: Some(self.arena.envs.alloc(EnvNode { val, rest: *self })),
            len: self.len + 1,
        }
    }

    /// Push several binders, `vals[0]` outermost (the order the branch
    /// telescopes and the β-rules write them).
    pub fn extend(&self, vals: &[&'v TmClo<'v>]) -> Env<'v> {
        let mut e = *self;
        for v in vals {
            e = e.push(v);
        }
        e
    }

    /// Resolve a de Bruijn index (0 = innermost).
    pub fn lookup(&self, i: u32) -> Lookup<'v> {
        if i >= self.len {
            return Lookup::Base(i - self.len);
        }
        let mut cur = self;
        let mut k = i;
        loop {
            // Safe by the length invariant: `k < cur.len` at every step.
            let Some(n) = cur.node.as_ref() else {
                return Lookup::Base(k);
            };
            if k == 0 {
                return Lookup::Bound(n.val);
            }
            k -= 1;
            cur = &n.rest;
        }
    }

    /// The identity environment of a Γ with `n` concrete entries: entry `j`
    /// (counted from the *outer* end) is the neutral variable at level `j`.
    /// This is the environment at the root of a conversion.
    ///
    /// Every identity environment is a *prefix* of every longer one. A query
    /// builds the requested spine once in its arena and every sub-conversion
    /// shares that spine; no identity state escapes the query or lives in a
    /// thread-local cache.
    pub fn identity(arena: &'v ValueArena<'v>, n: u32) -> Env<'v> {
        let mut env = Env::empty(arena);
        for level in 0..n {
            let value = Rc::new(Val::var(level));
            env = env.push(arena.tm(TmClo::val(value)));
        }
        env
    }

    /// The outermost `n` entries — the identity environment of a Γ-prefix.
    pub fn prefix(&self, n: u32) -> Env<'v> {
        let mut cur = *self;
        while cur.len > n {
            match cur.node.as_ref() {
                Some(node) => cur = node.rest,
                None => break,
            }
        }
        cur
    }

    /// The entries, **outermost first** — the order [`Env::extend`] wants.
    /// Used by the outer-namespace maps, which have to rebuild the list.
    pub fn to_vec(&self) -> Vec<&'v TmClo<'v>> {
        let mut out = Vec::with_capacity(self.len as usize);
        let mut cur = self;
        while let Some(n) = cur.node.as_ref() {
            out.push(n.val);
            cur = &n.rest;
        }
        out.reverse();
        out
    }
}

/// Region storage for one conversion/evaluation query. Semantic graph edges
/// borrow this region, so releasing a query drops flat arena storage rather
/// than recursively walking a reference-counted graph.
pub struct ValueArena<'v> {
    #[cfg(feature = "value-metrics")]
    metrics: Option<&'v ValueMetrics>,
    term_cache: RefCell<ValueCache<*const TmClo<'v>, Val<'v>>>,
    type_cache: RefCell<ValueCache<*const TyClo<'v>, VTy<'v>>>,
    envs: Arena<EnvNode<'v>>,
    terms: Arena<TmClo<'v>>,
    types: Arena<TyClo<'v>>,
}

const VALUE_CACHE_CAPACITY: usize = 16 * 1024;

/// Aggregate, observational counters for value-machine regions.
///
/// A caller explicitly lends this collector to every region it wants to
/// measure.  The ordinary [`ValueArena::new`] path has no collector, so
/// measure. The `value-metrics` feature compiles the counters in; ordinary
/// builds contain neither the collector pointer nor counted-event branches.
/// There is no global or thread-local instrumentation state.
#[derive(Clone, Default)]
pub struct ValueMetrics {
    inner: Rc<ValueMetricCells>,
}

#[derive(Default)]
struct ValueMetricCells {
    arenas: Cell<u64>,
    env_nodes: Cell<u64>,
    term_closures: Cell<u64>,
    type_closures: Cell<u64>,
    term_cache_lookups: Cell<u64>,
    term_cache_hits: Cell<u64>,
    term_cache_inserts: Cell<u64>,
    term_cache_evictions: Cell<u64>,
    term_cache_peak: Cell<u64>,
    type_cache_lookups: Cell<u64>,
    type_cache_hits: Cell<u64>,
    type_cache_inserts: Cell<u64>,
    type_cache_evictions: Cell<u64>,
    type_cache_peak: Cell<u64>,
    app_domain_checks: Cell<u64>,
    app_domain_fast_hits: Cell<u64>,
    app_codomain_checks: Cell<u64>,
    app_codomain_fast_hits: Cell<u64>,
    app_shared_body_env_hits: Cell<u64>,
}

/// A copyable snapshot of [`ValueMetrics`]. Counts aggregate every profiled
/// region since the collector was created or last reset; cache peaks are the
/// largest resident set in any one region, not a sum across regions.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ValueMetricsSnapshot {
    pub arenas: u64,
    pub env_nodes: u64,
    pub term_closures: u64,
    pub type_closures: u64,
    pub term_cache_lookups: u64,
    pub term_cache_hits: u64,
    pub term_cache_inserts: u64,
    pub term_cache_evictions: u64,
    pub term_cache_peak: u64,
    pub type_cache_lookups: u64,
    pub type_cache_hits: u64,
    pub type_cache_inserts: u64,
    pub type_cache_evictions: u64,
    pub type_cache_peak: u64,
    pub app_domain_checks: u64,
    pub app_domain_fast_hits: u64,
    pub app_codomain_checks: u64,
    pub app_codomain_fast_hits: u64,
    pub app_shared_body_env_hits: u64,
}

impl ValueMetrics {
    pub fn snapshot(&self) -> ValueMetricsSnapshot {
        ValueMetricsSnapshot {
            arenas: self.inner.arenas.get(),
            env_nodes: self.inner.env_nodes.get(),
            term_closures: self.inner.term_closures.get(),
            type_closures: self.inner.type_closures.get(),
            term_cache_lookups: self.inner.term_cache_lookups.get(),
            term_cache_hits: self.inner.term_cache_hits.get(),
            term_cache_inserts: self.inner.term_cache_inserts.get(),
            term_cache_evictions: self.inner.term_cache_evictions.get(),
            term_cache_peak: self.inner.term_cache_peak.get(),
            type_cache_lookups: self.inner.type_cache_lookups.get(),
            type_cache_hits: self.inner.type_cache_hits.get(),
            type_cache_inserts: self.inner.type_cache_inserts.get(),
            type_cache_evictions: self.inner.type_cache_evictions.get(),
            type_cache_peak: self.inner.type_cache_peak.get(),
            app_domain_checks: self.inner.app_domain_checks.get(),
            app_domain_fast_hits: self.inner.app_domain_fast_hits.get(),
            app_codomain_checks: self.inner.app_codomain_checks.get(),
            app_codomain_fast_hits: self.inner.app_codomain_fast_hits.get(),
            app_shared_body_env_hits: self.inner.app_shared_body_env_hits.get(),
        }
    }

    pub fn reset(&self) {
        let zero = ValueMetricsSnapshot::default();
        self.inner.arenas.set(zero.arenas);
        self.inner.env_nodes.set(zero.env_nodes);
        self.inner.term_closures.set(zero.term_closures);
        self.inner.type_closures.set(zero.type_closures);
        self.inner.term_cache_lookups.set(zero.term_cache_lookups);
        self.inner.term_cache_hits.set(zero.term_cache_hits);
        self.inner.term_cache_inserts.set(zero.term_cache_inserts);
        self.inner.term_cache_evictions.set(zero.term_cache_evictions);
        self.inner.term_cache_peak.set(zero.term_cache_peak);
        self.inner.type_cache_lookups.set(zero.type_cache_lookups);
        self.inner.type_cache_hits.set(zero.type_cache_hits);
        self.inner.type_cache_inserts.set(zero.type_cache_inserts);
        self.inner.type_cache_evictions.set(zero.type_cache_evictions);
        self.inner.type_cache_peak.set(zero.type_cache_peak);
        self.inner.app_domain_checks.set(zero.app_domain_checks);
        self.inner.app_domain_fast_hits.set(zero.app_domain_fast_hits);
        self.inner.app_codomain_checks.set(zero.app_codomain_checks);
        self.inner.app_codomain_fast_hits.set(zero.app_codomain_fast_hits);
        self.inner.app_shared_body_env_hits.set(zero.app_shared_body_env_hits);
    }

    #[cfg(feature = "value-metrics")]
    fn bump(cell: &Cell<u64>) {
        cell.set(cell.get().saturating_add(1));
    }

    #[cfg(feature = "value-metrics")]
    fn record_peak(cell: &Cell<u64>, resident: usize) {
        cell.set(cell.get().max(resident as u64));
    }
}

struct ValueCache<K, V> {
    values: HashMap<K, Rc<V>>,
    order: VecDeque<K>,
}

impl<K: Copy + Eq + std::hash::Hash, V> ValueCache<K, V> {
    fn new() -> ValueCache<K, V> {
        ValueCache { values: HashMap::new(), order: VecDeque::new() }
    }

    fn get(&self, key: K) -> Option<Rc<V>> {
        self.values.get(&key).cloned()
    }

    #[cfg(not(feature = "value-metrics"))]
    fn insert(&mut self, key: K, value: &Rc<V>) {
        if self.values.contains_key(&key) { return; }
        self.values.insert(key, Rc::clone(value));
        self.order.push_back(key);
        if self.order.len() > VALUE_CACHE_CAPACITY {
            if let Some(oldest) = self.order.pop_front() { self.values.remove(&oldest); }
        }
    }

    #[cfg(feature = "value-metrics")]
    fn insert_profiled(&mut self, key: K, value: &Rc<V>) -> (bool, bool) {
        if self.values.contains_key(&key) { return (false, false); }
        self.values.insert(key, Rc::clone(value));
        self.order.push_back(key);
        let evicted = self.order.len() > VALUE_CACHE_CAPACITY;
        if evicted {
            if let Some(oldest) = self.order.pop_front() { self.values.remove(&oldest); }
        }
        (true, evicted)
    }

    #[cfg(feature = "value-metrics")]
    fn len(&self) -> usize {
        self.values.len()
    }

}

impl<'v> ValueArena<'v> {
    pub(crate) fn record_app_annotation(&self, codomain: bool, fast: bool, env_hit: bool) {
        #[cfg(feature = "value-metrics")]
        if let Some(m) = self.metrics {
            let (checks, hits) = if codomain {
                (&m.inner.app_codomain_checks, &m.inner.app_codomain_fast_hits)
            } else {
                (&m.inner.app_domain_checks, &m.inner.app_domain_fast_hits)
            };
            ValueMetrics::bump(checks);
            if fast {
                ValueMetrics::bump(hits);
            }
            if env_hit {
                ValueMetrics::bump(&m.inner.app_shared_body_env_hits);
            }
        }
        #[cfg(not(feature = "value-metrics"))]
        let _ = (codomain, fast, env_hit);
    }

    pub fn new() -> ValueArena<'v> {
        ValueArena {
            #[cfg(feature = "value-metrics")]
            metrics: None,
            term_cache: RefCell::new(ValueCache::new()),
            type_cache: RefCell::new(ValueCache::new()),
            envs: Arena::new(),
            terms: Arena::new(),
            types: Arena::new(),
        }
    }

    /// Make a region whose activity contributes to `metrics`.
    pub fn profiled(metrics: &'v ValueMetrics) -> ValueArena<'v> {
        #[cfg(feature = "value-metrics")]
        {
            ValueMetrics::bump(&metrics.inner.arenas);
            ValueArena {
                metrics: Some(metrics),
                term_cache: RefCell::new(ValueCache::new()),
                type_cache: RefCell::new(ValueCache::new()),
                envs: Arena::new(),
                terms: Arena::new(),
                types: Arena::new(),
            }
        }
        #[cfg(not(feature = "value-metrics"))]
        {
            let _ = metrics;
            Self::new()
        }
    }

    pub fn tm(&'v self, value: TmClo<'v>) -> &'v TmClo<'v> {
        #[cfg(feature = "value-metrics")]
        if let Some(m) = self.metrics {
            ValueMetrics::bump(&m.inner.term_closures);
        }
        self.terms.alloc(value)
    }

    pub fn ty(&'v self, value: TyClo<'v>) -> &'v TyClo<'v> {
        #[cfg(feature = "value-metrics")]
        if let Some(m) = self.metrics {
            ValueMetrics::bump(&m.inner.type_closures);
        }
        self.types.alloc(value)
    }

    /// The cached value for `clo`, if it is currently retained by this
    /// query's bounded cache.
    pub fn memo_tm(&self, clo: &'v TmClo<'v>) -> Option<Rc<Val<'v>>> {
        match clo {
            TmClo::Val(value) => Some(Rc::clone(value)),
            _ => {
                let found = self.term_cache.borrow().get(clo as *const TmClo<'v>);
                #[cfg(feature = "value-metrics")]
                if let Some(m) = self.metrics {
                    ValueMetrics::bump(&m.inner.term_cache_lookups);
                    if found.is_some() {
                        ValueMetrics::bump(&m.inner.term_cache_hits);
                    }
                }
                found
            }
        }
    }

    pub(crate) fn memo_ty(&self, clo: &'v TyClo<'v>) -> Option<Rc<VTy<'v>>> {
        match clo {
            TyClo::Val(value) => Some(Rc::clone(value)),
            _ => {
                let found = self.type_cache.borrow().get(clo as *const TyClo<'v>);
                #[cfg(feature = "value-metrics")]
                if let Some(m) = self.metrics {
                    ValueMetrics::bump(&m.inner.type_cache_lookups);
                    if found.is_some() {
                        ValueMetrics::bump(&m.inner.type_cache_hits);
                    }
                }
                found
            }
        }
    }

    pub(crate) fn cache_tm(&self, clo: &'v TmClo<'v>, value: &Rc<Val<'v>>) {
        if !matches!(clo, TmClo::Val(_)) {
            let mut cache = self.term_cache.borrow_mut();
            #[cfg(feature = "value-metrics")]
            {
                let (inserted, evicted) =
                    cache.insert_profiled(clo as *const TmClo<'v>, value);
                if let Some(m) = self.metrics {
                    if inserted { ValueMetrics::bump(&m.inner.term_cache_inserts); }
                    if evicted {
                        ValueMetrics::bump(&m.inner.term_cache_evictions);
                    }
                    ValueMetrics::record_peak(&m.inner.term_cache_peak, cache.len());
                }
            }
            #[cfg(not(feature = "value-metrics"))]
            {
                cache.insert(clo as *const TmClo<'v>, value);
            }
        }
    }

    pub(crate) fn cache_ty(&self, clo: &'v TyClo<'v>, value: &Rc<VTy<'v>>) {
        if !matches!(clo, TyClo::Val(_)) {
            let mut cache = self.type_cache.borrow_mut();
            #[cfg(feature = "value-metrics")]
            {
                let (inserted, evicted) =
                    cache.insert_profiled(clo as *const TyClo<'v>, value);
                if let Some(m) = self.metrics {
                    if inserted { ValueMetrics::bump(&m.inner.type_cache_inserts); }
                    if evicted {
                        ValueMetrics::bump(&m.inner.type_cache_evictions);
                    }
                    ValueMetrics::record_peak(&m.inner.type_cache_peak, cache.len());
                }
            }
            #[cfg(not(feature = "value-metrics"))]
            {
                cache.insert(clo as *const TyClo<'v>, value);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Closures and lazy values
// ---------------------------------------------------------------------------

/// A term sub-structure of a value: an environment plus unevaluated syntax.
/// Its weak head result is held, when useful, by [`ValueArena`]'s bounded
/// query cache.
///
/// With `k > 0` pending binders it is a **closure** (applied by
/// [`crate::eval::Eval::apply`]); with none it is a **lazy value** (forced by
/// [`crate::eval::Eval::force`]). The two are the same object because the
/// binder count is determined by the position, exactly as in the syntax.
///
/// [`TmClo::Val`] is an already-computed value (a β payload, a δ payload) and
/// [`TmClo::Elim`] is a pending elimination — the shape the *glued* unfold of
/// a neutral takes as its spine grows (design §5).
///
/// **A thunk never memoizes a failure**: the memo is written only on `Ok`, so
/// a value graph forced under an insufficient budget and re-forced under a
/// larger one still succeeds (design §6). Successful results live in the
/// query arena's bounded cache, so sharing cannot retain an unbounded forced
/// graph.
pub enum TmClo<'v> {
    Syn {
        env: Env<'v>,
        body: Rc<Term>,
    },
    Val(Rc<Val<'v>>),
    Elim {
        head: &'v TmClo<'v>,
        elim: Rc<Elim<'v>>,
    },
}

impl<'v> TmClo<'v> {
    pub fn syn(env: Env<'v>, body: Rc<Term>) -> TmClo<'v> {
        TmClo::Syn { env, body }
    }

    pub fn val(v: Rc<Val<'v>>) -> TmClo<'v> {
        TmClo::Val(v)
    }

    pub fn elim(head: &'v TmClo<'v>, elim: Rc<Elim<'v>>) -> TmClo<'v> {
        TmClo::Elim { head, elim }
    }

    /// The environment and syntax, when this is a syntactic closure. Used
    /// where a *rule* needs the sub-structure's syntax rather than its value
    /// — the `El` decodes (which wrap the encoding's children in `El`) and
    /// the universe/global instantiations. Everything the evaluator builds
    /// from syntax is `Syn`; the fallback is a stuck value, never a panic.
    pub fn as_syn(&self) -> Option<(&Env<'v>, &Rc<Term>)> {
        match self {
            TmClo::Syn { env, body, .. } => Some((env, body)),
            _ => None,
        }
    }

}

/// A type sub-structure of a value: the type mirror of [`TmClo`].
///
/// [`TyClo::Syn`] is the ordinary case — an environment plus unevaluated
/// syntax. The other two exist because *conversion* builds
/// types the evaluator never does (docs/nbe-conversion-design.md §13, stage
/// 2b): the comparison rules synthesize `Π`, `Vec`, `El` … whose children are
/// **domain objects** rather than syntax, and there is no environment in
/// which a domain object could be written down.
///
/// - [`TyClo::Val`] is an already-computed type. As a *closure* it is
///   constant: applying it to arguments ignores them, which is exactly what
///   the rules that weaken a type into a binder position mean.
/// - [`TyClo::Vec`] is `Vec^l(T; k)` held **unforced**, so that the Σ-tail of
///   a vector at a canonical length stays lazy even when the element type is
///   a value with no syntax. Forcing it is `Eval::vec_ty`.
pub enum TyClo<'v> {
    Syn {
        env: Env<'v>,
        body: Rc<Type>,
    },
    Val(Rc<VTy<'v>>),
    Vec {
        level: Level,
        elem: &'v TyClo<'v>,
        len: &'v TmClo<'v>,
    },
    /// `El^l t` held **unforced**. `El` has no canonical value — it decodes
    /// or it is stuck — but it is still a perfectly good *sub-structure*, and
    /// keeping it lazy is what makes the decode one step deep and lets
    /// conversion synthesize `El`s over encodings that are values.
    El {
        level: Level,
        tm: &'v TmClo<'v>,
    },
}

impl<'v> TyClo<'v> {
    pub fn new(env: Env<'v>, body: Rc<Type>) -> TyClo<'v> {
        TyClo::Syn { env, body }
    }

    pub fn val(v: Rc<VTy<'v>>) -> TyClo<'v> {
        TyClo::Val(v)
    }

    pub fn vec(level: Level, elem: &'v TyClo<'v>, len: &'v TmClo<'v>) -> TyClo<'v> {
        TyClo::Vec { level, elem, len }
    }

    pub fn el(level: Level, tm: &'v TmClo<'v>) -> TyClo<'v> {
        TyClo::El { level, tm }
    }

    /// The environment and syntax, when this is a syntactic closure. See
    /// [`TmClo::as_syn`]: a rule that needs the sub-structure's *syntax*
    /// falls back to a stuck value rather than panicking.
    pub fn as_syn(&self) -> Option<(&Env<'v>, &Rc<Type>)> {
        match self {
            TyClo::Syn { env, body, .. } => Some((env, body)),
            _ => None,
        }
    }

}

// ---------------------------------------------------------------------------
// Neutrals
// ---------------------------------------------------------------------------

/// The tail of a local substitution inside a value: `·_{g?}` or `wk_g`.
///
/// The paper's `k` — δ̂, the *source* context's length — is deliberately
/// **dropped**, and `·`'s base is normalized to the ambient Γ's. Both are
/// determined by the scope the value lives in, which is common to the two
/// sides of every comparison; and keeping them would make a value disagree
/// with its own reduct. The rewriter renormalizes them at every
/// `apply_local` (`wk^k_g ∘ δ = wk^δ̂_g`, `·^k ∘ δ = ·^δ̂_δ̌`, `subst.rs`),
/// which is a thing an environment machine — having performed no
/// substitution — has no opportunity to do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VTail {
    /// `·^k_{g?}` at the ambient base.
    Empty(CtxBase),
    /// `wk^k_g`.
    Wk(GlobalVar),
}

/// A local substitution inside a value. The **terms are values** — evaluated
/// pointwise when the neutral is built — because a `δ` of unforced syntax is
/// the defect class reintroduced by the domain (design §3.4, the subtlest
/// correctness point in it).
#[derive(Clone)]
pub struct VSubst<'v> {
    pub tail: VTail,
    pub terms: Vec<Rc<Val<'v>>>,
}

impl VTail {
    /// The tail of a syntactic substitution, read in a scope whose base is
    /// `base`. See [`VTail`] for why `len` and `·`'s base are not carried.
    pub fn of(tail: SubstTail, base: CtxBase) -> VTail {
        match tail {
            SubstTail::Wk { ctx_var, .. } => VTail::Wk(ctx_var),
            SubstTail::Empty { .. } => VTail::Empty(base),
        }
    }
}

/// The head of a neutral.
#[derive(Clone)]
pub enum Head<'v> {
    /// A concrete local, by de Bruijn **level** from the outer end of Γ.
    Var(u32),
    /// A local of the abstract prefix `g`, by **depth** from its inner end.
    BaseVar(u32),
    /// `u^δ` — a global term variable. Glued when it is a definition
    /// ([`VNeutral::unfold`]).
    Global { var: GlobalVar, subst: VSubst<'v> },
    /// `box (U^δ)` under a code recursor: canonical, but the recursor can
    /// never fire on it (ch. 06). Naming it a head is what keeps
    /// `reduce::is_neutral_term`'s special case from being re-derived.
    BoxedGlobalTy(Rc<Type>),
    /// `box (u^δ)` under a code recursor.
    BoxedGlobalTm(Rc<Term>),
    /// An eliminator applied to a value it cannot eliminate — reachable only
    /// on ill-typed input, where `reduce.rs` is likewise stuck without being
    /// neutral. Given a home here so that no input reaches a panic.
    Stuck(Rc<Val<'v>>),
}

impl Head<'_> {
    /// Whether this head makes the spine a genuine ch. 06 neutral (as
    /// opposed to an ill-typed stuck form).
    pub fn is_neutral(&self) -> bool {
        !matches!(self, Head::Stuck(_))
    }
}

/// A **glued** neutral: a head, a spine of eliminations applied
/// outermost-last, and — when the head is a defined global — the pending
/// δ-unfolding of the whole thing (design §5).
///
/// `unfold` is `Some` exactly when the head is a `Global` that `Defs` says is
/// defined; pushing an elimination onto a glued neutral extends the unfold by
/// the same elimination, so forcing it replays the spine. The δ-lazy
/// conversion order compares spines *without* forcing and only unfolds when
/// that fails.
pub struct VNeutral<'v> {
    pub head: Head<'v>,
    pub spine: Vec<Elim<'v>>,
    pub unfold: Option<&'v TmClo<'v>>,
}

/// Neutral **types**: ch. 06's `V := U^δ | El^l ν`.
pub enum VNeTy<'v> {
    /// `U^δ` — a global type variable. Never glued: type-level bindings have
    /// no bodies.
    Global { var: GlobalVar, subst: VSubst<'v> },
    /// `El^l ν` at an encoding that does not decode. Forced, so the payload
    /// is a weak head value: a neutral (the ch. 06 case) or — on ill-typed
    /// input — a stuck one.
    El { level: Level, tm: Rc<Val<'v>> },
}

// ---------------------------------------------------------------------------
// Type values
// ---------------------------------------------------------------------------

/// Weak head normal **types**. Every former keeps its levels as syntax
/// (§3.1: there is no level redex); a sub-structure under the former's own
/// local binder is a [`TyClo`]/[`TmClo`] with that binder pending.
pub enum VTy<'v> {
    Nat,
    Ty(Level),
    Unit { level: Level },
    Empty { level: Level },
    SEmpty { level: Level },
    Squash {
        level: Level,
        ty: &'v TyClo<'v>,
    },
    Pi {
        dom_level: Level,
        cod_level: Level,
        dom: &'v TyClo<'v>,
        cod: &'v TyClo<'v>,
    },
    Sigma {
        fst_level: Level,
        snd_level: Level,
        fst: &'v TyClo<'v>,
        snd: &'v TyClo<'v>,
    },
    W {
        shape_level: Level,
        pos_level: Level,
        shape: &'v TyClo<'v>,
        pos: &'v TyClo<'v>,
    },
    /// The arity is a `Nat` **term** under the shape binder, so it is a term
    /// closure, not a type one.
    Wf {
        level: Level,
        shape: &'v TyClo<'v>,
        arity: &'v TmClo<'v>,
    },
    /// Non-dependent: neither summand binds, so neither is a closure — both
    /// are lazy 0-binder sub-structures.
    Sum {
        lhs_level: Level,
        rhs_level: Level,
        lhs: &'v TyClo<'v>,
        rhs: &'v TyClo<'v>,
    },
    Id {
        level: Level,
        ty: &'v TyClo<'v>,
        lhs: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
    },
    SEq {
        level: Level,
        ty: &'v TyClo<'v>,
        lhs: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
    },
    /// **Only at a non-canonical length** — at `0`/`S k` the former steps, so
    /// the evaluator never builds this. `len` is therefore already forced.
    Vec {
        level: Level,
        elem: &'v TyClo<'v>,
        len: Rc<Val<'v>>,
    },
    /// See [`VTy::Vec`].
    Fin { len: Rc<Val<'v>> },
    /// Binds *universe* variables, not a local: entered by instantiating the
    /// body syntax and evaluating it in the **unchanged** environment
    /// (`inst_univ` renumbers the outer scope back down, so the captured
    /// environment is already in the post-instantiation scope).
    UPi {
        num_vars: u32,
        level: Level,
        body: &'v TyClo<'v>,
    },
    /// Binds a *global* (context) variable; see [`VTy::UPi`].
    CtxPi { level: Level, body: &'v TyClo<'v> },
    /// Binds a *global* (type) variable; `ctx` is the argument's local
    /// context Δ and stays syntax (design §3.4).
    TyPi {
        ctx: LocalCtx,
        arg_level: Level,
        body_level: Level,
        body: &'v TyClo<'v>,
    },
    CodeTy { ctx: LocalCtx, level: Level },
    /// `ty` is scoped in Δ — a *different* local scope — and therefore stays
    /// syntax.
    CodeTm {
        ctx: LocalCtx,
        ty: Rc<Type>,
        level: Level,
    },
    Neutral(VNeTy<'v>),
}

// ---------------------------------------------------------------------------
// Term values
// ---------------------------------------------------------------------------

/// Weak head normal **terms**.
pub enum Val<'v> {
    // -- encodings of types (decoded by `El`) --
    TmNat,
    TmTy(Level),
    TmUnit { level: Level },
    TmEmpty { level: Level },
    TmSEmpty { level: Level },
    TmSquash {
        level: Level,
        ty: &'v TmClo<'v>,
    },
    TmPi {
        dom_level: Level,
        cod_level: Level,
        dom: &'v TmClo<'v>,
        cod: &'v TmClo<'v>,
    },
    TmSigma {
        fst_level: Level,
        snd_level: Level,
        fst: &'v TmClo<'v>,
        snd: &'v TmClo<'v>,
    },
    TmW {
        shape_level: Level,
        pos_level: Level,
        shape: &'v TmClo<'v>,
        pos: &'v TmClo<'v>,
    },
    TmWf {
        level: Level,
        shape: &'v TmClo<'v>,
        arity: &'v TmClo<'v>,
    },
    TmId {
        level: Level,
        ty: &'v TmClo<'v>,
        lhs: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
    },
    TmSEq {
        level: Level,
        ty: &'v TmClo<'v>,
        lhs: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
    },
    TmSum {
        lhs_level: Level,
        rhs_level: Level,
        lhs: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
    },
    TmVec {
        level: Level,
        elem: &'v TmClo<'v>,
        len: &'v TmClo<'v>,
    },
    TmFin { len: &'v TmClo<'v> },

    // -- data --
    Zero,
    Succ(&'v TmClo<'v>),
    Refl {
        level: Level,
        ty: &'v TyClo<'v>,
        tm: &'v TmClo<'v>,
    },
    SRefl {
        level: Level,
        ty: &'v TyClo<'v>,
        tm: &'v TmClo<'v>,
    },
    Squash {
        level: Level,
        ty: &'v TyClo<'v>,
        tm: &'v TmClo<'v>,
    },
    Pair {
        fst_level: Level,
        snd_level: Level,
        fst_ty: &'v TyClo<'v>,
        snd_ty: &'v TyClo<'v>,
        fst: &'v TmClo<'v>,
        snd: &'v TmClo<'v>,
    },
    Triv { level: Level },
    Inl {
        lhs_level: Level,
        rhs_level: Level,
        lhs: &'v TyClo<'v>,
        rhs: &'v TyClo<'v>,
        val: &'v TmClo<'v>,
    },
    Inr {
        lhs_level: Level,
        rhs_level: Level,
        lhs: &'v TyClo<'v>,
        rhs: &'v TyClo<'v>,
        val: &'v TmClo<'v>,
    },
    Sup {
        shape_level: Level,
        pos_level: Level,
        shape_ty: &'v TyClo<'v>,
        pos_ty: &'v TyClo<'v>,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
    },
    Supf {
        level: Level,
        shape: &'v TyClo<'v>,
        arity: &'v TmClo<'v>,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
    },

    // -- functions --
    Lam {
        dom_level: Level,
        cod_level: Level,
        dom: &'v TyClo<'v>,
        body: &'v TmClo<'v>,
    },
    /// Binds universe variables; see [`VTy::UPi`].
    ULam {
        num_vars: u32,
        level: Level,
        body: &'v TmClo<'v>,
    },
    CtxLam { level: Level, body: &'v TmClo<'v> },
    TyLam {
        ctx: LocalCtx,
        arg_level: Level,
        body_level: Level,
        body: &'v TmClo<'v>,
    },

    // -- code: inert atoms carrying syntax, with NO environment (§3.5) --
    BoxTy(Rc<Type>),
    BoxTm(Rc<Term>),

    Neutral(Rc<VNeutral<'v>>),
}

impl<'v> Val<'v> {
    /// The neutral variable at concrete level `lvl`.
    pub fn var(lvl: u32) -> Val<'v> {
        Val::Neutral(Rc::new(VNeutral {
            head: Head::Var(lvl),
            spine: Vec::new(),
            unfold: None,
        }))
    }

    /// The neutral variable at abstract-prefix depth `depth`.
    pub fn base_var(depth: u32) -> Val<'v> {
        Val::Neutral(Rc::new(VNeutral {
            head: Head::BaseVar(depth),
            spine: Vec::new(),
            unfold: None,
        }))
    }

    /// Whether this value is a ch. 06 neutral (as opposed to canonical or
    /// ill-typed-stuck).
    pub fn is_neutral(&self) -> bool {
        matches!(self, Val::Neutral(n) if n.head.is_neutral())
    }
}

// ---------------------------------------------------------------------------
// Eliminations
// ---------------------------------------------------------------------------

/// One elimination of a neutral spine, with the eliminator's annotations
/// evaluated (or held as closures) exactly as the corresponding [`Term`]
/// carries them. Conversion compares them where required; for application it
/// instead uses the Pi inferred from the function spine, since well-typedness
/// already forces the stored annotations to agree.
///
/// The four forms whose β needs to rebuild *syntax* (`ElimW`, `ElimWf`, and
/// the two code recursors) carry the environment they were built in; the
/// others reach everything they need through their closures.
#[derive(Clone)]
pub enum Elim<'v> {
    App {
        dom_level: Level,
        cod_level: Level,
        dom: &'v TyClo<'v>,
        cod: &'v TyClo<'v>,
        arg: &'v TmClo<'v>,
    },
    UApp { levels: Vec<Level> },
    /// The argument is a local context, syntax by construction.
    CtxApp { ctx: LocalCtx },
    /// The argument is a type in the binding's Δ — a *different* local scope
    /// — so it stays syntax (design §3.4).
    TyApp { arg: Rc<Type> },
    Fst {
        fst_level: Level,
        snd_level: Level,
        fst_ty: &'v TyClo<'v>,
        snd_ty: &'v TyClo<'v>,
    },
    Snd {
        fst_level: Level,
        snd_level: Level,
        fst_ty: &'v TyClo<'v>,
        snd_ty: &'v TyClo<'v>,
    },
    ElimNat {
        level: Level,
        motive: &'v TyClo<'v>,
        base: &'v TmClo<'v>,
        step: &'v TmClo<'v>,
    },
    ElimEmpty {
        level: Level,
        scrut_level: Level,
        motive: &'v TyClo<'v>,
    },
    ElimSEmpty {
        level: Level,
        scrut_level: Level,
        motive: &'v TyClo<'v>,
    },
    ElimSquash {
        src_level: Level,
        dst_level: Level,
        src_ty: &'v TyClo<'v>,
        motive: &'v TyClo<'v>,
        case: &'v TmClo<'v>,
    },
    Case {
        lhs_level: Level,
        rhs_level: Level,
        motive_level: Level,
        lhs: &'v TyClo<'v>,
        rhs: &'v TyClo<'v>,
        motive: &'v TyClo<'v>,
        case_l: &'v TmClo<'v>,
        case_r: &'v TmClo<'v>,
    },
    ElimW {
        shape_level: Level,
        pos_level: Level,
        motive_level: Level,
        shape: &'v TyClo<'v>,
        pos: &'v TyClo<'v>,
        motive: &'v TyClo<'v>,
        step: &'v TmClo<'v>,
        env: Env<'v>,
    },
    ElimWf {
        level: Level,
        motive_level: Level,
        shape: &'v TyClo<'v>,
        arity: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
        step: &'v TmClo<'v>,
        env: Env<'v>,
    },
    J {
        ty_level: Level,
        motive_level: Level,
        ty: &'v TyClo<'v>,
        lhs: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
        case: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
    },
    Transp {
        ty_level: Level,
        motive_level: Level,
        ty: &'v TyClo<'v>,
        motive: &'v TyClo<'v>,
        lhs: &'v TmClo<'v>,
        rhs: &'v TmClo<'v>,
        tm: &'v TmClo<'v>,
    },
    LetBoxTy {
        motive_level: Level,
        code_level: Level,
        ctx: LocalCtx,
        motive: &'v TyClo<'v>,
        body: &'v TmClo<'v>,
    },
    LetBoxTm {
        motive_level: Level,
        code_level: Level,
        ctx: LocalCtx,
        ty: Rc<Type>,
        motive: &'v TyClo<'v>,
        body: &'v TmClo<'v>,
    },
    ElimCodeTy {
        ty_motive_level: Level,
        tm_motive_level: Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: Level,
        ctx: LocalCtx,
        env: Env<'v>,
    },
    /// `ty` is the recursor's type annotation, **already in WHNF** and
    /// scoped in Δ (ch. 06 fixes the type-then-term reduction order).
    ElimCodeTm {
        ty_motive_level: Level,
        tm_motive_level: Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: Level,
        ctx: LocalCtx,
        ty: Rc<Type>,
        env: Env<'v>,
    },
}

impl Elim<'_> {
    /// A stable name for the elimination form — the head discriminant a
    /// shape comparison keys on.
    pub fn tag(&self) -> &'static str {
        match self {
            Elim::App { .. } => "app",
            Elim::UApp { .. } => "uapp",
            Elim::CtxApp { .. } => "ctxapp",
            Elim::TyApp { .. } => "tyapp",
            Elim::Fst { .. } => "fst",
            Elim::Snd { .. } => "snd",
            Elim::ElimNat { .. } => "elim_Nat",
            Elim::ElimEmpty { .. } => "elim_Empty",
            Elim::ElimSEmpty { .. } => "elim_sEmpty",
            Elim::ElimSquash { .. } => "elim_Squash",
            Elim::Case { .. } => "case",
            Elim::ElimW { .. } => "elim_W",
            Elim::ElimWf { .. } => "elim_Wf",
            Elim::J { .. } => "J",
            Elim::Transp { .. } => "transp",
            Elim::LetBoxTy { .. } => "letbox_Ty",
            Elim::LetBoxTm { .. } => "letbox_Tm",
            Elim::ElimCodeTy { .. } => "elim_CodeTy",
            Elim::ElimCodeTm { .. } => "elim_CodeTm",
        }
    }
}

// ---------------------------------------------------------------------------
// Budget-bounded Debug (CLAUDE.md: never derived, always `node()`-gated)
// ---------------------------------------------------------------------------

impl fmt::Debug for Env<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| write!(f, "ρ[{}]", self.len))
    }
}

impl fmt::Debug for TmClo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            TmClo::Syn { env, body, .. } => write!(f, "⟨{env:?}⊢{body:?}⟩"),
            TmClo::Val(v) => write!(
                f,
                "{:?}",
                v,
            ),
            TmClo::Elim { elim, .. } => write!(f, "⟨·{}⟩", elim.tag()),
        })
    }
}

impl fmt::Debug for TyClo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            TyClo::Syn { env, body, .. } => write!(f, "⟨{env:?}⊢{body:?}⟩"),
            TyClo::Val(v) => write!(f, "{v:?}"),
            TyClo::Vec { elem, len, .. } => write!(f, "⟨Vec({elem:?}; {len:?})⟩"),
            TyClo::El { level, tm, .. } => write!(f, "⟨El[{level:?}]({tm:?})⟩"),
        })
    }
}

impl fmt::Debug for VSubst<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            write!(f, "^{:?}[", self.tail)?;
            for (i, t) in self.terms.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{t:?}")?;
            }
            f.write_str("]")
        })
    }
}

impl fmt::Debug for Head<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Head::Var(l) => write!(f, "x@{l}"),
            Head::BaseVar(d) => write!(f, "g#{d}"),
            Head::Global { var, subst } => write!(f, "u{}{:?}", var.0, subst),
            Head::BoxedGlobalTy(t) => write!(f, "□{t:?}"),
            Head::BoxedGlobalTm(t) => write!(f, "□{t:?}"),
            Head::Stuck(v) => write!(f, "stuck({v:?})"),
        })
    }
}

impl fmt::Debug for VNeutral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            write!(f, "{:?}", self.head)?;
            for e in &self.spine {
                write!(f, " ·{}", e.tag())?;
            }
            if self.unfold.is_some() {
                f.write_str(" ⟨δ⟩")?;
            }
            Ok(())
        })
    }
}

impl fmt::Debug for VNeTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            VNeTy::Global { var, subst } => write!(f, "U{}{:?}", var.0, subst),
            VNeTy::El { level, tm } => write!(f, "El[{level:?}]({tm:?})"),
        })
    }
}

impl fmt::Debug for Elim<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Elim::App { arg, .. } => write!(f, "app({arg:?})"),
            Elim::UApp { levels } => write!(f, "$({} levels)", levels.len()),
            Elim::TyApp { arg } => write!(f, "@({arg:?})"),
            other => f.write_str(other.tag()),
        })
    }
}

impl fmt::Debug for VTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            VTy::Nat => f.write_str("Nat"),
            VTy::Ty(l) => write!(f, "Ty {l:?}"),
            VTy::Unit { level } => write!(f, "Unit {level:?}"),
            VTy::Empty { level } => write!(f, "Empty {level:?}"),
            VTy::SEmpty { level } => write!(f, "sEmpty {level:?}"),
            VTy::Squash { ty, .. } => write!(f, "∥{ty:?}∥"),
            VTy::Pi { dom, cod, .. } => write!(f, "Π({dom:?}). {cod:?}"),
            VTy::Sigma { fst, snd, .. } => write!(f, "Σ({fst:?}). {snd:?}"),
            VTy::W { shape, pos, .. } => write!(f, "W({shape:?}). {pos:?}"),
            VTy::Wf { shape, arity, .. } => write!(f, "Wf({shape:?}). {arity:?}"),
            VTy::Sum { lhs, rhs, .. } => write!(f, "({lhs:?} + {rhs:?})"),
            VTy::Id { ty, lhs, rhs, .. } => write!(f, "Id({ty:?}; {lhs:?}; {rhs:?})"),
            VTy::SEq { ty, lhs, rhs, .. } => write!(f, "sEq({ty:?}; {lhs:?}; {rhs:?})"),
            VTy::Vec { elem, len, .. } => write!(f, "Vec({elem:?}; {len:?})"),
            VTy::Fin { len } => write!(f, "Fin({len:?})"),
            VTy::UPi { num_vars, body, .. } => write!(f, "ΠΠ[{num_vars}ℓ]. {body:?}"),
            VTy::CtxPi { body, .. } => write!(f, "(g:Ctx)⇒ {body:?}"),
            VTy::TyPi { body, .. } => write!(f, "(U:Typ)⇒ {body:?}"),
            VTy::CodeTy { level, .. } => write!(f, "□(⊢ Ty {level:?})"),
            VTy::CodeTm { ty, level, .. } => write!(f, "□(⊢ {ty:?} @ {level:?})"),
            VTy::Neutral(n) => write!(f, "{n:?}"),
        })
    }
}

impl fmt::Debug for Val<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Val::TmNat => f.write_str("`Nat"),
            Val::TmTy(l) => write!(f, "`Ty {l:?}"),
            Val::TmUnit { .. } => f.write_str("`Unit"),
            Val::TmEmpty { .. } => f.write_str("`Empty"),
            Val::TmSEmpty { .. } => f.write_str("`sEmpty"),
            Val::TmSquash { ty, .. } => write!(f, "`Squash({ty:?})"),
            Val::TmPi { dom, cod, .. } => write!(f, "`Π({dom:?}). {cod:?}"),
            Val::TmSigma { fst, snd, .. } => write!(f, "`Σ({fst:?}). {snd:?}"),
            Val::TmW { shape, pos, .. } => write!(f, "`W({shape:?}). {pos:?}"),
            Val::TmWf { shape, arity, .. } => write!(f, "`Wf({shape:?}). {arity:?}"),
            Val::TmId { ty, lhs, rhs, .. } => write!(f, "`Id({ty:?}; {lhs:?}; {rhs:?})"),
            Val::TmSEq { ty, lhs, rhs, .. } => write!(f, "`sEq({ty:?}; {lhs:?}; {rhs:?})"),
            Val::TmSum { lhs, rhs, .. } => write!(f, "`({lhs:?} + {rhs:?})"),
            Val::TmVec { elem, len, .. } => write!(f, "`Vec({elem:?}; {len:?})"),
            Val::TmFin { len } => write!(f, "`Fin({len:?})"),
            Val::Zero => f.write_str("ze"),
            Val::Succ(t) => write!(f, "su {t:?}"),
            Val::Refl { tm, .. } => write!(f, "refl({tm:?})"),
            Val::SRefl { tm, .. } => write!(f, "srefl({tm:?})"),
            Val::Squash { tm, .. } => write!(f, "squash({tm:?})"),
            Val::Pair { fst, snd, .. } => write!(f, "⟨{fst:?}, {snd:?}⟩"),
            Val::Triv { .. } => f.write_str("⟨⟩"),
            Val::Inl { val, .. } => write!(f, "inl({val:?})"),
            Val::Inr { val, .. } => write!(f, "inr({val:?})"),
            Val::Sup { label, children, .. } => write!(f, "sup({label:?}; {children:?})"),
            Val::Supf { label, children, .. } => write!(f, "sup_f({label:?}; {children:?})"),
            Val::Lam { dom, body, .. } => write!(f, "λ({dom:?}). {body:?}"),
            Val::ULam { num_vars, body, .. } => write!(f, "Λ[{num_vars}ℓ]. {body:?}"),
            Val::CtxLam { body, .. } => write!(f, "Λ(g). {body:?}"),
            Val::TyLam { body, .. } => write!(f, "Λ(U). {body:?}"),
            Val::BoxTy(t) => write!(f, "box {t:?}"),
            Val::BoxTm(t) => write!(f, "box {t:?}"),
            Val::Neutral(n) => write!(f, "{n:?}"),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{TmClo, Val, ValueArena, ValueMetrics};
    use std::rc::Rc;

    #[test]
    fn deep_arena_value_chain_drops_without_using_the_native_stack() {
        let arena = ValueArena::new();
        let mut clo = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        for _ in 0..100_000 {
            clo = arena.tm(TmClo::val(Rc::new(Val::Succ(clo))));
        }
        assert!(arena.memo_tm(clo).is_some());
    }

    #[test]
    fn environment_value_identity_ignores_nodes_but_not_captured_values() {
        let arena = ValueArena::new();
        let base = super::Env::empty(&arena);
        let shared = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let left = base.push(shared);
        let right = base.push(shared);
        assert!(!super::Env::ptr_eq(&left, &right));
        assert!(super::Env::values_ptr_eq(&left, &right));

        let separately_allocated = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let different = base.push(separately_allocated);
        assert!(!super::Env::values_ptr_eq(&left, &different));
    }

    #[test]
    fn query_value_cache_is_bounded() {
        let metrics = ValueMetrics::default();
        let arena = ValueArena::profiled(&metrics);
        let env = super::Env::empty(&arena);
        let mut closures = Vec::with_capacity(super::VALUE_CACHE_CAPACITY + 1);
        for _ in 0..=super::VALUE_CACHE_CAPACITY {
            let clo = arena.tm(TmClo::syn(env, Rc::new(crate::term::Term::Zero)));
            arena.cache_tm(clo, &Rc::new(Val::Zero));
            closures.push(clo);
        }
        assert!(arena.memo_tm(closures[0]).is_none());
        assert!(arena.memo_tm(*closures.last().expect("one cached closure")).is_some());
        #[cfg(feature = "value-metrics")]
        {
            let stats = metrics.snapshot();
            assert_eq!(stats.arenas, 1);
            assert_eq!(stats.term_closures, (super::VALUE_CACHE_CAPACITY + 1) as u64);
            assert_eq!(stats.term_cache_inserts, (super::VALUE_CACHE_CAPACITY + 1) as u64);
            assert_eq!(stats.term_cache_evictions, 1);
            assert_eq!(stats.term_cache_peak, super::VALUE_CACHE_CAPACITY as u64);
            assert_eq!(stats.term_cache_lookups, 2);
            assert_eq!(stats.term_cache_hits, 1);

            metrics.reset();
            assert_eq!(metrics.snapshot(), Default::default());
        }
    }
}
