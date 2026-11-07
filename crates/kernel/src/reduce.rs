//! Untyped weak-head reduction `⇝` and WHNF/neutral classification
//! (docs/delam/06, §Weak Head Normal Forms and §Reduction Relations).
//!
//! - Reduction is **untyped** and fires on head *shape* only: level
//!   annotations never gate a β-rule (they are forced by typing;
//!   preservation is the paper's job, not this function's).
//! - [`step_term`]/[`step_type`] are the single-step relation; `Ok(None)` means
//!   no rule applies — true for WHNFs and neutrals, but also for ill-typed
//!   stuck terms (e.g. `elim_Nat` on a λ), which the classification
//!   predicates deliberately do not cover.
//! - The ambient local context `Γ` parameterizes reduction because
//!   β-substitutions materialize `id_Γ` explicitly; only Γ's *shape*
//!   (length and base) is read, entry types are never inspected.
//! - Recursor β instantiates the branch telescopes (documented on
//!   [`Branches`]) in three stages: universe instantiation
//!   (innermost-first), global instantiation (payloads outermost-first),
//!   then the recursive-call local substitution `id_Γ, s⃗/x⃗`.
//! - For `ElimCodeTm` the type annotation reduces to WHNF *before* the
//!   scrutinee (the paper fixes this order); its β-rule on `box (λ…)` reads
//!   the return type off that WHNF `Π` annotation — the λ syntax itself
//!   does not carry it.
//! - Recursors block (are neutral) on neutral scrutinees and on
//!   `box (U^δ)` / `box (u^δ)`.
//! - **Who calls this** (since 2026-07-31): `typing.rs`, whose whnf this
//!   still is; the shared β helpers, which the value machine reuses rather
//!   than transcribe; and `conv::oracle`, the differential oracle.
//!   Conversion itself evaluates (`eval.rs`) — and so this file's standing
//!   became *the specification*: it is ch. 06's relation transcribed rule
//!   for rule, and the machine is measured against it, which is why it is
//!   not going anywhere. See DESIGN.md, *Algorithms*.
//! - **δ (extension)**: the `_delta` entry points take a [`Defs`] and add
//!   the one rule `u^δ ⇝ t[δ]` for a *defined* global. The Ψ-free names
//!   ([`step_term`], [`whnf_term`], …) are ch. 06's relation exactly and
//!   unfold nothing; so are the classification predicates, which therefore
//!   call every global neutral — the layer-c view, and the only one that
//!   reaches inside a `box`.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    iwf_children_ty, iwf_ih, iwf_motive_scrut_ty, iwf_step_telescope, m_out_corec, m_step_ty, nth,
    wf_step_telescope, IWfSig, MSig, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx,
    LocalSubst, LocalVar, Term, Type,
};

/// Reduction ran out of fuel before reaching a normal form. On well-typed
/// input this indicates the fuel bound was too small (reduction of
/// well-typed terms terminates); on untyped input it may be divergence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutOfFuel;

/// How deep the checker's **native** recursion may go before it reports
/// [`OutOfFuel`] instead of overflowing the thread's stack.
///
/// Fuel bounds the *steps* a reduction takes; it does not bound the frames a
/// reduction stands on, and the two are unrelated when a value nests
/// scrutinees (docs/native-depth-budget-design.md). The account is shared
/// across conversion's recursion and the evaluator's re-entries for the same
/// reason fuel is: they interleave on one native stack.
///
/// Like fuel, this is an invariant on *whether* the machine answers and never
/// a cost model — an answer given under it agrees with the answer the deeper
/// stack gives. The value sits between what the deepest known good workload
/// needs and what the 8 MiB rail (`RUST_MIN_STACK` in `scripts/test`)
/// measurably holds. What a counted level costs is a property of the frames
/// the recursion passes through, which are kept small on purpose (design
/// §8: a function a counted recursion passes through is a dispatcher), so
/// moving this number needs both the design doc's ends re-read and the
/// `stack/eval-nested-scrutinee` probe re-run.
pub const NATIVE_DEPTH_LIMIT: u32 = 2048;

/// [`NATIVE_DEPTH_LIMIT`] for the small-step reducer's own account
/// (`Frames`, docs/native-depth-budget-design.md §7).
///
/// Separate because the reducer's frame is separate: a counted step stands
/// on `step_term_frame`, whose one match holds every rule's temporaries and
/// costs several times what a counted evaluator or conversion level does
/// since those were split (design §8). The reducer is not on the checking
/// path's hot side — it spells, and it is the oracle's — so it keeps the
/// bound its frame was measured at rather than holding the shared one back.
pub const REDUCER_DEPTH_LIMIT: u32 = 1024;

/// The native stack [`NATIVE_DEPTH_LIMIT`] was measured against, for a thread
/// that runs the kernel. A thread with less aborts on a stack overflow where
/// this one answers `OutOfFuel`, and a SIGABRT is not a verdict. Rust gives a
/// spawned thread 2 MiB unless `RUST_MIN_STACK` says otherwise, and only
/// `scripts/test` says otherwise, so a thread that runs the kernel asks for
/// this size itself (issues/kernel-worker-stack-below-depth-budget.md).
pub const NATIVE_STACK_BYTES: usize = 8 << 20;

// ---------------------------------------------------------------------------
// δ: definition unfolding, and the layer that owns it
// ---------------------------------------------------------------------------

/// The δ-environment of a reduction: the Ψ whose **definitions**
/// ([`GlobalBinding::Tm`] with a body) may unfold, or [`Defs::opaque`] for
/// the paper's Ψ-free reduction.
///
/// Transparency is layer-indexed (extension,
/// issues/simulate-conversion-cost.md). At the computing layers p/m a
/// definition is its body: `u^δ ⇝ t[δ]`, ordinary δ-reduction, which is
/// what makes running a Ψ-referenced program cheap. At layer c a global is
/// *syntax* — ch. 06 blocks the code-recursion principles on globals and
/// compares boxed globals syntactically, so a code-level conversion that
/// identified `box(u)` with `box(t)` while the recursor distinguished them
/// would break coherence. [`Defs::opaque`] is therefore the only correct
/// choice at c, and it is what every layer-c path here uses: reduction
/// never enters a `box`, and `conv.rs` compares boxed code with `==`.
#[derive(Clone, Copy)]
pub struct Defs<'a> {
    psi: Option<&'a GlobalCtx>,
    cache: Option<&'a GlobalCache>,
}

/// A binding's **signature**, rescoped from its own Ψ-prefix into the ambient
/// Ψ: the declared local context, and — for a term binding — its declared
/// type. What the `u^δ` / `U^δ` rules of [`crate::conv`] and [`crate::typing`]
/// read off a global occurrence, and all they read.
pub(crate) struct Sig {
    pub(crate) ctx: LocalCtx,
    pub(crate) ty: Option<Rc<Type>>,
}

/// Rescoped per-Ψ facts about a global binding, memoized by [`GlobalVar`]:
/// its definition body, and its signature.
///
/// Both are `shift_global(v + 1)` of something stored in Ψ, and both are a
/// function of the index alone — not of the occurrence, not of the δ that
/// occurrence carries. A cache is therefore sound *for one Ψ*, which is why
/// it is owned beside the Ψ it belongs to (`conv::Env`, `typing::Env`) and
/// rebuilt whenever a telescope push changes Ψ, rather than being a global
/// table keyed by an index that means different things in different scopes.
/// An entry surviving a push would answer about the wrong binding: a
/// soundness bug, not a slowdown.
#[derive(Default)]
pub struct GlobalCache {
    bodies: std::cell::RefCell<Vec<Option<Rc<Term>>>>,
    sigs: std::cell::RefCell<Vec<Option<Rc<Sig>>>>,
}

impl GlobalCache {
    pub fn new() -> GlobalCache {
        GlobalCache::default()
    }

    fn body_or_insert(&self, v: GlobalVar, build: impl FnOnce() -> Term) -> Rc<Term> {
        let mut slots = self.bodies.borrow_mut();
        slot_or_insert(&mut slots, v, || Rc::new(build()))
    }

    /// The rescoped signature of `v`, built on the first occurrence in this Ψ.
    /// `build` reads only Ψ, never the cache, so there is no re-entrant borrow.
    pub(crate) fn sig_or_insert(&self, v: GlobalVar, build: impl FnOnce() -> Sig) -> Rc<Sig> {
        let mut slots = self.sigs.borrow_mut();
        slot_or_insert(&mut slots, v, || {
            crate::stats::global_sig_rescopes(1);
            Rc::new(build())
        })
    }
}

fn slot_or_insert<T>(
    slots: &mut Vec<Option<Rc<T>>>,
    v: GlobalVar,
    build: impl FnOnce() -> Rc<T>,
) -> Rc<T> {
    let i = v.0 as usize;
    if slots.len() <= i {
        slots.resize_with(i + 1, || None);
    }
    if let Some(t) = &slots[i] {
        return Rc::clone(t);
    }
    let t = build();
    slots[i] = Some(Rc::clone(&t));
    t
}

impl<'a> Defs<'a> {
    /// Nothing unfolds: every global is an opaque neutral, exactly as in
    /// ch. 06's reduction relation. The right choice at layer c, and the
    /// meaning of the Ψ-free [`step_term`]/[`whnf_term`] entry points.
    pub fn opaque() -> Defs<'a> {
        Defs { psi: None, cache: None }
    }

    /// Definitions of `psi` unfold. Only sound at a computing layer.
    pub fn transparent(psi: &'a GlobalCtx) -> Defs<'a> {
        Defs { psi: Some(psi), cache: None }
    }

    /// [`Defs::transparent`] with a [`GlobalCache`] to memoize the rescoping
    /// in. The cache must belong to this exact `psi`.
    pub fn transparent_cached(psi: &'a GlobalCtx, cache: &'a GlobalCache) -> Defs<'a> {
        Defs { psi: Some(psi), cache: Some(cache) }
    }

    /// The body of `v`, rescoped from its Ψ-prefix into the ambient Ψ (the
    /// `shift_global(v + 1)` convention `typing.rs` uses for the binding's
    /// type). `None` for a declaration, an out-of-scope index, or an opaque
    /// environment.
    pub(crate) fn body(&self, v: GlobalVar) -> Option<Rc<Term>> {
        if self.withheld(v).is_some() {
            return None;
        }
        self.body_of(v)
    }

    /// [`Defs::body`] whatever the interface boundary says: the body a
    /// saturated closed call of a withheld definition unfolds to.
    pub(crate) fn withheld_body(&self, v: GlobalVar) -> Option<Rc<Term>> {
        self.withheld(v)?;
        self.body_of(v)
    }

    /// The arity `v` is withheld at by this world's interface boundary
    /// ([`crate::term::GlobalCtx::withheld`]), or `None` when it is not
    /// withheld. A withheld definition is not a definition to [`Defs::body`],
    /// [`Defs::body_unshifted`] or [`Defs::is_defined`]: it unfolds only
    /// through [`Defs::withheld_body`] at a call of this many arguments none
    /// of which reads a free local variable
    /// (`docs/interface-definitions-design.md` §3).
    pub fn withheld(&self, v: GlobalVar) -> Option<u32> {
        let psi = self.psi?;
        let w = psi.withheld.as_ref()?;
        let i = psi.bindings.len().checked_sub(1 + v.0 as usize)?;
        w.arity(i)
    }

    /// `v`'s absolute index in this world's Ψ.
    pub(crate) fn absolute(&self, v: GlobalVar) -> Option<usize> {
        self.psi?.bindings.len().checked_sub(1 + v.0 as usize)
    }

    fn body_of(&self, v: GlobalVar) -> Option<Rc<Term>> {
        let psi = self.psi?;
        let i = psi.bindings.len().checked_sub(1 + v.0 as usize)?;
        let GlobalBinding::Tm { body: Some(t), .. } = psi.bindings.get(i)? else {
            return None;
        };
        let rescope = || {
            crate::stats::delta_body_rescopes(1);
            t.shift_global(v.0 + 1)
        };
        Some(match self.cache {
            Some(c) => c.body_or_insert(v, rescope),
            None => Rc::new(rescope()),
        })
    }

    /// The body of `v` **as it is stored**, in its own Ψ-prefix rather than
    /// in the ambient Ψ: the value machine reads it under the global offset
    /// `v + 1` instead of paying for a copy per gate call
    /// (`docs/lazy-global-offset-design.md`). `None` on the same three
    /// conditions as [`Defs::body`].
    pub(crate) fn body_unshifted(&self, v: GlobalVar) -> Option<&'a Rc<Term>> {
        if self.withheld(v).is_some() {
            return None;
        }
        self.withheld_body_unshifted(v)
    }

    /// [`Defs::body_unshifted`] whatever the interface boundary says.
    pub(crate) fn withheld_body_unshifted(&self, v: GlobalVar) -> Option<&'a Rc<Term>> {
        let psi = self.psi?;
        let i = psi.bindings.len().checked_sub(1 + v.0 as usize)?;
        let GlobalBinding::Tm { body: Some(t), .. } = psi.bindings.get(i)? else {
            return None;
        };
        Some(t)
    }

    /// Whether `v` is an opaque binding whose proof Ψ keeps sealed
    /// ([`crate::term::GlobalCtx::sealed`]). Such a binding is *not* a
    /// definition: δ never unfolds it, and only an elimination stuck on an
    /// application of it unseals it ([`Defs::sealed_body`]).
    pub fn is_sealed(&self, v: GlobalVar) -> bool {
        // Asked without loading a lazily kept proof: a stuck head is tested
        // far more often than it is opened.
        let Some(psi) = self.psi else { return false };
        psi.bindings.len().checked_sub(1 + v.0 as usize).is_some_and(|i| psi.sealed_kept(i).is_some())
    }

    fn sealed_at(&self, v: GlobalVar) -> Option<(usize, &'a Rc<Term>)> {
        let psi = self.psi?;
        let i = psi.bindings.len().checked_sub(1 + v.0 as usize)?;
        Some((i, psi.sealed_proof(i)?))
    }

    /// The sealed proof of `v`, rescoped like [`Defs::body`], **for an
    /// elimination stuck on it**: the one place a theorem computes
    /// (`issues/theorem-witness-unfolding.md`, option D). Every call is an
    /// unsealing and is recorded ([`crate::unseal`]), so only call it to
    /// unseal. `None` when `v` keeps no sealed proof here.
    pub(crate) fn sealed_body(&self, v: GlobalVar) -> Option<Rc<Term>> {
        let (i, t) = self.sealed_at(v)?;
        crate::unseal::note(i);
        let rescope = || {
            crate::stats::delta_body_rescopes(1);
            t.shift_global(v.0 + 1)
        };
        // A sealed binding has no body, so the slot is free for its proof.
        Some(match self.cache {
            Some(c) => c.body_or_insert(v, rescope),
            None => Rc::new(rescope()),
        })
    }

    /// The sealed proof of `v` unshifted (the value machine's
    /// [`Defs::body_unshifted`]), with the absolute index it is recorded
    /// under, **without** recording it: the value machine glues the proof
    /// lazily and records the unsealing only when the glue is forced
    /// (`crate::eval`), so a comparison decided on the spine opens nothing.
    pub(crate) fn sealed_proof_unshifted(&self, v: GlobalVar) -> Option<(usize, &'a Rc<Term>)> {
        self.sealed_at(v)
    }

    /// Whether an occurrence `v^δ` whose substitution has `terms` payloads
    /// fits `v`'s declared context: δ supplies exactly one payload per entry
    /// of Δ. Typing demands it of every occurrence (`subst_ck`'s
    /// `SubstMismatch`); δ-reduction, which the elaborator also runs on terms
    /// no judgement has seen, checks it before substituting a body, so an
    /// occurrence that does not fit is an ill-typed **stuck** form, as the
    /// reducer's contract says ([`whnf_type`]), instead of a body
    /// substituted by a δ that does not cover its context. Without the check
    /// a misnumbered global — an elaborator reading a type against the wrong
    /// world — aborted the process in the substitution
    /// (issues/merged-call-through-upcast-panics.md), and the value machine
    /// read the uncovered entries as base variables. An O(1) test: the
    /// binding is looked up by index, as the body is.
    pub(crate) fn fits(&self, v: GlobalVar, terms: usize) -> bool {
        let Some(psi) = self.psi else { return false };
        let Some(i) = psi.bindings.len().checked_sub(1 + v.0 as usize) else {
            return false;
        };
        matches!(psi.bindings.get(i), Some(GlobalBinding::Tm { ctx, .. }) if ctx.entries.len() == terms)
    }

    /// Whether `v` is a definition here — the head test the conversion
    /// heuristic keys on, without paying for the rescoped body.
    pub fn is_defined(&self, v: GlobalVar) -> bool {
        if self.withheld(v).is_some() {
            return false;
        }
        let Some(psi) = self.psi else { return false };
        let Some(i) = psi.bindings.len().checked_sub(1 + v.0 as usize) else {
            return false;
        };
        matches!(psi.bindings.get(i), Some(GlobalBinding::Tm { body: Some(_), .. }))
    }
}

/// Reflexive-transitive closure of type reduction, to WHNF/neutral (or an
/// ill-typed stuck form), spending one fuel per step. Ψ-free: no definition
/// unfolds (see [`Defs`]).
pub fn whnf_type(t: &Type, gamma: &LocalCtx, fuel: u64) -> Result<Type, OutOfFuel> {
    whnf_type_delta(t, gamma, Defs::opaque(), fuel)
}

/// [`whnf_type`] with a δ-environment.
pub fn whnf_type_delta(
    t: &Type,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    mut fuel: u64,
) -> Result<Type, OutOfFuel> {
    let mut cur = t.clone();
    while let Some(next) = step_type_delta(&cur, gamma, defs)? {
        if fuel == 0 {
            return Err(OutOfFuel);
        }
        fuel -= 1;
        cur = next;
    }
    Ok(cur)
}

/// Reflexive-transitive closure of term reduction, to WHNF/neutral (or an
/// ill-typed stuck form), spending one fuel per step. Ψ-free: no definition
/// unfolds (see [`Defs`]).
pub fn whnf_term(t: &Term, gamma: &LocalCtx, fuel: u64) -> Result<Term, OutOfFuel> {
    whnf_term_delta(t, gamma, Defs::opaque(), fuel)
}

/// [`whnf_term`] with a δ-environment.
pub fn whnf_term_delta(
    t: &Term,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    mut fuel: u64,
) -> Result<Term, OutOfFuel> {
    let mut cur = t.clone();
    while let Some(next) = step_term_delta(&cur, gamma, defs)? {
        if fuel == 0 {
            return Err(OutOfFuel);
        }
        fuel -= 1;
        cur = next;
    }
    Ok(cur)
}

// ---------------------------------------------------------------------------
// Single-step reduction
// ---------------------------------------------------------------------------

/// Single-step type reduction `T ⇝ T'`: the `El` decode rules plus
/// congruence into the encoding.
pub fn step_type(t: &Type, gamma: &LocalCtx) -> Result<Option<Type>, OutOfFuel> {
    step_type_delta(t, gamma, Defs::opaque())
}

/// [`step_type`] with a δ-environment. Type-level bindings have no bodies —
/// a `U^δ` is opaque at every layer — so δ reaches types only through `El`.
pub fn step_type_delta(t: &Type, gamma: &LocalCtx, defs: Defs<'_>) -> Result<Option<Type>, OutOfFuel> {
    let frames = Frames::default();
    let next = step_type_in(t, gamma, defs, &frames);
    frames.answer(next)
}

/// The native frames one step stands on. A step steps the head or scrutinee
/// it is blocked on first, so its recursion is as deep as the nesting of
/// blocked heads, and fuel, which counts steps, never sees it: the first step
/// of `x < pow(3, 5000)` stands on thousands of frames. Past
/// [`REDUCER_DEPTH_LIMIT`] a step gives up; every `None` above it is then
/// discarded, and the step answers [`OutOfFuel`] rather than "no rule
/// applies".
#[derive(Default)]
struct Frames {
    depth: std::cell::Cell<u32>,
    exhausted: std::cell::Cell<bool>,
}

impl Frames {
    fn enter(&self) -> bool {
        let depth = self.depth.get();
        if depth >= REDUCER_DEPTH_LIMIT {
            self.exhausted.set(true);
            return false;
        }
        self.depth.set(depth + 1);
        true
    }

    fn leave(&self) {
        self.depth.set(self.depth.get() - 1);
    }

    fn answer<T>(&self, next: Option<T>) -> Result<Option<T>, OutOfFuel> {
        if self.exhausted.get() { Err(OutOfFuel) } else { Ok(next) }
    }
}

fn step_type_in(t: &Type, gamma: &LocalCtx, defs: Defs<'_>, frames: &Frames) -> Option<Type> {
    if !frames.enter() {
        return None;
    }
    let next = step_type_frame(t, gamma, defs, frames);
    frames.leave();
    next
}

fn step_term_in(t: &Term, gamma: &LocalCtx, defs: Defs<'_>, frames: &Frames) -> Option<Term> {
    if !frames.enter() {
        return None;
    }
    let next = step_term_frame(t, gamma, defs, frames);
    frames.leave();
    next
}

fn step_type_frame(t: &Type, gamma: &LocalCtx, defs: Defs<'_>, frames: &Frames) -> Option<Type> {
    match t {
        Type::El { level, tm } => match &**tm {
            // El^0 Nat ⇝ Nat
            Term::TmNat => Some(Type::Nat),
            // El^{1+l} (Ty l) ⇝ Ty l
            Term::TmTy(l) => Some(Type::Ty(l.clone())),
            // El^{l⊔l'} (Π^{l,l'} x s t) ⇝ Π^{l,l'} (x : El^l s). El^{l'} t
            Term::TmPi { dom_level, cod_level, dom, cod } => Some(Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(Type::El { level: dom_level.clone(), tm: Rc::clone(dom) }),
                cod: Rc::new(Type::El { level: cod_level.clone(), tm: Rc::clone(cod) }),
            }),
            // El^l (Id^l s t u) ⇝ Id^l (El^l s; t; u)   (extension)
            Term::TmId { level: l, ty, lhs, rhs } => Some(Type::Id {
                level: l.clone(),
                ty: Rc::new(Type::El { level: l.clone(), tm: Rc::clone(ty) }),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            }),
            // El^{l⊔l'} (Σ^{l,l'} s t) ⇝ Σ^{l,l'}(El^l s; El^l' t)   (extension)
            Term::TmSigma { fst_level, snd_level, fst, snd } => Some(Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: Rc::new(Type::El { level: fst_level.clone(), tm: Rc::clone(fst) }),
                snd: Rc::new(Type::El { level: snd_level.clone(), tm: Rc::clone(snd) }),
            }),
            // El^l (Unit^l) ⇝ Unit^l, El^l (Empty^l) ⇝ Empty^l   (extension)
            Term::TmUnit { level } => Some(Type::Unit { level: level.clone() }),
            Term::TmEmpty { level } => Some(Type::Empty { level: level.clone() }),
            // El^l (sEq^l s t u) ⇝ sEq^l (El^l s; t; u), El^l (sEmpty^l) ⇝
            // sEmpty^l — mirror TmId/TmEmpty.   (extension)
            Term::TmSEq { level: l, ty, lhs, rhs } => Some(Type::SEq {
                level: l.clone(),
                ty: Rc::new(Type::El { level: l.clone(), tm: Rc::clone(ty) }),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            }),
            Term::TmSEmpty { level } => Some(Type::SEmpty { level: level.clone() }),
            Term::TmSquash { level, ty } => Some(Type::Squash {
                level: level.clone(),
                ty: Rc::new(Type::El { level: level.clone(), tm: Rc::clone(ty) }),
            }),
            // El^{l⊔l'} (s +^{l,l'} t) ⇝ El^l s +^{l,l'} El^l' t   (extension)
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => Some(Type::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: Rc::new(Type::El { level: lhs_level.clone(), tm: Rc::clone(lhs) }),
                rhs: Rc::new(Type::El { level: rhs_level.clone(), tm: Rc::clone(rhs) }),
            }),
            // El^{l⊔l'} (W (x:s). t) ⇝ W (x : El^l s). El^{l'} t   (extension)
            Term::TmW { shape_level, pos_level, shape, pos } => Some(Type::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: Rc::new(Type::El { level: shape_level.clone(), tm: Rc::clone(shape) }),
                pos: Rc::new(Type::El { level: pos_level.clone(), tm: Rc::clone(pos) }),
            }),
            // El^l (Vec^l(s; k)) ⇝ Vec^l(El^l s; k)   (extension, §6)
            Term::TmVec { level: l, elem, len } => Some(Type::Vec {
                level: l.clone(),
                elem: Rc::new(Type::El { level: l.clone(), tm: Rc::clone(elem) }),
                len: Rc::clone(len),
            }),
            // El^0 (Fin k) ⇝ Fin k   (extension, §6)
            Term::TmFin { len } => Some(Type::Fin { len: Rc::clone(len) }),
            // El^l (Wf^l(x:s). n) ⇝ Wf^l(x : El^l s). n   (extension, §6);
            // the arity is a term under the same binder, so it is carried
            // across unchanged — only the shape decodes.
            Term::TmWf { level: l, shape, arity } => Some(Type::Wf {
                level: l.clone(),
                shape: Rc::new(Type::El { level: l.clone(), tm: Rc::clone(shape) }),
                arity: Rc::clone(arity),
            }),
            // El^l (DVec^l(k; i. f)) ⇝ DVec^l(k; i. El^l f)
            // (docs/iwf-former-design.md §6).
            Term::TmDVec { level: l, len, fam } => Some(Type::DVec {
                level: l.clone(),
                len: Rc::clone(len),
                fam: Rc::new(Type::El { level: l.clone(), tm: Rc::clone(fam) }),
            }),
            // El(TmIWf …) ⇝ IWf(El idx; x : El shape. arity; out; child)(index)
            // (design §6).
            Term::TmIWf { level: l, idx_level, idx, shape, arity, out, child, index } => Some(Type::IWf {
                sig: Rc::new(crate::term::iwf_sig_of_code(l, idx_level, idx, shape, arity, out, child)),
                index: Rc::clone(index),
            }),
            // El(TmM …) ⇝ M(El idx; El shape; El pos; next)(index)
            // (docs/kernel-m-codes-design.md §1).
            Term::TmM { level: l, pos_level, idx_level, idx, shape, pos, next, index } => Some(Type::M {
                sig: Rc::new(crate::term::m_sig_of_code(l, pos_level, idx_level, idx, shape, pos, next)),
                index: Rc::clone(index),
            }),
            _ => step_term_in(tm, gamma, defs, frames)
                .map(|tm| Type::El { level: level.clone(), tm: Rc::new(tm) }),
        },
        // Vec^l(T; 0) ⇝ Unit^l, Vec^l(T; S k) ⇝ Σ^{l,l}(_ : T). Vec^l(T; k).
        // The tail is under the Σ's binder, so the length is shifted; `T`
        // and the tail's `T` likewise (docs/wf-former-design.md §1.1).
        //
        // **The nullary reduct carries `l`.** It did not until 2026-07-25,
        // which broke ch. 06's Preservation for every `l ≠ 0` and left the
        // nullary constructor of a level-`l` `Wf` uninhabitable — the defect
        // route (a) exists to close (docs/unit-empty-level-indexing.md §1).
        Type::Vec { level, elem, len } => match &**len {
            t if crate::term::is_nat_zero(t) => Some(Type::Unit { level: level.clone() }),
            Term::Succ(pred) => Some(Type::Sigma {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst: Rc::clone(elem),
                snd: Rc::new(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(elem.shift_local(1)),
                    len: Rc::new(pred.shift_local(1)),
                }),
            }),
            Term::NatLit(n) => {
                let pred = crate::term::nat_lit_pred(n);
                Some(Type::Sigma {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst: Rc::clone(elem),
                    snd: Rc::new(Type::Vec {
                        level: level.clone(),
                        elem: Rc::new(elem.shift_local(1)),
                        len: Rc::new(pred),
                    }),
                })
            }
            _ => step_term_in(len, gamma, defs, frames).map(|len| Type::Vec {
                level: level.clone(),
                elem: Rc::clone(elem),
                len: Rc::new(len),
            }),
        },
        // DVec^l(0; i. F) ⇝ Unit^l,
        // DVec^l(S k; i. F) ⇝ Σ^{l,l}(_ : F[inl ⟨⟩/i]). DVec^l(k; j. F[inr j/i])
        // (docs/iwf-former-design.md §1.1). The nullary reduct carries `l`,
        // as `Vec`'s does.
        Type::DVec { level, len, fam } => match &**len {
            t if crate::term::is_nat_zero(t) => Some(Type::Unit { level: level.clone() }),
            Term::Succ(pred) => Some(crate::term::dvec_succ_reduct(level, pred, fam)),
            Term::NatLit(n) => {
                let pred = Rc::new(crate::term::nat_lit_pred(n));
                Some(crate::term::dvec_succ_reduct(level, &pred, fam))
            }
            _ => step_term_in(len, gamma, defs, frames).map(|len| Type::DVec {
                level: level.clone(),
                len: Rc::new(len),
                fam: Rc::clone(fam),
            }),
        },
        // Fin(0) ⇝ Empty^0, Fin(S k) ⇝ Unit^0 +^{0,0} Fin(k).   (§1.2)
        // `Fin` is declared at level 0, so both reducts land there and it
        // needs nothing from the level-indexing round.
        Type::Fin { len } => match &**len {
            t if crate::term::is_nat_zero(t) => Some(Type::Empty { level: Level::Zero }),
            Term::Succ(pred) => Some(Type::Sum {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: Rc::new(Type::Unit { level: Level::Zero }),
                rhs: Rc::new(Type::Fin { len: Rc::clone(pred) }),
            }),
            Term::NatLit(n) => Some(Type::Sum {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: Rc::new(Type::Unit { level: Level::Zero }),
                rhs: Rc::new(Type::Fin {
                    len: Rc::new(crate::term::nat_lit_pred(n)),
                }),
            }),
            _ => step_term_in(len, gamma, defs, frames).map(|len| Type::Fin { len: Rc::new(len) }),
        },
        _ => None,
    }
}

/// Single-step term reduction `t ⇝ t'`: β for all elimination forms plus
/// congruence at head positions.
pub fn step_term(t: &Term, gamma: &LocalCtx) -> Result<Option<Term>, OutOfFuel> {
    step_term_delta(t, gamma, Defs::opaque())
}

/// [`step_term`] with a δ-environment: the single new rule is
/// `u^δ ⇝ t[δ]` when `u` is a definition of `defs` (extension). It needs no
/// arm of its own anywhere else — every congruence below already steps its
/// head/scrutinee, so a defined global unblocks the whole spine.
pub fn step_term_delta(t: &Term, gamma: &LocalCtx, defs: Defs<'_>) -> Result<Option<Term>, OutOfFuel> {
    let frames = Frames::default();
    let next = step_term_in(t, gamma, defs, &frames);
    frames.answer(next)
}

/// Step an elimination's scrutinee: unseal it when it is an application
/// spine of a sealed theorem (`issues/theorem-witness-unfolding.md`, option
/// D), and otherwise step it as any term. This is the *only* place the syntax
/// reducer unseals: a bare `u a⃗` with no elimination waiting on it stays
/// stuck, so a proof is opened exactly where something needs to compute
/// with what it built.
fn step_scrut(t: &Term, gamma: &LocalCtx, defs: Defs<'_>, frames: &Frames) -> Option<Term> {
    unseal_spine(t, defs).or_else(|| step_term_in(t, gamma, defs, frames))
}

/// `u a⃗` with the sealed theorem `u` replaced by its proof; `None` unless the
/// spine's head is a sealed theorem of `defs`.
fn unseal_spine(t: &Term, defs: Defs<'_>) -> Option<Term> {
    Some(match t {
        Term::GlobalTm { var, subst } => {
            if !defs.is_sealed(*var) || !defs.fits(*var, subst.terms.len()) {
                return None;
            }
            defs.sealed_body(*var)?.apply_local(subst)
        }
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => Term::App {
            fun: Rc::new(unseal_spine(fun, defs)?),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
            arg: Rc::clone(arg),
        },
        Term::AppAt { fun, arg } => Term::AppAt { fun: Rc::new(unseal_spine(fun, defs)?), arg: Rc::clone(arg) },
        Term::UApp { fun, levels } => Term::UApp { fun: Rc::new(unseal_spine(fun, defs)?), levels: levels.clone() },
        Term::CtxApp { fun, ctx } => Term::CtxApp { fun: Rc::new(unseal_spine(fun, defs)?), ctx: ctx.clone() },
        Term::TyApp { fun, arg } => Term::TyApp { fun: Rc::new(unseal_spine(fun, defs)?), arg: Rc::clone(arg) },
        _ => return None,
    })
}

/// The withheld definition at the head of `t` when `t` is a call of it that
/// may unfold: saturated (at least its arity of term arguments) and closed
/// (those arguments read no free local variable). `docs/interface-definitions-design.md` §3; the value machine's
/// rule is `Eval::glue_withheld`, and the two agree on every argument the
/// value machine can classify.
pub(crate) fn withheld_call(t: &Term, defs: Defs<'_>) -> Option<GlobalVar> {
    let mut args: Vec<&Rc<Term>> = Vec::new();
    let mut cur = t;
    let (var, _) = loop {
        match cur {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                args.push(arg);
                cur = fun;
            }
            Term::UApp { fun, .. } | Term::CtxApp { fun, .. } | Term::TyApp { fun, .. } => cur = fun,
            Term::GlobalTm { var, subst } => break (*var, subst),
            _ => return None,
        }
    };
    let arity = defs.withheld(var)? as usize;
    if arity == 0 || args.len() < arity {
        return None;
    }
    // `args` runs outermost first, so the call's own arguments are its last
    // `arity` entries; any before them are applied to its result. A
    // substitution tail is no sign of a variable (`eval/withheld.rs`).
    let closed = args[args.len() - arity..].iter().all(|a| crate::bounds::term_local_use(a).bound == 0);
    closed.then_some(var)
}

/// `t` with the head of its application spine, a withheld global at a call
/// [`withheld_call`] accepts, replaced by its body.
fn unfold_withheld(t: &Term, defs: Defs<'_>) -> Option<Term> {
    let var = withheld_call(t, defs)?;
    fn rebuild(t: &Term, defs: Defs<'_>, var: GlobalVar) -> Option<Term> {
        Some(match t {
            Term::GlobalTm { var: v, subst } if *v == var => {
                if !defs.fits(var, subst.terms.len()) {
                    return None;
                }
                crate::withheld::note(defs, var);
                defs.withheld_body(var)?.apply_local(subst)
            }
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => Term::App {
                fun: Rc::new(rebuild(fun, defs, var)?),
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
                arg: Rc::clone(arg),
            },
            Term::AppAt { fun, arg } => Term::AppAt { fun: Rc::new(rebuild(fun, defs, var)?), arg: Rc::clone(arg) },
            Term::UApp { fun, levels } => Term::UApp { fun: Rc::new(rebuild(fun, defs, var)?), levels: levels.clone() },
            Term::CtxApp { fun, ctx } => Term::CtxApp { fun: Rc::new(rebuild(fun, defs, var)?), ctx: ctx.clone() },
            Term::TyApp { fun, arg } => Term::TyApp { fun: Rc::new(rebuild(fun, defs, var)?), arg: Rc::clone(arg) },
            _ => return None,
        })
    }
    rebuild(t, defs, var)
}

fn step_term_frame(t: &Term, gamma: &LocalCtx, defs: Defs<'_>, frames: &Frames) -> Option<Term> {
    // A saturated closed call of a withheld definition unfolds its head, as a
    // definition's `u^δ` would; any other application of one stays stuck.
    if matches!(t, Term::App { .. } | Term::AppAt { .. }) {
        if let Some(next) = unfold_withheld(t, defs) {
            return Some(next);
        }
    }
    match t {
        // δ: `u^δ ⇝ t[δ]` for a definition `u := t`. Opaque at layer c,
        // where `defs` is `Defs::opaque()` — see [`Defs`].
        Term::GlobalTm { var, subst } if defs.fits(*var, subst.terms.len()) => {
            Some(defs.body(*var)?.apply_local(subst))
        }
        Term::ElimNat { level, motive, base, step, scrut } => match &**scrut {
            // elim_Nat … ze ⇝ s
            t if crate::term::is_nat_zero(t) => Some((**base).clone()),
            // elim_Nat … (su t) ⇝ s'[t/x, elim_Nat … t/y]
            Term::Succ(pred) => {
                let rec = Term::ElimNat {
                    level: level.clone(),
                    motive: Rc::clone(motive),
                    base: Rc::clone(base),
                    step: Rc::clone(step),
                    scrut: Rc::clone(pred),
                };
                let delta = LocalSubst::id(gamma)
                    .extended(Rc::clone(pred))
                    .extended(Rc::new(rec));
                Some(step.apply_local(&delta))
            }
            Term::NatLit(n) => {
                let pred = Rc::new(crate::term::nat_lit_pred(n));
                let rec = Term::ElimNat {
                    level: level.clone(),
                    motive: Rc::clone(motive),
                    base: Rc::clone(base),
                    step: Rc::clone(step),
                    scrut: Rc::clone(&pred),
                };
                let delta = LocalSubst::id(gamma)
                    .extended(pred)
                    .extended(Rc::new(rec));
                Some(step.apply_local(&delta))
            }
            _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::ElimNat {
                level: level.clone(),
                motive: Rc::clone(motive),
                base: Rc::clone(base),
                step: Rc::clone(step),
                scrut: Rc::new(s),
            }),
        },
        Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
            match &**proof {
                // J … refl ⇝ c   (extension; fires on head shape only)
                Term::Refl { .. } => Some((**case).clone()),
                _ => step_scrut(proof, gamma, defs, frames).map(|p| Term::J {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: Rc::clone(ty),
                    lhs: Rc::clone(lhs),
                    motive: Rc::clone(motive),
                    case: Rc::clone(case),
                    rhs: Rc::clone(rhs),
                    proof: Rc::new(p),
                }),
            }
        }
        // fst (pair a b) ⇝ a; else reduce the pair   (extension)
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => match &**pair {
            // β fires on **either** pair spelling and reads nothing from the
            // pair's annotations (docs/intro-by-type-design.md §2.4; the same
            // statement docs/delam-extensions.md §16.2 already makes for the
            // component form). This is why the checked spellings need no
            // rule of their own in the recursor's β.
            Term::Pair { fst, .. } | Term::PairAt { fst, .. } => Some((**fst).clone()),
            Term::VecLit { .. } => vec_lit_proj(pair, false),
            Term::VecItems { .. } => vec_items_proj(pair, false),
            _ => step_scrut(pair, gamma, defs, frames).map(|p| Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(fst_ty),
                snd_ty: Rc::clone(snd_ty),
                pair: Rc::new(p),
            }),
        },
        // fst@ / snd@ (extension; docs/intro-by-type-design.md). β as above,
        // on either pair spelling; otherwise step the pair, then the
        // annotation. Stepping `T` is what eventually exposes its former and
        // it is the only thing these arms use it for — nothing here spells
        // the components, so this arm is linear in `T` and not in its reduct.
        Term::FstAt { pair } | Term::SndAt { pair } => {
            let second = matches!(t, Term::SndAt { .. });
            let rebuild = |pair: Rc<Term>| {
                if second { Term::SndAt { pair } } else { Term::FstAt { pair } }
            };
            match &**pair {
                Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                    Some((**(if second { snd } else { fst })).clone())
                }
                Term::VecLit { .. } => vec_lit_proj(pair, second),
                Term::VecItems { .. } => vec_items_proj(pair, second),
                // The checked projections carry no annotation at all (design
                // §2.1), so there is nothing here but the receiver: a
                // projection on a neutral pair is neutral, and exposing the
                // Σ is the *typing* rule's business (`Tc::view`), not
                // reduction's.
                _ => step_scrut(pair, gamma, defs, frames).map(|p| rebuild(Rc::new(p))),
            }
        }
        // elim_Empty has no β rule (Empty has no constructors); it only ever
        // steps its scrutinee, staying neutral when the scrutinee is.
        Term::ElimEmpty { level, scrut_level, motive, scrut } => {
            step_scrut(scrut, gamma, defs, frames).map(|s| Term::ElimEmpty {
                level: level.clone(),
                scrut_level: scrut_level.clone(),
                motive: Rc::clone(motive),
                scrut: Rc::new(s),
            })
        }
        // elim_sEmpty likewise (extension; docs/sprop-design.md §5.1).
        Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
            step_term_in(scrut, gamma, defs, frames).map(|s| Term::ElimSEmpty {
                level: level.clone(),
                scrut_level: scrut_level.clone(),
                motive: Rc::clone(motive),
                scrut: Rc::new(s),
            })
        }
        Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
            match &**scrut {
                Term::Squash { tm, .. } => {
                    let delta = LocalSubst::id(gamma).extended(Rc::clone(tm));
                    Some(case.apply_local(&delta))
                }
                _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::ElimSquash {
                    src_level: src_level.clone(),
                    dst_level: dst_level.clone(),
                    src_ty: Rc::clone(src_ty),
                    motive: Rc::clone(motive),
                    case: Rc::clone(case),
                    scrut: Rc::new(s),
                }),
            }
        }
        // case (inl a) ⇝ c_l[a/x]; case (inr b) ⇝ c_r[b/y]; else reduce the
        // scrutinee, staying neutral when it is.   (extension)
        Term::Case {
            lhs_level,
            rhs_level,
            motive_level,
            lhs,
            rhs,
            motive,
            case_l,
            case_r,
            scrut,
        } => match &**scrut {
            // As for the projections: `case` fires on either injection
            // spelling and reads neither's annotation.
            Term::Inl { val, .. } | Term::InlAt { val, .. } => {
                Some(case_l.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(val))))
            }
            Term::Inr { val, .. } | Term::InrAt { val, .. } => {
                Some(case_r.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(val))))
            }
            _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::Case {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                motive_level: motive_level.clone(),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
                motive: Rc::clone(motive),
                case_l: Rc::clone(case_l),
                case_r: Rc::clone(case_r),
                scrut: Rc::new(s),
            }),
        },
        // snd (pair a b) ⇝ b; else reduce the pair   (extension)
        Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => match &**pair {
            Term::Pair { snd, .. } | Term::PairAt { snd, .. } => Some((**snd).clone()),
            Term::VecLit { .. } => vec_lit_proj(pair, true),
            Term::VecItems { .. } => vec_items_proj(pair, true),
            _ => step_scrut(pair, gamma, defs, frames).map(|p| Term::Snd {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(fst_ty),
                snd_ty: Rc::clone(snd_ty),
                pair: Rc::new(p),
            }),
        },
        // elim_W (sup(…; a; f)) ⇝ s[a/a, f/f, (λy. elim_W …(f y))/ih] — the
        // ih is synthesized as a λ around the recursive call, built from the
        // *eliminator's* annotations (fires on head shape only).  (extension)
        Term::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            scrut,
        } => match &**scrut {
            Term::Sup { label, children, .. } => {
                let lmax = Level::max(shape_level.clone(), pos_level.clone());
                let w = Type::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: Rc::clone(shape),
                    pos: Rc::clone(pos),
                };
                // T[a/x], scoped in Γ — the ih λ's domain.
                let pos_at = pos.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(label)));
                // Weaken the binder-carrying annotations under the ih λ in
                // one shift (the placeholder scrutinee is closed).
                let template = Term::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: Rc::clone(shape),
                    pos: Rc::clone(pos),
                    motive: Rc::clone(motive),
                    step: Rc::clone(step),
                    scrut: Rc::new(Term::Zero),
                }
                .shift_local(1);
                let Term::ElimW { shape: s1, pos: p1, motive: m1, step: st1, .. } = template
                else {
                    unreachable!()
                };
                // f y, scoped in (Γ, y : T[a/x]).
                let f_y = Term::App {
                    fun: Rc::new(children.shift_local(1)),
                    dom_level: pos_level.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::new(pos_at.shift_local(1)),
                    cod: Rc::new(w.shift_local(2)),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let rec = Term::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: s1,
                    pos: p1,
                    motive: m1,
                    step: st1,
                    scrut: Rc::new(f_y),
                };
                let ih = Term::Lam {
                    dom_level: pos_level.clone(),
                    cod_level: motive_level.clone(),
                    dom: Rc::new(pos_at),
                    body: Rc::new(rec),
                };
                let delta = LocalSubst::id(gamma)
                    .extended(Rc::clone(label))
                    .extended(Rc::clone(children))
                    .extended(Rc::new(ih));
                Some(step.apply_local(&delta))
            }
            _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::ElimW {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                motive_level: motive_level.clone(),
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
                motive: Rc::clone(motive),
                step: Rc::clone(step),
                scrut: Rc::new(s),
            }),
        },
        // elim_Wf (sup_f(…; a; cs)) ⇝ s[a, cs, λi. elim_Wf(…; nth … cs i)].
        // Like `elim_W`'s β this synthesizes the ih *under a λ*, but over a
        // `Fin` index: the recursive call goes to `nth(Wf; n[a/x]; cs; i)`,
        // which at a literal arity reduces to a projection of `cs`.
        Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => match &**scrut {
            Term::Supf { label, children, .. } => {
                // n[a/x], scoped in Γ — the ih λ's index bound.
                let arity_at =
                    arity.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(label)));
                let wf = Type::Wf {
                    level: level.clone(),
                    shape: Rc::clone(shape),
                    arity: Rc::clone(arity),
                };
                // Weaken the binder-carrying annotations under the ih λ in
                // one shift (the placeholder scrutinee is closed).
                let template = Term::ElimWf {
                    level: level.clone(),
                    motive_level: motive_level.clone(),
                    shape: Rc::clone(shape),
                    arity: Rc::clone(arity),
                    motive: Rc::clone(motive),
                    step: Rc::clone(step),
                    scrut: Rc::new(Term::Zero),
                }
                .shift_local(1);
                let Term::ElimWf { shape: s1, arity: n1, motive: m1, step: st1, .. } = template
                else {
                    unreachable!("shifting an elim_Wf yields an elim_Wf")
                };
                // nth(Wf; n[a/x]; cs; i), scoped in (Γ, i : Fin n[a/x]).
                let child = nth(
                    level,
                    &Rc::new(wf.shift_local(1)),
                    &Rc::new(arity_at.shift_local(1)),
                    Rc::new(children.shift_local(1)),
                    Rc::new(Term::Var(LocalVar(0))),
                );
                let rec = Term::ElimWf {
                    level: level.clone(),
                    motive_level: motive_level.clone(),
                    shape: s1,
                    arity: n1,
                    motive: m1,
                    step: st1,
                    scrut: Rc::new(child),
                };
                let ih = Term::Lam {
                    dom_level: Level::Zero,
                    cod_level: motive_level.clone(),
                    dom: Rc::new(Type::Fin { len: Rc::new(arity_at) }),
                    body: Rc::new(rec),
                };
                let delta = LocalSubst::id(gamma)
                    .extended(Rc::clone(label))
                    .extended(Rc::clone(children))
                    .extended(Rc::new(ih));
                Some(step.apply_local(&delta))
            }
            _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::ElimWf {
                level: level.clone(),
                motive_level: motive_level.clone(),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
                motive: Rc::clone(motive),
                step: Rc::clone(step),
                scrut: Rc::new(s),
            }),
        },
        // elim_IWf(…; m; sup_i(…; a; cs)) ⇝ s[a, cs, iwfIH a cs] — at a
        // `sup_i` of any annotations and at any index `m`, open data included
        // (docs/iwf-former-design.md §4; heather-coq `red_elimIWf_supi`). The
        // ih is `term::iwf_ih`, shared with the value machine.
        Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => match &**scrut {
            Term::Supi { label, children, .. } => {
                let ih = iwf_ih(sig, motive_level, motive, step, label, children);
                let delta = LocalSubst::id(gamma)
                    .extended(Rc::clone(label))
                    .extended(Rc::clone(children))
                    .extended(Rc::new(ih));
                Some(step.apply_local(&delta))
            }
            _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::ElimIWf {
                sig: Rc::clone(sig),
                motive_level: motive_level.clone(),
                motive: Rc::clone(motive),
                step: Rc::clone(step),
                index: Rc::clone(index),
                scrut: Rc::new(s),
            }),
        },
        // out(…; corec^{k}(…; X; c; j; x)) ⇝ m_out_corec(…) — one step, only
        // under `out` (docs/kernel-coinduction-design.md §1.4). The reduct
        // writes `c[j, x]` twice; this rewriter duplicates it (design §7).
        Term::Out { sig, index, scrut } => match &**scrut {
            Term::Corec { sig: csig, carrier_level, carrier, step, index: cindex, seed } => {
                Some(m_out_corec(csig, carrier_level, carrier, step, cindex, seed))
            }
            _ => step_scrut(scrut, gamma, defs, frames).map(|s| Term::Out {
                sig: Rc::clone(sig),
                index: Rc::clone(index),
                scrut: Rc::new(s),
            }),
        },
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => match &**fun {
            // app(λx. t; …; s) ⇝ t[s/x]
            Term::Lam { body, .. } => {
                Some(body.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg))))
            }
            _ => step_term_in(fun, gamma, defs, frames).map(|f| Term::App {
                fun: Rc::new(f),
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
                arg: Rc::clone(arg),
            }),
        },
        // app@ (extension; docs/app-by-head-type-design.md): β reads nothing
        // from the application, so it fires as on `app`; the congruence step
        // has no annotation to carry.
        Term::AppAt { fun, arg } => match &**fun {
            Term::Lam { body, .. } => {
                Some(body.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg))))
            }
            _ => step_term_in(fun, gamma, defs, frames)
                .map(|f| Term::AppAt { fun: Rc::new(f), arg: Rc::clone(arg) }),
        },
        Term::UApp { fun, levels } => match &**fun {
            // (Λ ℓ⃗. t) $ l⃗ ⇝ t[l⃗/ℓ⃗]; the written vectors pair positionally
            // (outermost first), instantiation wants innermost-first.
            Term::ULam { num_vars, body, .. } if *num_vars as usize == levels.len() => {
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                Some(body.inst_univ(&phi))
            }
            Term::ULam { .. } => None, // arity mismatch: ill-typed, stuck
            _ => step_term_in(fun, gamma, defs, frames)
                .map(|f| Term::UApp { fun: Rc::new(f), levels: levels.clone() }),
        },
        Term::CtxApp { fun, ctx } => match &**fun {
            // (Λ g. t) @ Δ ⇝ t[Δ/g]
            Term::CtxLam { body, .. } => {
                Some(body.apply_global(&GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()))))
            }
            _ => step_term_in(fun, gamma, defs, frames)
                .map(|f| Term::CtxApp { fun: Rc::new(f), ctx: ctx.clone() }),
        },
        Term::TyApp { fun, arg } => match &**fun {
            // (Λ U. t) @ T ⇝ t[T/U]
            Term::TyLam { body, .. } => {
                Some(body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)))))
            }
            _ => step_term_in(fun, gamma, defs, frames)
                .map(|f| Term::TyApp { fun: Rc::new(f), arg: Rc::clone(arg) }),
        },
        Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
            match &**scrut {
                // letbox … (box T) ⇝ t'[T/U]
                Term::BoxTy(code) => Some(
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(code)))),
                ),
                _ => step_term_in(scrut, gamma, defs, frames).map(|s| Term::LetBoxTy {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    motive: Rc::clone(motive),
                    body: Rc::clone(body),
                    scrut: Rc::new(s),
                }),
            }
        }
        Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
            match &**scrut {
                // letbox … (box t) ⇝ t'[t/u]
                Term::BoxTm(code) => Some(
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Tm(Rc::clone(code)))),
                ),
                _ => step_term_in(scrut, gamma, defs, frames).map(|s| Term::LetBoxTm {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    ty: Rc::clone(ty),
                    motive: Rc::clone(motive),
                    body: Rc::clone(body),
                    scrut: Rc::new(s),
                }),
            }
        }
        Term::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            scrut,
        } => {
            let rec = Rec { ty_motive_level, tm_motive_level, motives, branches };
            match &**scrut {
                Term::BoxTy(code) => beta_elim_ty(&rec, ctx, code, gamma),
                _ => step_term_in(scrut, gamma, defs, frames).map(|s| Term::ElimCodeTy {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives: Rc::clone(motives),
                    branches: Rc::clone(branches),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    scrut: Rc::new(s),
                }),
            }
        }
        Term::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ty,
            scrut,
        } => {
            // Fixed order: the type annotation (scoped in Δ, not Γ) reduces
            // to weak head normal form first, then the scrutinee.
            if let Some(ty) = step_type_in(ty, ctx, defs, frames) {
                return Some(Term::ElimCodeTm {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives: Rc::clone(motives),
                    branches: Rc::clone(branches),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    ty: Rc::new(ty),
                    scrut: Rc::clone(scrut),
                });
            }
            let rec = Rec { ty_motive_level, tm_motive_level, motives, branches };
            match &**scrut {
                Term::BoxTm(code) => beta_elim_tm(&rec, ctx, ty, code_level, code, gamma),
                _ => step_term_in(scrut, gamma, defs, frames).map(|s| Term::ElimCodeTm {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives: Rc::clone(motives),
                    branches: Rc::clone(branches),
                    code_level: code_level.clone(),
                    ctx: ctx.clone(),
                    ty: Rc::clone(ty),
                    scrut: Rc::new(s),
                }),
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Recursor β
// ---------------------------------------------------------------------------

use crate::term::{Branches, Motives};

/// The parts of a recursor that are copied verbatim into its recursive
/// calls.
pub(crate) struct Rec<'a> {
    ty_motive_level: &'a Level,
    tm_motive_level: &'a Level,
    motives: &'a Rc<Motives>,
    branches: &'a Rc<Branches>,
}

impl<'a> Rec<'a> {
    /// The recursor's copied-forward parts, for [`crate::eval`]'s β: the
    /// evaluator shares these functions rather than transcribing the 65
    /// branch telescopes a sixth time (docs/nbe-conversion-design.md §2).
    pub(crate) fn new(
        ty_motive_level: &'a Level,
        tm_motive_level: &'a Level,
        motives: &'a Rc<Motives>,
        branches: &'a Rc<Branches>,
    ) -> Rec<'a> {
        Rec { ty_motive_level, tm_motive_level, motives, branches }
    }
}

impl Rec<'_> {
    /// Recursive call `elim^Typ … (code_level, ctx) (box code)`.
    fn elim_ty(&self, code_level: Level, ctx: LocalCtx, code: Rc<Type>) -> Rc<Term> {
        Rc::new(Term::ElimCodeTy {
            ty_motive_level: self.ty_motive_level.clone(),
            tm_motive_level: self.tm_motive_level.clone(),
            motives: Rc::clone(self.motives),
            branches: Rc::clone(self.branches),
            code_level,
            ctx,
            scrut: Rc::new(Term::BoxTy(code)),
        })
    }

    /// Recursive call `elim^Trm … (code_level, ctx, ty) (box code)`.
    fn elim_tm(&self, code_level: Level, ctx: LocalCtx, ty: Rc<Type>, code: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::ElimCodeTm {
            ty_motive_level: self.ty_motive_level.clone(),
            tm_motive_level: self.tm_motive_level.clone(),
            motives: Rc::clone(self.motives),
            branches: Rc::clone(self.branches),
            code_level,
            ctx,
            ty,
            scrut: Rc::new(Term::BoxTm(code)),
        })
    }
}

/// `Δ, x : ty @ level`.
fn extend(delta: &LocalCtx, ty: Rc<Type>, level: Level) -> LocalCtx {
    let mut c = delta.clone();
    c.entries.push(CtxEntry { ty, level });
    c
}

/// Instantiate a branch under its telescope (see [`Branches`] for the
/// telescopes): universe payloads `phi` (innermost-first), global payloads
/// (outermost-first), and recursive-call payloads (outermost-first) spliced
/// onto `id_Γ`.
fn fire(
    branch: &Rc<Term>,
    phi: &[Level],
    globals: Vec<GlobalEntry>,
    locals: Vec<Rc<Term>>,
    gamma: &LocalCtx,
) -> Term {
    let t = branch.inst_univ(phi);
    let t = t.apply_global(&GlobalSubst { entries: globals });
    if locals.is_empty() {
        return t;
    }
    let mut delta = LocalSubst::id(gamma);
    for payload in locals {
        delta = delta.extended(payload);
    }
    t.apply_local(&delta)
}

/// The signature pieces of an `M` branch, `U_I, U_S, U_P, u_o` as global
/// payloads and `x_I, x_S, x_P, x_o` as recursive calls, each at the
/// context its piece lives in (docs/kernel-m-codes-design.md §2). The
/// pieces are the *types* of a boxed `M`/`corec`/`out`; [`tm_m_pieces`] is
/// the code former's.
fn m_sig_pieces(rec: &Rec, delta: &LocalCtx, sig: &MSig) -> (Vec<GlobalEntry>, Vec<Rc<Term>>) {
    let di = extend(delta, Rc::clone(&sig.idx), sig.idx_level.clone());
    let dis = extend(&di, Rc::clone(&sig.shape), sig.level.clone());
    let disp = extend(&dis, Rc::clone(&sig.pos), sig.pos_level.clone());
    let s_idx = rec.elim_ty(sig.idx_level.clone(), delta.clone(), Rc::clone(&sig.idx));
    let s_shape = rec.elim_ty(sig.level.clone(), di, Rc::clone(&sig.shape));
    let s_pos = rec.elim_ty(sig.pos_level.clone(), dis, Rc::clone(&sig.pos));
    let s_next = rec.elim_tm(
        sig.idx_level.clone(),
        disp,
        Rc::new(sig.idx.shift_local(3)),
        Rc::clone(&sig.next),
    );
    (
        vec![
            GlobalEntry::Ctx(delta.clone()),
            GlobalEntry::Ty(Rc::clone(&sig.idx)),
            GlobalEntry::Ty(Rc::clone(&sig.shape)),
            GlobalEntry::Ty(Rc::clone(&sig.pos)),
            GlobalEntry::Tm(Rc::clone(&sig.next)),
        ],
        vec![s_idx, s_shape, s_pos, s_next],
    )
}

/// The signature pieces of an `IWf` branch, `U_I, U_S, u_n, u_o, u_c` as
/// global payloads and `x_I, x_S, x_n, x_o, x_c` as recursive calls, each at
/// the context its piece lives in (docs/iwf-former-design.md §6). The pieces
/// are a boxed `IWf`/`sup_i`/`elim_IWf`'s; `TmIWf`'s are codes and are
/// recursed at `Ty`.
fn iwf_sig_pieces(rec: &Rec, delta: &LocalCtx, sig: &IWfSig) -> (Vec<GlobalEntry>, Vec<Rc<Term>>) {
    let dx = extend(delta, Rc::clone(&sig.shape), sig.level.clone());
    let dxi = extend(&dx, Rc::new(Type::Fin { len: Rc::clone(&sig.arity) }), Level::Zero);
    let s_idx = rec.elim_ty(sig.idx_level.clone(), delta.clone(), Rc::clone(&sig.idx));
    let s_shape = rec.elim_ty(sig.level.clone(), delta.clone(), Rc::clone(&sig.shape));
    let s_arity = rec.elim_tm(Level::Zero, dx.clone(), Rc::new(Type::Nat), Rc::clone(&sig.arity));
    let s_out = rec.elim_tm(sig.idx_level.clone(), dx, Rc::new(sig.idx.shift_local(1)), Rc::clone(&sig.out));
    let s_child = rec.elim_tm(sig.idx_level.clone(), dxi, Rc::new(sig.idx.shift_local(2)), Rc::clone(&sig.child));
    (
        vec![
            GlobalEntry::Ctx(delta.clone()),
            GlobalEntry::Ty(Rc::clone(&sig.idx)),
            GlobalEntry::Ty(Rc::clone(&sig.shape)),
            GlobalEntry::Tm(Rc::clone(&sig.arity)),
            GlobalEntry::Tm(Rc::clone(&sig.out)),
            GlobalEntry::Tm(Rc::clone(&sig.child)),
        ],
        vec![s_idx, s_shape, s_arity, s_out, s_child],
    )
}

/// `IWf`'s universe payload, innermost-first: `li, l`.
fn iwf_univs(sig: &IWfSig) -> Vec<Level> {
    vec![sig.idx_level.clone(), sig.level.clone()]
}

/// `M`'s universe payload, innermost-first: `li, l', l`.
fn m_univs(sig: &MSig) -> Vec<Level> {
    vec![sig.idx_level.clone(), sig.pos_level.clone(), sig.level.clone()]
}

/// β for `elim^Typ … (l', Δ) (box code)`, dispatching on the head of the
/// code. `None` blocks on `U^δ` (neutral) and on layer-m heads that cannot
/// be code (ill-typed, stuck).
pub(crate) fn beta_elim_ty(
    rec: &Rec,
    delta: &LocalCtx,
    code: &Rc<Type>,
    gamma: &LocalCtx,
) -> Option<Term> {
    let b = &**rec.branches;
    match &**code {
        // (g. t_Nat)
        Type::Nat => Some(fire(
            &b.ty_nat,
            &[],
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, g. t_Ty)
        Type::Ty(l) => Some(fire(
            &b.ty_ty,
            std::slice::from_ref(l),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Π)
        Type::Pi { dom_level, cod_level, dom, cod } => {
            let dx = extend(delta, Rc::clone(dom), dom_level.clone());
            let s_dom = rec.elim_ty(dom_level.clone(), delta.clone(), Rc::clone(dom));
            let s_cod = rec.elim_ty(cod_level.clone(), dx, Rc::clone(cod));
            Some(fire(
                &b.ty_pi,
                &[cod_level.clone(), dom_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(dom)),
                    GlobalEntry::Ty(Rc::clone(cod)),
                ],
                vec![s_dom, s_cod],
                gamma,
            ))
        }
        // (ℓ, g, u_t, x_t. t_El) — x_t recurses at the *term* motive.
        Type::El { level, tm } => {
            let s_tm = rec.elim_tm(
                Level::succ(level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(level.clone())),
                Rc::clone(tm),
            );
            Some(fire(
                &b.ty_el,
                std::slice::from_ref(level),
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(tm))],
                vec![s_tm],
                gamma,
            ))
        }
        // (ℓ, g, U_S, u_t, u_u, x_S, x_t, x_u. t_Id)   (extension)
        Type::Id { level, ty, lhs, rhs } => {
            let s_ty = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(ty));
            let s_lhs =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(lhs));
            let s_rhs =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(rhs));
            Some(fire(
                &b.ty_id,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                ],
                vec![s_ty, s_lhs, s_rhs],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Σ)   (extension)
        Type::Sigma { fst_level, snd_level, fst, snd } => {
            let dx = extend(delta, Rc::clone(fst), fst_level.clone());
            let s_fst = rec.elim_ty(fst_level.clone(), delta.clone(), Rc::clone(fst));
            let s_snd = rec.elim_ty(snd_level.clone(), dx, Rc::clone(snd));
            Some(fire(
                &b.ty_sigma,
                &[snd_level.clone(), fst_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(fst)),
                    GlobalEntry::Ty(Rc::clone(snd)),
                ],
                vec![s_fst, s_snd],
                gamma,
            ))
        }
        // (ℓ, g. t_Unit), (ℓ, g. t_Empty)   (extension)
        Type::Unit { level } => Some(fire(
            &b.ty_unit,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        Type::Empty { level } => Some(fire(
            &b.ty_empty,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, ℓ', g, U_A, U_B, x_A, x_B. t_+) — both summands in g (non-
        // dependent); mirrors ty_sigma minus the binder extension.   (extension)
        Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
            let s_lhs = rec.elim_ty(lhs_level.clone(), delta.clone(), Rc::clone(lhs));
            let s_rhs = rec.elim_ty(rhs_level.clone(), delta.clone(), Rc::clone(rhs));
            Some(fire(
                &b.ty_sum,
                &[rhs_level.clone(), lhs_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(lhs)),
                    GlobalEntry::Ty(Rc::clone(rhs)),
                ],
                vec![s_lhs, s_rhs],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_W) — mirrors ty_pi/ty_sigma.
        // (extension)
        Type::W { shape_level, pos_level, shape, pos } => {
            let dx = extend(delta, Rc::clone(shape), shape_level.clone());
            let s_shape = rec.elim_ty(shape_level.clone(), delta.clone(), Rc::clone(shape));
            let s_pos = rec.elim_ty(pos_level.clone(), dx, Rc::clone(pos));
            Some(fire(
                &b.ty_w,
                &[pos_level.clone(), shape_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(shape)),
                    GlobalEntry::Ty(Rc::clone(pos)),
                ],
                vec![s_shape, s_pos],
                gamma,
            ))
        }
        // (ℓ, g, U_T, u_k, x_T, x_k. t_Vec) — x_k recurses at the *term*
        // motive: the length is a term of Δ, not a type.   (extension, §6)
        Type::Vec { level, elem, len } => {
            let s_elem = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(elem));
            let s_len = rec.elim_tm(
                Level::Zero,
                delta.clone(),
                Rc::new(Type::Nat),
                Rc::clone(len),
            );
            Some(fire(
                &b.ty_vec,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(elem)),
                    GlobalEntry::Tm(Rc::clone(len)),
                ],
                vec![s_elem, s_len],
                gamma,
            ))
        }
        // (g, u_k, x_k. t_Fin) — no universe payload; `Fin` lives at 0.
        Type::Fin { len } => {
            let s_len = rec.elim_tm(
                Level::Zero,
                delta.clone(),
                Rc::new(Type::Nat),
                Rc::clone(len),
            );
            Some(fire(
                &b.ty_fin,
                &[],
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(len))],
                vec![s_len],
                gamma,
            ))
        }
        // (ℓ, g, U_S, u_n, x_S, x_n. t_Wf) — mirrors ty_w, but the arity is
        // a Nat *term* under the shape binder.   (extension, §6)
        Type::Wf { level, shape, arity } => {
            let dx = extend(delta, Rc::clone(shape), level.clone());
            let s_shape = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(shape));
            let s_arity =
                rec.elim_tm(Level::Zero, dx, Rc::new(Type::Nat), Rc::clone(arity));
            Some(fire(
                &b.ty_wf,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(shape)),
                    GlobalEntry::Tm(Rc::clone(arity)),
                ],
                vec![s_shape, s_arity],
                gamma,
            ))
        }
        // box (U^δ): blocked, neutral.
        Type::GlobalTy { .. } => None,
        // (ℓ, g, U_S, u_t, u_u, x_S, x_t, x_u. t_sEq) — mirrors ty_id.
        // (extension; docs/sprop-design.md §6)
        Type::SEq { level, ty, lhs, rhs } => {
            let s_ty = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(ty));
            let s_lhs =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(lhs));
            let s_rhs =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(rhs));
            Some(fire(
                &b.ty_seq,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                ],
                vec![s_ty, s_lhs, s_rhs],
                gamma,
            ))
        }
        // (ℓ, g. t_sEmpty) — mirrors ty_empty.   (extension)
        Type::SEmpty { level } => Some(fire(
            &b.ty_sempty,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        Type::Squash { level, ty } => {
            let s_ty = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(ty));
            Some(fire(
                &b.ty_squash,
                std::slice::from_ref(level),
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Ty(Rc::clone(ty))],
                vec![s_ty],
                gamma,
            ))
        }
        // (l, l', li, g, U_I, U_S, U_P, u_o, u_j, x_I, x_S, x_P, x_o, x_j.
        // t_M)   (docs/kernel-m-codes-design.md §2)
        Type::M { sig, index } => {
            let (mut globals, mut locals) = m_sig_pieces(rec, delta, sig);
            globals.push(GlobalEntry::Tm(Rc::clone(index)));
            locals.push(rec.elim_tm(
                sig.idx_level.clone(),
                delta.clone(),
                Rc::clone(&sig.idx),
                Rc::clone(index),
            ));
            Some(fire(&b.ty_m, &m_univs(sig), globals, locals, gamma))
        }
        // (ℓ, g, u_n, U_F, x_n, x_F. t_DVec) — the length at the *term*
        // motive, the family under `i : Fin u_n`.   (docs/iwf-former-design.md §6)
        Type::DVec { level, len, fam } => {
            let di = extend(delta, Rc::new(Type::Fin { len: Rc::clone(len) }), Level::Zero);
            let s_len = rec.elim_tm(Level::Zero, delta.clone(), Rc::new(Type::Nat), Rc::clone(len));
            let s_fam = rec.elim_ty(level.clone(), di, Rc::clone(fam));
            Some(fire(
                &b.ty_dvec,
                std::slice::from_ref(level),
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(len)), GlobalEntry::Ty(Rc::clone(fam))],
                vec![s_len, s_fam],
                gamma,
            ))
        }
        // (ℓ, ℓi, g, U_I, U_S, u_n, u_o, u_c, u_m, x_I, …, x_c, x_m. t_IWf)
        //   (design §6)
        Type::IWf { sig, index } => {
            let (mut globals, mut locals) = iwf_sig_pieces(rec, delta, sig);
            globals.push(GlobalEntry::Tm(Rc::clone(index)));
            locals.push(rec.elim_tm(sig.idx_level.clone(), delta.clone(), Rc::clone(&sig.idx), Rc::clone(index)));
            Some(fire(&b.ty_iwf, &iwf_univs(sig), globals, locals, gamma))
        }
        // Layer-m types cannot be layer-c code: ill-typed, stuck.
        _ => None,
    }
}

/// β for `elim^Trm … (l', Δ, T) (box code)`, dispatching on the head of the
/// code; `ann_ty` is the recursor's type annotation, already in WHNF (the
/// `λ` case reads its return type off it). `None` blocks on `u^δ` (neutral)
/// and on layer-m heads that cannot be code (ill-typed, stuck).
pub(crate) fn beta_elim_tm(
    rec: &Rec,
    delta: &LocalCtx,
    ann_ty: &Rc<Type>,
    code_level: &Level,
    code: &Rc<Term>,
    gamma: &LocalCtx,
) -> Option<Term> {
    let b = &**rec.branches;
    match &**code {
        // (ℓ, g, U_T, u_x. t_x) — u_x is layer v: only the variable fits.
        Term::Var(x) => Some(fire(
            &b.tm_var,
            std::slice::from_ref(code_level),
            vec![
                GlobalEntry::Ctx(delta.clone()),
                GlobalEntry::Ty(Rc::clone(ann_ty)),
                GlobalEntry::Tm(Rc::new(Term::Var(*x))),
            ],
            vec![],
            gamma,
        )),
        // (g. t'_Nat)
        Term::TmNat => Some(fire(
            &b.tm_nat,
            &[],
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, g. t'_Ty)
        Term::TmTy(l) => Some(fire(
            &b.tm_ty,
            std::slice::from_ref(l),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_Π) — the codomain code is
        // scoped in (Δ, x : El u_s @ ℓ).
        Term::TmPi { dom_level, cod_level, dom, cod } => {
            let s_dom = rec.elim_tm(
                Level::succ(dom_level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(dom_level.clone())),
                Rc::clone(dom),
            );
            let dx = extend(
                delta,
                Rc::new(Type::El { level: dom_level.clone(), tm: Rc::clone(dom) }),
                dom_level.clone(),
            );
            let s_cod = rec.elim_tm(
                Level::succ(cod_level.clone()),
                dx,
                Rc::new(Type::Ty(cod_level.clone())),
                Rc::clone(cod),
            );
            Some(fire(
                &b.tm_pi,
                &[cod_level.clone(), dom_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(dom)),
                    GlobalEntry::Tm(Rc::clone(cod)),
                ],
                vec![s_dom, s_cod],
                gamma,
            ))
        }
        // (g. t_ze)
        t if crate::term::is_nat_zero(t) => Some(fire(
            &b.tm_zero,
            &[],
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (g, u_t, x_t. t_succ)
        Term::Succ(pred) => {
            let s_pred = rec.elim_tm(
                Level::Zero,
                delta.clone(),
                Rc::new(Type::Nat),
                Rc::clone(pred),
            );
            Some(fire(
                &b.tm_succ,
                &[],
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(pred))],
                vec![s_pred],
                gamma,
            ))
        }
        Term::NatLit(n) => {
            let pred = Rc::new(crate::term::nat_lit_pred(n));
            let s_pred = rec.elim_tm(
                Level::Zero,
                delta.clone(),
                Rc::new(Type::Nat),
                Rc::clone(&pred),
            );
            Some(fire(
                &b.tm_succ,
                &[],
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(pred)],
                vec![s_pred],
                gamma,
            ))
        }
        // (ℓ, g, U_M, u_s, u_s', u_t, x_M, x_s, x_s', x_t. t_elimN) —
        // x_M recurses at the *type* motive; the branch-annotation types of
        // x_s / x_s' instantiate the motive at ze / su x.
        Term::ElimNat { level, motive, base, step, scrut } => {
            let dx_nat = extend(delta, Rc::new(Type::Nat), Level::Zero);
            let s_motive = rec.elim_ty(level.clone(), dx_nat.clone(), Rc::clone(motive));
            let ty_base =
                motive.apply_local(&LocalSubst::id(delta).extended(Rc::new(Term::Zero)));
            let s_base =
                rec.elim_tm(level.clone(), delta.clone(), Rc::new(ty_base), Rc::clone(base));
            let dxy = extend(&dx_nat, Rc::clone(motive), level.clone());
            // M[id_Δ, su x/x] scoped in (Δ, x : Nat, y : M): weaken id_Δ
            // under the two binders, then send x ↦ su x.
            let su_x = Term::Succ(Rc::new(Term::Var(crate::term::LocalVar(1))));
            let ty_step = motive
                .apply_local(&LocalSubst::id(delta).shift_local(2).extended(Rc::new(su_x)));
            let s_step = rec.elim_tm(level.clone(), dxy, Rc::new(ty_step), Rc::clone(step));
            let s_scrut =
                rec.elim_tm(Level::Zero, delta.clone(), Rc::new(Type::Nat), Rc::clone(scrut));
            Some(fire(
                &b.tm_elim_nat,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(base)),
                    GlobalEntry::Tm(Rc::clone(step)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_motive, s_base, s_step, s_scrut],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, u_t, x_S, x_t. t_λ) — U_T (the return type,
        // layer p, no recursive call) comes off the WHNF `Π` annotation;
        // the λ syntax does not carry it.
        Term::Lam { dom_level, cod_level, dom, body } => {
            let Type::Pi { cod, .. } = &**ann_ty else {
                return None; // annotation not a Π: ill-typed, stuck
            };
            let s_dom = rec.elim_ty(dom_level.clone(), delta.clone(), Rc::clone(dom));
            let dx = extend(delta, Rc::clone(dom), dom_level.clone());
            let s_body = rec.elim_tm(cod_level.clone(), dx, Rc::clone(cod), Rc::clone(body));
            Some(fire(
                &b.tm_lam,
                &[cod_level.clone(), dom_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(dom)),
                    GlobalEntry::Ty(Rc::clone(cod)),
                    GlobalEntry::Tm(Rc::clone(body)),
                ],
                vec![s_dom, s_body],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, u_t, u_s, x_S, x_T, x_t, x_s. t_app) — the
        // annotations S and T are sub-structures precisely so these
        // recursive calls can be formed.
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
            let s_dom = rec.elim_ty(dom_level.clone(), delta.clone(), Rc::clone(dom));
            let dx = extend(delta, Rc::clone(dom), dom_level.clone());
            let s_cod = rec.elim_ty(cod_level.clone(), dx, Rc::clone(cod));
            let pi = Rc::new(Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
            });
            let s_fun = rec.elim_tm(
                Level::max(dom_level.clone(), cod_level.clone()),
                delta.clone(),
                pi,
                Rc::clone(fun),
            );
            let s_arg =
                rec.elim_tm(dom_level.clone(), delta.clone(), Rc::clone(dom), Rc::clone(arg));
            Some(fire(
                &b.tm_app,
                &[cod_level.clone(), dom_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(dom)),
                    GlobalEntry::Ty(Rc::clone(cod)),
                    GlobalEntry::Tm(Rc::clone(fun)),
                    GlobalEntry::Tm(Rc::clone(arg)),
                ],
                vec![s_dom, s_cod, s_fun, s_arg],
                gamma,
            ))
        }
        // (ℓ, g, u_S, u_t, u_u, x_S, x_t, x_u. t'_Id) — the encoding; both
        // endpoints are scoped in Δ at El u_S.   (extension)
        Term::TmId { level, ty, lhs, rhs } => {
            let s_ty = rec.elim_tm(
                Level::succ(level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(level.clone())),
                Rc::clone(ty),
            );
            let el = Rc::new(Type::El { level: level.clone(), tm: Rc::clone(ty) });
            let s_lhs =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(&el), Rc::clone(lhs));
            let s_rhs = rec.elim_tm(level.clone(), delta.clone(), el, Rc::clone(rhs));
            Some(fire(
                &b.tm_id,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                ],
                vec![s_ty, s_lhs, s_rhs],
                gamma,
            ))
        }
        // (ℓ, g, U_S, u_t, x_S, x_t. t_refl)   (extension)
        Term::Refl { level, ty, tm } => {
            let s_ty = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(ty));
            let s_tm =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(tm));
            Some(fire(
                &b.tm_refl,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(tm)),
                ],
                vec![s_ty, s_tm],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, u_a, U_M, u_c, u_r, u_e, x_S, x_a, x_M, x_c, x_r,
        // x_e. t_J) — the motive code is scoped in
        // (Δ, y : S @ ℓ, p : Id^ℓ(S; a; y) @ ℓ); the case's annotation type
        // instantiates the motive at (a, refl).   (extension)
        Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
            let s_ty = rec.elim_ty(ty_level.clone(), delta.clone(), Rc::clone(ty));
            let s_lhs =
                rec.elim_tm(ty_level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(lhs));
            let dy = extend(delta, Rc::clone(ty), ty_level.clone());
            let p_ty = Type::Id {
                level: ty_level.clone(),
                ty: Rc::new(ty.shift_local(1)),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(Term::Var(crate::term::LocalVar(0))),
            };
            let dyp = extend(&dy, Rc::new(p_ty), ty_level.clone());
            let s_motive = rec.elim_ty(motive_level.clone(), dyp, Rc::clone(motive));
            let refl_a = Term::Refl {
                level: ty_level.clone(),
                ty: Rc::clone(ty),
                tm: Rc::clone(lhs),
            };
            let ty_case = motive.apply_local(
                &LocalSubst::id(delta).extended(Rc::clone(lhs)).extended(Rc::new(refl_a)),
            );
            let s_case = rec.elim_tm(
                motive_level.clone(),
                delta.clone(),
                Rc::new(ty_case),
                Rc::clone(case),
            );
            let s_rhs =
                rec.elim_tm(ty_level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(rhs));
            let id_ty = Rc::new(Type::Id {
                level: ty_level.clone(),
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            });
            let s_proof =
                rec.elim_tm(ty_level.clone(), delta.clone(), id_ty, Rc::clone(proof));
            Some(fire(
                &b.tm_j,
                &[motive_level.clone(), ty_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(case)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                    GlobalEntry::Tm(Rc::clone(proof)),
                ],
                vec![s_ty, s_lhs, s_motive, s_case, s_rhs, s_proof],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_Σ) — the encoding; mirrors
        // tm_pi.   (extension)
        Term::TmSigma { fst_level, snd_level, fst, snd } => {
            let s_fst = rec.elim_tm(
                Level::succ(fst_level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(fst_level.clone())),
                Rc::clone(fst),
            );
            let dx = extend(
                delta,
                Rc::new(Type::El { level: fst_level.clone(), tm: Rc::clone(fst) }),
                fst_level.clone(),
            );
            let s_snd = rec.elim_tm(
                Level::succ(snd_level.clone()),
                dx,
                Rc::new(Type::Ty(snd_level.clone())),
                Rc::clone(snd),
            );
            Some(fire(
                &b.tm_sigma,
                &[snd_level.clone(), fst_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(fst)),
                    GlobalEntry::Tm(Rc::clone(snd)),
                ],
                vec![s_fst, s_snd],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, u_a, u_b, x_S, x_T, x_a, x_b. t_pair) — both
        // type annotations are sub-structures (like app).   (extension)
        Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => {
            let s_fst_ty = rec.elim_ty(fst_level.clone(), delta.clone(), Rc::clone(fst_ty));
            let dx = extend(delta, Rc::clone(fst_ty), fst_level.clone());
            let s_snd_ty = rec.elim_ty(snd_level.clone(), dx, Rc::clone(snd_ty));
            let s_fst =
                rec.elim_tm(fst_level.clone(), delta.clone(), Rc::clone(fst_ty), Rc::clone(fst));
            // b : T[a/x].
            let snd_at =
                snd_ty.apply_local(&LocalSubst::id(delta).extended(Rc::clone(fst)));
            let s_snd =
                rec.elim_tm(snd_level.clone(), delta.clone(), Rc::new(snd_at), Rc::clone(snd));
            Some(fire(
                &b.tm_pair,
                &[snd_level.clone(), fst_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(fst_ty)),
                    GlobalEntry::Ty(Rc::clone(snd_ty)),
                    GlobalEntry::Tm(Rc::clone(fst)),
                    GlobalEntry::Tm(Rc::clone(snd)),
                ],
                vec![s_fst_ty, s_snd_ty, s_fst, s_snd],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_fst)   (extension)
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
            let s_fst_ty = rec.elim_ty(fst_level.clone(), delta.clone(), Rc::clone(fst_ty));
            let dx = extend(delta, Rc::clone(fst_ty), fst_level.clone());
            let s_snd_ty = rec.elim_ty(snd_level.clone(), dx, Rc::clone(snd_ty));
            let sigma = Rc::new(Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: Rc::clone(fst_ty),
                snd: Rc::clone(snd_ty),
            });
            let s_pair = rec.elim_tm(
                Level::max(fst_level.clone(), snd_level.clone()),
                delta.clone(),
                sigma,
                Rc::clone(pair),
            );
            Some(fire(
                &b.tm_fst,
                &[snd_level.clone(), fst_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(fst_ty)),
                    GlobalEntry::Ty(Rc::clone(snd_ty)),
                    GlobalEntry::Tm(Rc::clone(pair)),
                ],
                vec![s_fst_ty, s_snd_ty, s_pair],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_snd)   (extension)
        Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
            let s_fst_ty = rec.elim_ty(fst_level.clone(), delta.clone(), Rc::clone(fst_ty));
            let dx = extend(delta, Rc::clone(fst_ty), fst_level.clone());
            let s_snd_ty = rec.elim_ty(snd_level.clone(), dx, Rc::clone(snd_ty));
            let sigma = Rc::new(Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: Rc::clone(fst_ty),
                snd: Rc::clone(snd_ty),
            });
            let s_pair = rec.elim_tm(
                Level::max(fst_level.clone(), snd_level.clone()),
                delta.clone(),
                sigma,
                Rc::clone(pair),
            );
            Some(fire(
                &b.tm_snd,
                &[snd_level.clone(), fst_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(fst_ty)),
                    GlobalEntry::Ty(Rc::clone(snd_ty)),
                    GlobalEntry::Tm(Rc::clone(pair)),
                ],
                vec![s_fst_ty, s_snd_ty, s_pair],
                gamma,
            ))
        }
        // (g. t'_Unit), (g. t'_Empty) — the encodings.   (extension)
        Term::TmUnit { level } => Some(fire(
            &b.tm_unit,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        Term::TmEmpty { level } => Some(fire(
            &b.tm_empty,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (g. t_triv)   (extension)
        Term::Triv { level } => Some(fire(
            &b.tm_triv,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, g, U_M, u_t, x_M, x_t. t_elimE) — x_M recurses at the *type*
        // motive; mirrors tm_elim_nat minus the base/step branches.   (extension)
        // (ℓ, ℓ', g, U_M, u_t, x_M, x_t. t_elimE) — ℓ the motive's, ℓ' the
        // scrutinee's `Empty` level. Two universes as of
        // docs/unit-empty-level-indexing.md §3.
        Term::ElimEmpty { level, scrut_level, motive, scrut } => {
            let empty = || Rc::new(Type::Empty { level: scrut_level.clone() });
            let dx_empty = extend(delta, empty(), scrut_level.clone());
            let s_motive = rec.elim_ty(level.clone(), dx_empty, Rc::clone(motive));
            let s_scrut =
                rec.elim_tm(scrut_level.clone(), delta.clone(), empty(), Rc::clone(scrut));
            Some(fire(
                &b.tm_elim_empty,
                // innermost-first: ℓ' (scrutinee) then ℓ (motive)
                &[scrut_level.clone(), level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_motive, s_scrut],
                gamma,
            ))
        }
        // -- strict equality (extension; docs/sprop-design.md §6) ----------
        // (ℓ, g, u_S, u_t, u_u, x_S, x_t, x_u. t'_sEq) — mirrors tm_id.
        Term::TmSEq { level, ty, lhs, rhs } => {
            let s_ty = rec.elim_tm(
                Level::succ(level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(level.clone())),
                Rc::clone(ty),
            );
            let el = Rc::new(Type::El { level: level.clone(), tm: Rc::clone(ty) });
            let s_lhs =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(&el), Rc::clone(lhs));
            let s_rhs = rec.elim_tm(level.clone(), delta.clone(), el, Rc::clone(rhs));
            Some(fire(
                &b.tm_seq,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                ],
                vec![s_ty, s_lhs, s_rhs],
                gamma,
            ))
        }
        // (ℓ, g. t'_sEmpty) — mirrors tm_empty.
        Term::TmSEmpty { level } => Some(fire(
            &b.tm_sempty,
            std::slice::from_ref(level),
            vec![GlobalEntry::Ctx(delta.clone())],
            vec![],
            gamma,
        )),
        // (ℓ, g, U_S, u_t, x_S, x_t. t_srefl) — mirrors tm_refl.
        Term::SRefl { level, ty, tm } => {
            let s_ty = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(ty));
            let s_tm =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(tm));
            Some(fire(
                &b.tm_srefl,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(tm)),
                ],
                vec![s_ty, s_tm],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_M, u_t, x_M, x_t. t_elim_sE) — mirrors tm_elim_empty.
        Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
            let sempty = || Rc::new(Type::SEmpty { level: scrut_level.clone() });
            let dx_sempty = extend(delta, sempty(), scrut_level.clone());
            let s_motive = rec.elim_ty(level.clone(), dx_sempty, Rc::clone(motive));
            let s_scrut =
                rec.elim_tm(scrut_level.clone(), delta.clone(), sempty(), Rc::clone(scrut));
            Some(fire(
                &b.tm_elim_sempty,
                // innermost-first: ℓ' (scrutinee) then ℓ (motive)
                &[scrut_level.clone(), level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_motive, s_scrut],
                gamma,
            ))
        }
        Term::TmSquash { level, ty } => {
            let s_ty = rec.elim_tm(
                Level::succ(level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(level.clone())),
                Rc::clone(ty),
            );
            Some(fire(
                &b.tm_squash,
                std::slice::from_ref(level),
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(ty))],
                vec![s_ty],
                gamma,
            ))
        }
        Term::Squash { level, ty, tm } => {
            let s_ty = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(ty));
            let s_tm = rec.elim_tm(level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(tm));
            Some(fire(
                &b.tm_squash_in,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Tm(Rc::clone(tm)),
                ],
                vec![s_ty, s_tm],
                gamma,
            ))
        }
        Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
            let sq_src = Rc::new(Type::Squash {
                level: src_level.clone(),
                ty: Rc::clone(src_ty),
            });
            let dz = extend(delta, Rc::clone(&sq_src), src_level.clone());
            let dx = extend(delta, Rc::clone(src_ty), src_level.clone());
            let s_src = rec.elim_ty(src_level.clone(), delta.clone(), Rc::clone(src_ty));
            let s_motive = rec.elim_ty(dst_level.clone(), dz, Rc::clone(motive));
            let packed = Rc::new(Term::Squash {
                level: src_level.clone(),
                ty: Rc::new(src_ty.shift_local(1)),
                tm: Rc::new(Term::Var(LocalVar(0))),
            });
            let case_inner = motive.apply_local(
                &LocalSubst::id(delta).shift_local(1).extended(packed),
            );
            let case_ty = Rc::new(Type::Squash {
                level: dst_level.clone(),
                ty: Rc::new(case_inner),
            });
            let s_case = rec.elim_tm(dst_level.clone(), dx, case_ty, Rc::clone(case));
            let s_scrut = rec.elim_tm(
                src_level.clone(),
                delta.clone(),
                Rc::clone(&sq_src),
                Rc::clone(scrut),
            );
            Some(fire(
                &b.tm_elim_squash,
                &[dst_level.clone(), src_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(src_ty)),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(case)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_src, s_motive, s_case, s_scrut],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, u_a, u_b, x_a, x_b. t'_+) — the encoding; mirrors
        // tm_sigma minus the binder extension.   (extension)
        Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
            let s_lhs = rec.elim_tm(
                Level::succ(lhs_level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(lhs_level.clone())),
                Rc::clone(lhs),
            );
            let s_rhs = rec.elim_tm(
                Level::succ(rhs_level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(rhs_level.clone())),
                Rc::clone(rhs),
            );
            Some(fire(
                &b.tm_sum,
                &[rhs_level.clone(), lhs_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                ],
                vec![s_lhs, s_rhs],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_A, U_B, u_a, x_A, x_B, x_a. t_inl) — both type
        // annotations are sub-structures.   (extension)
        Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
            let s_lhs = rec.elim_ty(lhs_level.clone(), delta.clone(), Rc::clone(lhs));
            let s_rhs = rec.elim_ty(rhs_level.clone(), delta.clone(), Rc::clone(rhs));
            let s_val =
                rec.elim_tm(lhs_level.clone(), delta.clone(), Rc::clone(lhs), Rc::clone(val));
            Some(fire(
                &b.tm_inl,
                &[rhs_level.clone(), lhs_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(lhs)),
                    GlobalEntry::Ty(Rc::clone(rhs)),
                    GlobalEntry::Tm(Rc::clone(val)),
                ],
                vec![s_lhs, s_rhs, s_val],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_A, U_B, u_b, x_A, x_B, x_b. t_inr) — as inl but the
        // value inhabits B.   (extension)
        Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
            let s_lhs = rec.elim_ty(lhs_level.clone(), delta.clone(), Rc::clone(lhs));
            let s_rhs = rec.elim_ty(rhs_level.clone(), delta.clone(), Rc::clone(rhs));
            let s_val =
                rec.elim_tm(rhs_level.clone(), delta.clone(), Rc::clone(rhs), Rc::clone(val));
            Some(fire(
                &b.tm_inr,
                &[rhs_level.clone(), lhs_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(lhs)),
                    GlobalEntry::Ty(Rc::clone(rhs)),
                    GlobalEntry::Tm(Rc::clone(val)),
                ],
                vec![s_lhs, s_rhs, s_val],
                gamma,
            ))
        }
        // (ℓ, ℓ', ℓ'', g, U_A, U_B, U_M, u_l, u_r, u_t, x_A, x_B, x_M, x_l,
        // x_r, x_t. t_case) — x_M/x_l/x_r/x_t recurse (x_M at the *type*
        // motive); a positive dependent eliminator.   (extension)
        Term::Case {
            lhs_level,
            rhs_level,
            motive_level,
            lhs,
            rhs,
            motive,
            case_l,
            case_r,
            scrut,
        } => {
            let lmax = Level::max(lhs_level.clone(), rhs_level.clone());
            let sum = Rc::new(Type::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            });
            let s_lhs = rec.elim_ty(lhs_level.clone(), delta.clone(), Rc::clone(lhs));
            let s_rhs = rec.elim_ty(rhs_level.clone(), delta.clone(), Rc::clone(rhs));
            // M scoped in (Δ, z : A + B).
            let dz = extend(delta, Rc::clone(&sum), lmax.clone());
            let s_motive = rec.elim_ty(motive_level.clone(), dz, Rc::clone(motive));
            // c_l : M[inl x/z] scoped in (Δ, x : A).
            let dx = extend(delta, Rc::clone(lhs), lhs_level.clone());
            let inl_x = Term::Inl {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(rhs.shift_local(1)),
                val: Rc::new(Term::Var(LocalVar(0))),
            };
            let left_ty = motive
                .apply_local(&LocalSubst::id(delta).shift_local(1).extended(Rc::new(inl_x)));
            let s_case_l =
                rec.elim_tm(motive_level.clone(), dx, Rc::new(left_ty), Rc::clone(case_l));
            // c_r : M[inr y/z] scoped in (Δ, y : B).
            let dy = extend(delta, Rc::clone(rhs), rhs_level.clone());
            let inr_y = Term::Inr {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(rhs.shift_local(1)),
                val: Rc::new(Term::Var(LocalVar(0))),
            };
            let right_ty = motive
                .apply_local(&LocalSubst::id(delta).shift_local(1).extended(Rc::new(inr_y)));
            let s_case_r =
                rec.elim_tm(motive_level.clone(), dy, Rc::new(right_ty), Rc::clone(case_r));
            let s_scrut =
                rec.elim_tm(lmax, delta.clone(), Rc::clone(&sum), Rc::clone(scrut));
            Some(fire(
                &b.tm_case,
                &[motive_level.clone(), rhs_level.clone(), lhs_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(lhs)),
                    GlobalEntry::Ty(Rc::clone(rhs)),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(case_l)),
                    GlobalEntry::Tm(Rc::clone(case_r)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_lhs, s_rhs, s_motive, s_case_l, s_case_r, s_scrut],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_W) — the encoding; mirrors
        // tm_pi/tm_sigma.   (extension)
        Term::TmW { shape_level, pos_level, shape, pos } => {
            let s_shape = rec.elim_tm(
                Level::succ(shape_level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(shape_level.clone())),
                Rc::clone(shape),
            );
            let dx = extend(
                delta,
                Rc::new(Type::El { level: shape_level.clone(), tm: Rc::clone(shape) }),
                shape_level.clone(),
            );
            let s_pos = rec.elim_tm(
                Level::succ(pos_level.clone()),
                dx,
                Rc::new(Type::Ty(pos_level.clone())),
                Rc::clone(pos),
            );
            Some(fire(
                &b.tm_w,
                &[pos_level.clone(), shape_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(shape)),
                    GlobalEntry::Tm(Rc::clone(pos)),
                ],
                vec![s_shape, s_pos],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, U_T, u_a, u_f, x_S, x_T, x_a, x_f. t_sup) — both
        // type annotations are sub-structures (like pair).   (extension)
        Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
            let lmax = Level::max(shape_level.clone(), pos_level.clone());
            let s_shape = rec.elim_ty(shape_level.clone(), delta.clone(), Rc::clone(shape_ty));
            let dx = extend(delta, Rc::clone(shape_ty), shape_level.clone());
            let s_pos = rec.elim_ty(pos_level.clone(), dx, Rc::clone(pos_ty));
            let s_label = rec.elim_tm(
                shape_level.clone(),
                delta.clone(),
                Rc::clone(shape_ty),
                Rc::clone(label),
            );
            // f : Π(y : T[a/x]). W.
            let w = Type::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: Rc::clone(shape_ty),
                pos: Rc::clone(pos_ty),
            };
            let pos_at =
                pos_ty.apply_local(&LocalSubst::id(delta).extended(Rc::clone(label)));
            let f_ty = Rc::new(Type::Pi {
                dom_level: pos_level.clone(),
                cod_level: lmax.clone(),
                dom: Rc::new(pos_at),
                cod: Rc::new(w.shift_local(1)),
            });
            let s_children = rec.elim_tm(
                Level::max(pos_level.clone(), lmax),
                delta.clone(),
                f_ty,
                Rc::clone(children),
            );
            Some(fire(
                &b.tm_sup,
                &[pos_level.clone(), shape_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(shape_ty)),
                    GlobalEntry::Ty(Rc::clone(pos_ty)),
                    GlobalEntry::Tm(Rc::clone(label)),
                    GlobalEntry::Tm(Rc::clone(children)),
                ],
                vec![s_shape, s_pos, s_label, s_children],
                gamma,
            ))
        }
        // (ℓ, ℓ', ℓ'', g, U_S, U_T, U_M, u_s, u_t, x_S, x_T, x_M, x_s, x_t.
        // t_elimW) — x_M recurses at the *type* motive; the step's
        // annotation type instantiates the motive at sup(a, f), mirroring
        // the typing rule.   (extension)
        Term::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            scrut,
        } => {
            let lmax = Level::max(shape_level.clone(), pos_level.clone());
            let w = Type::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
            };
            let s_shape = rec.elim_ty(shape_level.clone(), delta.clone(), Rc::clone(shape));
            let da = extend(delta, Rc::clone(shape), shape_level.clone());
            let s_pos = rec.elim_ty(pos_level.clone(), da.clone(), Rc::clone(pos));
            let dz = extend(delta, Rc::new(w.clone()), lmax.clone());
            let s_motive = rec.elim_ty(motive_level.clone(), dz, Rc::clone(motive));
            // Step scoped in (Δ, a : S, f : Π(y:T[a/x]). W,
            // ih : Π(y:T[a/x]). M[f y/z]) — same construction as typing.
            let f_ty = Type::Pi {
                dom_level: pos_level.clone(),
                cod_level: lmax.clone(),
                dom: Rc::clone(pos),
                cod: Rc::new(w.shift_local(2)),
            };
            let daf = extend(&da, Rc::new(f_ty), Level::max(pos_level.clone(), lmax.clone()));
            let f_y = Term::App {
                fun: Rc::new(Term::Var(LocalVar(1))),
                dom_level: pos_level.clone(),
                cod_level: lmax.clone(),
                dom: Rc::new(pos.shift_local(2)),
                cod: Rc::new(w.shift_local(4)),
                arg: Rc::new(Term::Var(LocalVar(0))),
            };
            let ih_cod = motive
                .apply_local(&LocalSubst::id(delta).shift_local(3).extended(Rc::new(f_y)));
            let ih_ty = Type::Pi {
                dom_level: pos_level.clone(),
                cod_level: motive_level.clone(),
                dom: Rc::new(pos.shift_local(1)),
                cod: Rc::new(ih_cod),
            };
            let dafi = extend(
                &daf,
                Rc::new(ih_ty),
                Level::max(pos_level.clone(), motive_level.clone()),
            );
            let Type::W { shape: s2, pos: p2, .. } = w.shift_local(2) else {
                unreachable!()
            };
            let sup_af = Term::Sup {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape_ty: s2,
                pos_ty: p2,
                label: Rc::new(Term::Var(LocalVar(1))),
                children: Rc::new(Term::Var(LocalVar(0))),
            };
            let ty_step = motive.apply_local(
                &LocalSubst::id(delta)
                    .shift_local(3)
                    .extended(Rc::new(sup_af.shift_local(1))),
            );
            let s_step =
                rec.elim_tm(motive_level.clone(), dafi, Rc::new(ty_step), Rc::clone(step));
            let s_scrut = rec.elim_tm(lmax, delta.clone(), Rc::new(w), Rc::clone(scrut));
            Some(fire(
                &b.tm_elim_w,
                &[motive_level.clone(), pos_level.clone(), shape_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(shape)),
                    GlobalEntry::Ty(Rc::clone(pos)),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(step)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_shape, s_pos, s_motive, s_step, s_scrut],
                gamma,
            ))
        }
        // (ℓ, g, u_t, u_k, x_t, x_k. t'_Vec) — the encoding.   (extension, §6)
        Term::TmVec { level, elem, len } => {
            let s_elem = rec.elim_tm(
                Level::succ(level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(level.clone())),
                Rc::clone(elem),
            );
            let s_len = rec.elim_tm(
                Level::Zero,
                delta.clone(),
                Rc::new(Type::Nat),
                Rc::clone(len),
            );
            Some(fire(
                &b.tm_vec,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(elem)),
                    GlobalEntry::Tm(Rc::clone(len)),
                ],
                vec![s_elem, s_len],
                gamma,
            ))
        }
        // (g, u_k, x_k. t'_Fin) — the encoding; no universe payload.
        Term::TmFin { len } => {
            let s_len = rec.elim_tm(
                Level::Zero,
                delta.clone(),
                Rc::new(Type::Nat),
                Rc::clone(len),
            );
            Some(fire(
                &b.tm_fin,
                &[],
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(len))],
                vec![s_len],
                gamma,
            ))
        }
        // (ℓ, g, u_s, u_n, x_s, x_n. t'_Wf) — the encoding; the arity
        // recurses under `x : El ℓ u_s`.   (extension, §6)
        Term::TmWf { level, shape, arity } => {
            let s_shape = rec.elim_tm(
                Level::succ(level.clone()),
                delta.clone(),
                Rc::new(Type::Ty(level.clone())),
                Rc::clone(shape),
            );
            let dx = extend(
                delta,
                Rc::new(Type::El { level: level.clone(), tm: Rc::clone(shape) }),
                level.clone(),
            );
            let s_arity = rec.elim_tm(Level::Zero, dx, Rc::new(Type::Nat), Rc::clone(arity));
            Some(fire(
                &b.tm_wf,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(shape)),
                    GlobalEntry::Tm(Rc::clone(arity)),
                ],
                vec![s_shape, s_arity],
                gamma,
            ))
        }
        // (ℓ, g, U_S, u_n, u_a, u_cs, x_S, x_n, x_a, x_cs. t_supf) — the
        // shape annotation is a type sub-structure (like sup's), the arity a
        // term one; the children recurse at the `Vec` type.   (extension, §6)
        Term::Supf { level, shape, arity, label, children } => {
            let wf = Type::Wf {
                level: level.clone(),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
            };
            let s_shape = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(shape));
            let dx = extend(delta, Rc::clone(shape), level.clone());
            let s_arity = rec.elim_tm(Level::Zero, dx, Rc::new(Type::Nat), Rc::clone(arity));
            let s_label =
                rec.elim_tm(level.clone(), delta.clone(), Rc::clone(shape), Rc::clone(label));
            let arity_at =
                arity.apply_local(&LocalSubst::id(delta).extended(Rc::clone(label)));
            let cs_ty = Type::Vec {
                level: level.clone(),
                elem: Rc::new(wf.clone()),
                len: Rc::new(arity_at),
            };
            let s_children = rec.elim_tm(
                level.clone(),
                delta.clone(),
                Rc::new(cs_ty),
                Rc::clone(children),
            );
            Some(fire(
                &b.tm_supf,
                std::slice::from_ref(level),
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(shape)),
                    GlobalEntry::Tm(Rc::clone(arity)),
                    GlobalEntry::Tm(Rc::clone(label)),
                    GlobalEntry::Tm(Rc::clone(children)),
                ],
                vec![s_shape, s_arity, s_label, s_children],
                gamma,
            ))
        }
        // (ℓ, ℓ', g, U_S, u_n, U_M, u_s, u_t, x_S, x_n, x_M, x_s, x_t.
        // t_elimWf) — x_M recurses at the *type* motive; the step's context
        // and annotation come from `wf_step_telescope`, exactly as in the
        // typing rule.   (extension, §6)
        Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
            let wf = Type::Wf {
                level: level.clone(),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
            };
            let s_shape = rec.elim_ty(level.clone(), delta.clone(), Rc::clone(shape));
            let da = extend(delta, Rc::clone(shape), level.clone());
            let s_arity =
                rec.elim_tm(Level::Zero, da.clone(), Rc::new(Type::Nat), Rc::clone(arity));
            let dz = extend(delta, Rc::new(wf.clone()), level.clone());
            let s_motive = rec.elim_ty(motive_level.clone(), dz, Rc::clone(motive));
            let (cs_ty, ih_ty, step_ty) =
                wf_step_telescope(delta, level, motive_level, shape, arity, motive);
            let dacs = extend(&da, Rc::new(cs_ty), level.clone());
            let dacsi = extend(&dacs, Rc::new(ih_ty), motive_level.clone());
            let s_step =
                rec.elim_tm(motive_level.clone(), dacsi, Rc::new(step_ty), Rc::clone(step));
            let s_scrut =
                rec.elim_tm(level.clone(), delta.clone(), Rc::new(wf), Rc::clone(scrut));
            Some(fire(
                &b.tm_elim_wf,
                &[motive_level.clone(), level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(shape)),
                    GlobalEntry::Tm(Rc::clone(arity)),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(step)),
                    GlobalEntry::Tm(Rc::clone(scrut)),
                ],
                vec![s_shape, s_arity, s_motive, s_step, s_scrut],
                gamma,
            ))
        }
        // (l, l', li, g, u_I, u_S, u_P, u_o, u_j, x_I, x_S, x_P, x_o, x_j.
        // t'_M) — the encoding; the pieces recurse at `Ty`, under `El` of
        // the earlier ones, as tm_wf's do.   (docs/kernel-m-codes-design.md §2)
        Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => {
            let el = |level: &Level, tm: &Rc<Term>| {
                Rc::new(Type::El { level: level.clone(), tm: Rc::clone(tm) })
            };
            let code_at = |level: &Level, ctx: LocalCtx, tm: &Rc<Term>| {
                rec.elim_tm(Level::succ(level.clone()), ctx, Rc::new(Type::Ty(level.clone())), Rc::clone(tm))
            };
            let el_i = el(idx_level, idx);
            let di = extend(delta, Rc::clone(&el_i), idx_level.clone());
            let dis = extend(&di, el(level, shape), level.clone());
            let disp = extend(&dis, el(pos_level, pos), pos_level.clone());
            let s_idx = code_at(idx_level, delta.clone(), idx);
            let s_shape = code_at(level, di, shape);
            let s_pos = code_at(pos_level, dis, pos);
            let s_next = rec.elim_tm(idx_level.clone(), disp, Rc::new(el_i.shift_local(3)), Rc::clone(next));
            let s_index = rec.elim_tm(idx_level.clone(), delta.clone(), el_i, Rc::clone(index));
            Some(fire(
                &b.tm_m,
                &[idx_level.clone(), pos_level.clone(), level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Tm(Rc::clone(idx)),
                    GlobalEntry::Tm(Rc::clone(shape)),
                    GlobalEntry::Tm(Rc::clone(pos)),
                    GlobalEntry::Tm(Rc::clone(next)),
                    GlobalEntry::Tm(Rc::clone(index)),
                ],
                vec![s_idx, s_shape, s_pos, s_next, s_index],
                gamma,
            ))
        }
        // (l, l', li, k, g, U_I, U_S, U_P, u_o, U_X, u_c, u_j, u_x, x_I, …,
        // x_x. t_corec) — the step recurses at `m_step_ty`, as in the typing
        // rule. A boxed corec is inert: this is the only thing the code
        // recursor does with one.   (docs/kernel-m-codes-design.md §2)
        Term::Corec { sig, carrier_level, carrier, step, index, seed } => {
            let (mut globals, mut locals) = m_sig_pieces(rec, delta, sig);
            let di = extend(delta, Rc::clone(&sig.idx), sig.idx_level.clone());
            let dix = extend(&di, Rc::clone(carrier), carrier_level.clone());
            let step_ty = m_step_ty(sig, carrier_level, carrier).shift_local(1);
            let step_level = Level::join(
                sig.level.clone(),
                Level::join(carrier_level.clone(), sig.family_level()),
            );
            locals.push(rec.elim_ty(carrier_level.clone(), di, Rc::clone(carrier)));
            locals.push(rec.elim_tm(step_level, dix, Rc::new(step_ty), Rc::clone(step)));
            locals.push(rec.elim_tm(
                sig.idx_level.clone(),
                delta.clone(),
                Rc::clone(&sig.idx),
                Rc::clone(index),
            ));
            locals.push(rec.elim_tm(
                carrier_level.clone(),
                delta.clone(),
                Rc::new(carrier.inst_top(0, index)),
                Rc::clone(seed),
            ));
            globals.extend([
                GlobalEntry::Ty(Rc::clone(carrier)),
                GlobalEntry::Tm(Rc::clone(step)),
                GlobalEntry::Tm(Rc::clone(index)),
                GlobalEntry::Tm(Rc::clone(seed)),
            ]);
            let mut univs = vec![carrier_level.clone()];
            univs.extend(m_univs(sig));
            Some(fire(&b.tm_corec, &univs, globals, locals, gamma))
        }
        // (l, l', li, g, U_I, U_S, U_P, u_o, u_j, u_m, x_I, …, x_m. t_out)
        //   (docs/kernel-m-codes-design.md §2)
        Term::Out { sig, index, scrut } => {
            let (mut globals, mut locals) = m_sig_pieces(rec, delta, sig);
            locals.push(rec.elim_tm(
                sig.idx_level.clone(),
                delta.clone(),
                Rc::clone(&sig.idx),
                Rc::clone(index),
            ));
            locals.push(rec.elim_tm(
                sig.family_level(),
                delta.clone(),
                Rc::new(sig.at(Rc::clone(index))),
                Rc::clone(scrut),
            ));
            globals.extend([GlobalEntry::Tm(Rc::clone(index)), GlobalEntry::Tm(Rc::clone(scrut))]);
            Some(fire(&b.tm_out, &m_univs(sig), globals, locals, gamma))
        }
        // (ℓ, g, u_n, u_f, x_n, x_f. t'_DVec) — the encoding; the family
        // recurses at `Ty` under `i : Fin u_n`.   (docs/iwf-former-design.md §6)
        Term::TmDVec { level, len, fam } => {
            let di = extend(delta, Rc::new(Type::Fin { len: Rc::clone(len) }), Level::Zero);
            let s_len = rec.elim_tm(Level::Zero, delta.clone(), Rc::new(Type::Nat), Rc::clone(len));
            let s_fam = rec.elim_tm(Level::succ(level.clone()), di, Rc::new(Type::Ty(level.clone())), Rc::clone(fam));
            Some(fire(
                &b.tm_dvec,
                std::slice::from_ref(level),
                vec![GlobalEntry::Ctx(delta.clone()), GlobalEntry::Tm(Rc::clone(len)), GlobalEntry::Tm(Rc::clone(fam))],
                vec![s_len, s_fam],
                gamma,
            ))
        }
        // (ℓ, ℓi, g, u_I, u_S, u_n, u_o, u_c, u_m, x_I, …, x_m. t'_IWf) —
        // the encoding; the index type and shapes recurse at `Ty`, the rest
        // under `El` of the shapes, as tm_wf's do.   (design §6)
        Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => {
            let sig = crate::term::iwf_sig_of_code(level, idx_level, idx, shape, arity, out, child);
            let code_at = |level: &Level, tm: &Rc<Term>| {
                rec.elim_tm(Level::succ(level.clone()), delta.clone(), Rc::new(Type::Ty(level.clone())), Rc::clone(tm))
            };
            let (mut globals, mut locals) = iwf_sig_pieces(rec, delta, &sig);
            globals[1] = GlobalEntry::Tm(Rc::clone(idx));
            globals[2] = GlobalEntry::Tm(Rc::clone(shape));
            locals[0] = code_at(idx_level, idx);
            locals[1] = code_at(level, shape);
            globals.push(GlobalEntry::Tm(Rc::clone(index)));
            locals.push(rec.elim_tm(idx_level.clone(), delta.clone(), Rc::clone(&sig.idx), Rc::clone(index)));
            Some(fire(&b.tm_iwf, &iwf_univs(&sig), globals, locals, gamma))
        }
        // (ℓ, ℓi, g, U_I, U_S, u_n, u_o, u_c, u_a, u_cs, x_I, …, x_c, x_a,
        // x_cs. t_supi) — the children recurse at `iwf_children_ty`, as in
        // the typing rule.   (design §6)
        Term::Supi { sig, label, children } => {
            let (mut globals, mut locals) = iwf_sig_pieces(rec, delta, sig);
            locals.push(rec.elim_tm(sig.level.clone(), delta.clone(), Rc::clone(&sig.shape), Rc::clone(label)));
            locals.push(rec.elim_tm(
                sig.family_level(),
                delta.clone(),
                Rc::new(iwf_children_ty(sig, label)),
                Rc::clone(children),
            ));
            globals.extend([GlobalEntry::Tm(Rc::clone(label)), GlobalEntry::Tm(Rc::clone(children))]);
            Some(fire(&b.tm_sup_i, &iwf_univs(sig), globals, locals, gamma))
        }
        // (ℓ, ℓi, ℓ', g, U_I, U_S, u_n, u_o, u_c, U_M, u_s, u_m, u_t, x_I, …,
        // x_t. t_elimIWf) — x_M recurses at the *type* motive under
        // `(j, z)`; the step's context and annotation come from
        // `iwf_step_telescope`, exactly as in the typing rule.   (design §6)
        Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => {
            let (mut globals, mut locals) = iwf_sig_pieces(rec, delta, sig);
            let fl = sig.family_level();
            let dj = extend(delta, Rc::clone(&sig.idx), sig.idx_level.clone());
            let djz = extend(&dj, Rc::new(iwf_motive_scrut_ty(sig)), fl.clone());
            let (cs_ty, ih_ty, step_ty) = iwf_step_telescope(sig, motive_level, motive);
            let da = extend(delta, Rc::clone(&sig.shape), sig.level.clone());
            let dacs = extend(&da, Rc::new(cs_ty), fl.clone());
            let dacsi = extend(&dacs, Rc::new(ih_ty), motive_level.clone());
            locals.push(rec.elim_ty(motive_level.clone(), djz, Rc::clone(motive)));
            locals.push(rec.elim_tm(motive_level.clone(), dacsi, Rc::new(step_ty), Rc::clone(step)));
            locals.push(rec.elim_tm(sig.idx_level.clone(), delta.clone(), Rc::clone(&sig.idx), Rc::clone(index)));
            locals.push(rec.elim_tm(fl, delta.clone(), Rc::new(sig.at(Rc::clone(index))), Rc::clone(scrut)));
            globals.extend([
                GlobalEntry::Ty(Rc::clone(motive)),
                GlobalEntry::Tm(Rc::clone(step)),
                GlobalEntry::Tm(Rc::clone(index)),
                GlobalEntry::Tm(Rc::clone(scrut)),
            ]);
            let mut univs = vec![motive_level.clone()];
            univs.extend(iwf_univs(sig));
            Some(fire(&b.tm_elim_iwf, &univs, globals, locals, gamma))
        }
        // box (u^δ): blocked, neutral.
        Term::GlobalTm { .. } => None,
        // Layer-m forms cannot be layer-c code: ill-typed, stuck.
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// WHNF / neutral classification (the W/V/w/ν grammars)
// ---------------------------------------------------------------------------

/// Neutral types `V := U^δ | El^l ν`.
pub fn is_neutral_type(t: &Type) -> bool {
    match t {
        Type::GlobalTy { .. } => true,
        Type::El { tm, .. } => is_neutral_term(tm),
        // A stuck length blocks the reduction, so the type is neutral —
        // conversion compares such `Vec`/`Fin`/`DVec` structurally (extension).
        Type::Vec { len, .. } | Type::Fin { len } | Type::DVec { len, .. } => {
            is_neutral_term(len)
        }
        _ => false,
    }
}

/// Weak head normal types, `W ∪ V` (conversion compares neutrals through
/// the same normal-form judgment, so the useful predicate is the union).
pub fn is_whnf_type(t: &Type) -> bool {
    match t {
        Type::Nat
        | Type::Pi { .. }
        | Type::Id { .. }
        | Type::SEq { .. }
        | Type::SEmpty { .. }
        | Type::Squash { .. }
        | Type::Sigma { .. }
        | Type::Unit { .. }
        | Type::Empty { .. }
        | Type::Sum { .. }
        | Type::W { .. }
        | Type::Wf { .. }
        | Type::IWf { .. }
        | Type::M { .. }
        | Type::Ty(_)
        | Type::UPi { .. }
        | Type::CtxPi { .. }
        | Type::TyPi { .. }
        | Type::CodeTy { .. }
        | Type::CodeTm { .. } => true,
        Type::El { .. } | Type::GlobalTy { .. } => is_neutral_type(t),
        // Vec/Fin step on a *canonical* length, so they are normal exactly
        // when the length is stuck (extension; docs/wf-former-design.md §1).
        // `DVec` likewise (docs/iwf-former-design.md §1.1).
        Type::Vec { len, .. } | Type::Fin { len } | Type::DVec { len, .. } => {
            is_neutral_term(len)
        }
    }
}

/// Neutral terms `ν` (Ne). Recursors are neutral on neutral scrutinees and
/// on `box (U^δ)` / `box (u^δ)`. For `ElimCodeTm` we additionally require
/// the type annotation to be in WHNF — the paper's grammar leaves it
/// unconstrained, but its fixed type-then-term reduction order still
/// reduces such a term, and neutrals must not step.
pub fn is_neutral_term(t: &Term) -> bool {
    match t {
        Term::Var(_) | Term::GlobalTm { .. } => true,
        Term::ElimNat { scrut, .. } => is_neutral_term(scrut),
        Term::ElimEmpty { scrut, .. } => is_neutral_term(scrut),
        Term::Case { scrut, .. } => is_neutral_term(scrut),
        Term::ElimW { scrut, .. } => is_neutral_term(scrut),
        Term::ElimWf { scrut, .. } => is_neutral_term(scrut),
        Term::ElimIWf { scrut, .. } => is_neutral_term(scrut),
        Term::Out { scrut, .. } => is_neutral_term(scrut),
        Term::J { proof, .. } => is_neutral_term(proof),
        Term::ElimSEmpty { scrut, .. } => is_neutral_term(scrut),
        Term::ElimSquash { scrut, .. } => is_neutral_term(scrut),
        Term::Fst { pair, .. }
        | Term::Snd { pair, .. }
        | Term::FstAt { pair, .. }
        | Term::SndAt { pair, .. } => is_neutral_term(pair),
        Term::App { fun, .. }
        | Term::AppAt { fun, .. }
        | Term::UApp { fun, .. }
        | Term::CtxApp { fun, .. }
        | Term::TyApp { fun, .. } => is_neutral_term(fun),
        Term::LetBoxTy { scrut, .. } | Term::LetBoxTm { scrut, .. } => is_neutral_term(scrut),
        Term::ElimCodeTy { scrut, .. } => match &**scrut {
            Term::BoxTy(code) => matches!(&**code, Type::GlobalTy { .. }),
            s => is_neutral_term(s),
        },
        Term::ElimCodeTm { ty, scrut, .. } => {
            is_whnf_type(ty)
                && match &**scrut {
                    Term::BoxTm(code) => matches!(&**code, Term::GlobalTm { .. }),
                    s => is_neutral_term(s),
                }
        }
        _ => false,
    }
}

/// `fst`/`snd` of a [`Term::VecLit`]: a component of its one-step view
/// ([`crate::term::vec_lit_unfold`]), so a projection reads the literal
/// exactly as it reads the pair chain it spells. A literal outside its
/// range is ill-typed and stuck.
fn vec_lit_proj(lit: &Term, second: bool) -> Option<Term> {
    let Term::VecLit { level, elem, zero, one, width, bits } = lit else {
        unreachable!("vec_lit_proj is given a vector literal")
    };
    if !crate::term::vec_lit_in_range(*width, *bits) {
        return None;
    }
    let Term::Pair { fst, snd, .. } =
        crate::term::vec_lit_unfold(level, elem, zero, one, *width, *bits)
    else {
        unreachable!("a vector literal unfolds to a pair")
    };
    Some((*if second { snd } else { fst }).clone())
}

/// `fst`/`snd` of a [`Term::VecItems`], through its one-step view
/// ([`crate::term::vec_items_unfold`]) as [`vec_lit_proj`] is. Out of
/// range is ill-typed and stuck.
fn vec_items_proj(node: &Term, second: bool) -> Option<Term> {
    let Term::VecItems { level, elem, items, from } = node else {
        unreachable!("vec_items_proj is given a vector-items node")
    };
    let Term::Pair { fst, snd, .. } = crate::term::vec_items_unfold(level, elem, items, *from)? else {
        unreachable!("a vector-items node unfolds to a pair")
    };
    Some((*if second { snd } else { fst }).clone())
}

/// Weak head normal terms `w` (Nf), including neutrals.
pub fn is_whnf_term(t: &Term) -> bool {
    match t {
        Term::TmNat
        | Term::TmPi { .. }
        | Term::TmTy(_)
        | Term::TmId { .. }
        | Term::TmSigma { .. }
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::TmSEq { .. }
        | Term::TmSEmpty { .. }
        | Term::TmSquash { .. }
        | Term::TmSum { .. }
        | Term::TmW { .. }
        | Term::TmVec { .. }
        | Term::TmFin { .. }
        | Term::TmWf { .. }
        | Term::TmM { .. }
        | Term::TmDVec { .. }
        | Term::TmIWf { .. }
        | Term::Zero
        | Term::Succ(_)
        | Term::Refl { .. }
        | Term::SRefl { .. }
        | Term::Squash { .. }
        | Term::Pair { .. }
        | Term::Triv { .. }
        | Term::Inl { .. }
        | Term::Inr { .. }
        // The checked spellings are introduction forms and are whnf exactly
        // as the forms they spell (docs/intro-by-type-design.md).
        | Term::PairAt { .. }
        | Term::VecLit { .. }
        | Term::VecItems { .. }
        | Term::InlAt { .. }
        | Term::InrAt { .. }
        | Term::Sup { .. }
        | Term::Supf { .. }
        | Term::Supi { .. }
        | Term::Corec { .. }
        | Term::Lam { .. }
        | Term::ULam { .. }
        | Term::CtxLam { .. }
        | Term::TyLam { .. }
        | Term::BoxTy(_)
        | Term::BoxTm(_) => true,
        _ => is_neutral_term(t),
    }
}
