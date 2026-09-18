//! Untyped weak-head reduction `⇝` and WHNF/neutral classification
//! (docs/delam/06, §Weak Head Normal Forms and §Reduction Relations).
//!
//! - Reduction is **untyped** and fires on head *shape* only: level
//!   annotations never gate a β-rule (they are forced by typing;
//!   preservation is the paper's job, not this function's).
//! - [`step_term`]/[`step_type`] are the single-step relation; `None` means
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
    nth, wf_step_telescope, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx,
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
/// measurably holds — a narrower gap than it sounds, because a re-entry costs
/// kilobytes of stack. Both ends are measured in the design doc, and moving
/// this number without re-reading them will break one end or the other.
pub const NATIVE_DEPTH_LIMIT: u32 = 1024;

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
    bodies: Option<&'a BodyCache>,
}

/// Rescoped definition bodies, memoized by [`GlobalVar`].
///
/// [`Defs::body`] rescopes a body with `shift_global(v + 1)`, and that
/// rescoping is a function of the index alone — not of the occurrence, not
/// of the δ that occurrence carries. A cache is therefore sound *for one
/// Ψ*, which is why it is owned beside the Ψ it belongs to (`conv::Env`)
/// and rebuilt whenever a telescope push changes Ψ, rather than being a
/// global table keyed by an index that means different things in different
/// scopes.
#[derive(Default)]
pub struct BodyCache(std::cell::RefCell<Vec<Option<Rc<Term>>>>);

impl BodyCache {
    pub fn new() -> BodyCache {
        BodyCache::default()
    }

    fn get_or_insert(&self, v: GlobalVar, build: impl FnOnce() -> Term) -> Rc<Term> {
        let i = v.0 as usize;
        let mut slots = self.0.borrow_mut();
        if slots.len() <= i {
            slots.resize(i + 1, None);
        }
        if let Some(t) = &slots[i] {
            return Rc::clone(t);
        }
        // `build` reads only Ψ, never the cache, so no re-entrant borrow.
        let t = Rc::new(build());
        slots[i] = Some(Rc::clone(&t));
        t
    }
}

impl<'a> Defs<'a> {
    /// Nothing unfolds: every global is an opaque neutral, exactly as in
    /// ch. 06's reduction relation. The right choice at layer c, and the
    /// meaning of the Ψ-free [`step_term`]/[`whnf_term`] entry points.
    pub fn opaque() -> Defs<'a> {
        Defs { psi: None, bodies: None }
    }

    /// Definitions of `psi` unfold. Only sound at a computing layer.
    pub fn transparent(psi: &'a GlobalCtx) -> Defs<'a> {
        Defs { psi: Some(psi), bodies: None }
    }

    /// [`Defs::transparent`] with a [`BodyCache`] to memoize the rescoping
    /// in. The cache must belong to this exact `psi`.
    pub fn transparent_cached(psi: &'a GlobalCtx, bodies: &'a BodyCache) -> Defs<'a> {
        Defs { psi: Some(psi), bodies: Some(bodies) }
    }

    /// The body of `v`, rescoped from its Ψ-prefix into the ambient Ψ (the
    /// `shift_global(v + 1)` convention `typing.rs` uses for the binding's
    /// type). `None` for a declaration, an out-of-scope index, or an opaque
    /// environment.
    pub(crate) fn body(&self, v: GlobalVar) -> Option<Rc<Term>> {
        let psi = self.psi?;
        let i = psi.bindings.len().checked_sub(1 + v.0 as usize)?;
        let GlobalBinding::Tm { body: Some(t), .. } = psi.bindings.get(i)? else {
            return None;
        };
        let rescope = || {
            crate::stats::delta_body_rescopes(1);
            t.shift_global(v.0 + 1)
        };
        Some(match self.bodies {
            Some(c) => c.get_or_insert(v, rescope),
            None => Rc::new(rescope()),
        })
    }

    /// The body of `v` **as it is stored**, in its own Ψ-prefix rather than
    /// in the ambient Ψ: the value machine reads it under the global offset
    /// `v + 1` instead of paying for a copy per gate call
    /// (`docs/lazy-global-offset-design.md`). `None` on the same three
    /// conditions as [`Defs::body`].
    pub(crate) fn body_unshifted(&self, v: GlobalVar) -> Option<&'a Rc<Term>> {
        let psi = self.psi?;
        let i = psi.bindings.len().checked_sub(1 + v.0 as usize)?;
        let GlobalBinding::Tm { body: Some(t), .. } = psi.bindings.get(i)? else {
            return None;
        };
        Some(t)
    }

    /// Whether `v` is a definition here — the head test the conversion
    /// heuristic keys on, without paying for the rescoped body.
    pub fn is_defined(&self, v: GlobalVar) -> bool {
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
    while let Some(next) = step_type_delta(&cur, gamma, defs) {
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
    while let Some(next) = step_term_delta(&cur, gamma, defs) {
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
pub fn step_type(t: &Type, gamma: &LocalCtx) -> Option<Type> {
    step_type_delta(t, gamma, Defs::opaque())
}

/// [`step_type`] with a δ-environment. Type-level bindings have no bodies —
/// a `U^δ` is opaque at every layer — so δ reaches types only through `El`.
pub fn step_type_delta(t: &Type, gamma: &LocalCtx, defs: Defs<'_>) -> Option<Type> {
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
            _ => step_term_delta(tm, gamma, defs)
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
            Term::Zero | Term::NatLit(0) => Some(Type::Unit { level: level.clone() }),
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
                let pred = if *n == 1 { Term::Zero } else { Term::NatLit(n - 1) };
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
            _ => step_term_delta(len, gamma, defs).map(|len| Type::Vec {
                level: level.clone(),
                elem: Rc::clone(elem),
                len: Rc::new(len),
            }),
        },
        // Fin(0) ⇝ Empty^0, Fin(S k) ⇝ Unit^0 +^{0,0} Fin(k).   (§1.2)
        // `Fin` is declared at level 0, so both reducts land there and it
        // needs nothing from the level-indexing round.
        Type::Fin { len } => match &**len {
            Term::Zero | Term::NatLit(0) => Some(Type::Empty { level: Level::Zero }),
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
                    len: Rc::new(if *n == 1 { Term::Zero } else { Term::NatLit(n - 1) }),
                }),
            }),
            _ => step_term_delta(len, gamma, defs).map(|len| Type::Fin { len: Rc::new(len) }),
        },
        _ => None,
    }
}

/// Single-step term reduction `t ⇝ t'`: β for all elimination forms plus
/// congruence at head positions.
pub fn step_term(t: &Term, gamma: &LocalCtx) -> Option<Term> {
    step_term_delta(t, gamma, Defs::opaque())
}

/// [`step_term`] with a δ-environment: the single new rule is
/// `u^δ ⇝ t[δ]` when `u` is a definition of `defs` (extension). It needs no
/// arm of its own anywhere else — every congruence below already steps its
/// head/scrutinee, so a defined global unblocks the whole spine.
pub fn step_term_delta(t: &Term, gamma: &LocalCtx, defs: Defs<'_>) -> Option<Term> {
    match t {
        // δ: `u^δ ⇝ t[δ]` for a definition `u := t`. Opaque at layer c,
        // where `defs` is `Defs::opaque()` — see [`Defs`].
        Term::GlobalTm { var, subst } => Some(defs.body(*var)?.apply_local(subst)),
        Term::ElimNat { level, motive, base, step, scrut } => match &**scrut {
            // elim_Nat … ze ⇝ s
            Term::Zero | Term::NatLit(0) => Some((**base).clone()),
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
                let pred = Rc::new(if *n == 1 { Term::Zero } else { Term::NatLit(n - 1) });
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
            _ => step_term_delta(scrut, gamma, defs).map(|s| Term::ElimNat {
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
                _ => step_term_delta(proof, gamma, defs).map(|p| Term::J {
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
        Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
            match &**proof {
                // transp(…; srefl; t) ⇝ t   (extension; fires on head shape
                // only, like J's β — sufficient for closed computation by
                // canonicity; the neutral-proof case belongs to conv.rs's
                // strip rule, never to reduction. docs/sprop-design.md §5.1)
                Term::SRefl { .. } => Some((**tm).clone()),
                _ => step_term_delta(proof, gamma, defs).map(|p| Term::Transp {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: Rc::clone(ty),
                    motive: Rc::clone(motive),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                    proof: Rc::new(p),
                    tm: Rc::clone(tm),
                }),
            }
        }
        // fst (pair a b) ⇝ a; else reduce the pair   (extension)
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => match &**pair {
            Term::Pair { fst, .. } => Some((**fst).clone()),
            _ => step_term_delta(pair, gamma, defs).map(|p| Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(fst_ty),
                snd_ty: Rc::clone(snd_ty),
                pair: Rc::new(p),
            }),
        },
        // elim_Empty has no β rule (Empty has no constructors); it only ever
        // steps its scrutinee, staying neutral when the scrutinee is.
        Term::ElimEmpty { level, scrut_level, motive, scrut } => {
            step_term_delta(scrut, gamma, defs).map(|s| Term::ElimEmpty {
                level: level.clone(),
                scrut_level: scrut_level.clone(),
                motive: Rc::clone(motive),
                scrut: Rc::new(s),
            })
        }
        // elim_sEmpty likewise (extension; docs/sprop-design.md §5.1).
        Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
            step_term_delta(scrut, gamma, defs).map(|s| Term::ElimSEmpty {
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
                _ => step_term_delta(scrut, gamma, defs).map(|s| Term::ElimSquash {
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
            Term::Inl { val, .. } => {
                Some(case_l.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(val))))
            }
            Term::Inr { val, .. } => {
                Some(case_r.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(val))))
            }
            _ => step_term_delta(scrut, gamma, defs).map(|s| Term::Case {
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
            Term::Pair { snd, .. } => Some((**snd).clone()),
            _ => step_term_delta(pair, gamma, defs).map(|p| Term::Snd {
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
            _ => step_term_delta(scrut, gamma, defs).map(|s| Term::ElimW {
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
            _ => step_term_delta(scrut, gamma, defs).map(|s| Term::ElimWf {
                level: level.clone(),
                motive_level: motive_level.clone(),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
                motive: Rc::clone(motive),
                step: Rc::clone(step),
                scrut: Rc::new(s),
            }),
        },
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => match &**fun {
            // app(λx. t; …; s) ⇝ t[s/x]
            Term::Lam { body, .. } => {
                Some(body.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg))))
            }
            _ => step_term_delta(fun, gamma, defs).map(|f| Term::App {
                fun: Rc::new(f),
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
                arg: Rc::clone(arg),
            }),
        },
        Term::UApp { fun, levels } => match &**fun {
            // (Λ ℓ⃗. t) $ l⃗ ⇝ t[l⃗/ℓ⃗]; the written vectors pair positionally
            // (outermost first), instantiation wants innermost-first.
            Term::ULam { num_vars, body, .. } if *num_vars as usize == levels.len() => {
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                Some(body.inst_univ(&phi))
            }
            Term::ULam { .. } => None, // arity mismatch: ill-typed, stuck
            _ => step_term_delta(fun, gamma, defs)
                .map(|f| Term::UApp { fun: Rc::new(f), levels: levels.clone() }),
        },
        Term::CtxApp { fun, ctx } => match &**fun {
            // (Λ g. t) @ Δ ⇝ t[Δ/g]
            Term::CtxLam { body, .. } => {
                Some(body.apply_global(&GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()))))
            }
            _ => step_term_delta(fun, gamma, defs)
                .map(|f| Term::CtxApp { fun: Rc::new(f), ctx: ctx.clone() }),
        },
        Term::TyApp { fun, arg } => match &**fun {
            // (Λ U. t) @ T ⇝ t[T/U]
            Term::TyLam { body, .. } => {
                Some(body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)))))
            }
            _ => step_term_delta(fun, gamma, defs)
                .map(|f| Term::TyApp { fun: Rc::new(f), arg: Rc::clone(arg) }),
        },
        Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
            match &**scrut {
                // letbox … (box T) ⇝ t'[T/U]
                Term::BoxTy(code) => Some(
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(code)))),
                ),
                _ => step_term_delta(scrut, gamma, defs).map(|s| Term::LetBoxTy {
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
                _ => step_term_delta(scrut, gamma, defs).map(|s| Term::LetBoxTm {
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
                _ => step_term_delta(scrut, gamma, defs).map(|s| Term::ElimCodeTy {
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
            if let Some(ty) = step_type_delta(ty, ctx, defs) {
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
                _ => step_term_delta(scrut, gamma, defs).map(|s| Term::ElimCodeTm {
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
    /// evaluator shares these functions rather than transcribing the 56
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
        Term::Zero | Term::NatLit(0) => Some(fire(
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
            let pred = Rc::new(if *n == 1 { Term::Zero } else { Term::NatLit(n - 1) });
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
        // (ℓ, ℓ', g, U_I, U_P, u_a, u_b, u_e, u_t, x_I, x_P, x_a, x_b, x_e,
        // x_t. t_transp) — tm_j with the motive over one binder; globals in
        // Term::Transp field order; the proof is recursed like any subterm.
        Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
            let s_ty = rec.elim_ty(ty_level.clone(), delta.clone(), Rc::clone(ty));
            let dx = extend(delta, Rc::clone(ty), ty_level.clone());
            let s_motive = rec.elim_ty(motive_level.clone(), dx, Rc::clone(motive));
            let s_lhs =
                rec.elim_tm(ty_level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(lhs));
            let s_rhs =
                rec.elim_tm(ty_level.clone(), delta.clone(), Rc::clone(ty), Rc::clone(rhs));
            let seq_ty = Rc::new(Type::SEq {
                level: ty_level.clone(),
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            });
            let s_proof =
                rec.elim_tm(ty_level.clone(), delta.clone(), seq_ty, Rc::clone(proof));
            let motive_at_lhs =
                motive.apply_local(&LocalSubst::id(delta).extended(Rc::clone(lhs)));
            let s_tm = rec.elim_tm(
                motive_level.clone(),
                delta.clone(),
                Rc::new(motive_at_lhs),
                Rc::clone(tm),
            );
            Some(fire(
                &b.tm_transp,
                &[motive_level.clone(), ty_level.clone()],
                vec![
                    GlobalEntry::Ctx(delta.clone()),
                    GlobalEntry::Ty(Rc::clone(ty)),
                    GlobalEntry::Ty(Rc::clone(motive)),
                    GlobalEntry::Tm(Rc::clone(lhs)),
                    GlobalEntry::Tm(Rc::clone(rhs)),
                    GlobalEntry::Tm(Rc::clone(proof)),
                    GlobalEntry::Tm(Rc::clone(tm)),
                ],
                vec![s_ty, s_motive, s_lhs, s_rhs, s_proof, s_tm],
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
        // conversion compares such `Vec`/`Fin` structurally (extension).
        Type::Vec { len, .. } | Type::Fin { len } => is_neutral_term(len),
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
        | Type::Ty(_)
        | Type::UPi { .. }
        | Type::CtxPi { .. }
        | Type::TyPi { .. }
        | Type::CodeTy { .. }
        | Type::CodeTm { .. } => true,
        Type::El { .. } | Type::GlobalTy { .. } => is_neutral_type(t),
        // Vec/Fin step on a *canonical* length, so they are normal exactly
        // when the length is stuck (extension; docs/wf-former-design.md §1).
        Type::Vec { len, .. } | Type::Fin { len } => is_neutral_term(len),
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
        Term::J { proof, .. } => is_neutral_term(proof),
        // For *reduction* purposes a transp is stuck exactly when its proof
        // is (β fires on srefl only); conversion additionally strips it when
        // the endpoints convert, but that is conv.rs's business, not a
        // reduction (docs/sprop-design.md §5.2).
        Term::Transp { proof, .. } => is_neutral_term(proof),
        Term::ElimSEmpty { scrut, .. } => is_neutral_term(scrut),
        Term::ElimSquash { scrut, .. } => is_neutral_term(scrut),
        Term::Fst { pair, .. } | Term::Snd { pair, .. } => is_neutral_term(pair),
        Term::App { fun, .. }
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
        | Term::Zero
        | Term::Succ(_)
        | Term::Refl { .. }
        | Term::SRefl { .. }
        | Term::Squash { .. }
        | Term::Pair { .. }
        | Term::Triv { .. }
        | Term::Inl { .. }
        | Term::Inr { .. }
        | Term::Sup { .. }
        | Term::Supf { .. }
        | Term::Lam { .. }
        | Term::ULam { .. }
        | Term::CtxLam { .. }
        | Term::TyLam { .. }
        | Term::BoxTy(_)
        | Term::BoxTm(_) => true,
        _ => is_neutral_term(t),
    }
}
