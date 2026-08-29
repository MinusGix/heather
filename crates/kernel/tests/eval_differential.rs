//! **Differential test: the evaluator against the rewriter**
//! (docs/nbe-conversion-design.md §§2, 11.2, 13 stage 1).
//!
//! `reduce.rs` is ch. 06's reduction relation transcribed rule for rule; it
//! is the *specification*. `eval.rs` is the environment machine that will
//! replace it on the conversion path. This suite is the standing evidence
//! that the machine decides the same relation — the first test in the repo
//! that pits two kernel implementations against each other.
//!
//! ## What agreement means here
//!
//! The design's machine-adequacy statement (§11.2) relates a value `v` to a
//! ch. 06 weak head normal form `w` by induction on the head constructor:
//! heads agree, non-binder children are related pointwise, a closure is
//! related to a body when applying it to a value related to a term yields
//! something related to the whnf of the substituted body, a box's payload is
//! syntactically equal, and a neutral's spine is related eliminator-wise
//! over an identical head.
//!
//! [`Agree`] is the strongest *checkable* form of that: it compares head
//! constructors and every child, descends **under binders by applying the
//! closure to a fresh neutral variable** while the syntax side pushes the
//! matching context entry (the mechanism conversion itself will use in stage
//! 2b, so 2b inherits tested machinery), and it bounds the recursion at
//! [`DEPTH`] — an unbounded relation is not a decidable test, and the
//! sub-values at greater depth are reached anyway by other seeds and other
//! roots.
//!
//! Under the binder the two sides use *different index spaces* — the value
//! resolves through its environment, the term through the substitution the
//! rewriter performed — and that is exactly the point: the only place the
//! two must coincide is where a value bottoms out at [`Head::Var`], whose de
//! Bruijn **level** must be the syntax's `Γ.len() - 1 - i` ([`Head::BaseVar`]
//! for the abstract prefix). That single equation is the two-part variable
//! identity of design §3.2, and it is what these open-term cases pin.
//!
//! ## What it does not prove
//!
//! Nothing about sharing. `subst_laws.rs` makes this point about itself and
//! the design repeats it (§2): `eval` could agree on every value and still be
//! exponential. Only the acceptance instrument (`scripts/probe-whnf-sharing`)
//! measures the exponent.
//!
//! Failures report **seeds only**. A disagreeing pair is precisely the kind
//! of term that OOMs a machine if Debug-formatted, and 300 of them would do
//! it 300 times.

mod common;

use std::rc::Rc;

use common::wt::{
    gen_wt_ctx, gen_wt_env, gen_wt_term, gen_wt_term_at, gen_wt_type, identity_branches,
    identity_motives, perturb_conv, FUEL,
};
use common::Rng;
use heather_kernel::eval::Eval;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{whnf_term_delta, whnf_type_delta, Defs};
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::value::{
    Elim, Env, Head, TmClo, TyClo, VNeTy, VNeutral, VSubst, VTail, VTy, Val,
    ValueArena,
};

/// Cases per seed stream. Five streams over `wt.rs`'s generator; the schedule
/// matters more than the count (`ch05_06_lemmas.rs` found a real generator
/// defect at ~1-in-3000 by varying the schedule), so the streams differ in
/// both their seed mixer and what they build on top of the generated triple.
/// The whole file is ~0.25 s in a debug profile — it is cheap because both
/// sides are weak-head, not normalizing.
const CASES: u64 = 600;

/// Generator budget: how deep a well-typed term `wt.rs` synthesizes.
const BUDGET: u32 = 8;

/// How far the agreement relation recurses through forcing. Every level
/// multiplies the work by the branching factor of the value.
const DEPTH: u32 = 5;

// ---------------------------------------------------------------------------
// The agreement relation
// ---------------------------------------------------------------------------

struct Agree<'a, 'v> {
    ev: Eval<'a, 'v>,
    defs: Defs<'a>,
    arena: &'v ValueArena<'v>,
}

type A = Result<(), String>;

fn ok() -> A {
    Ok(())
}

fn bad(what: &str) -> A {
    Err(what.to_string())
}

/// Extend Γ by `k` binders and produce the matching fresh neutral variables.
///
/// The entry types are fillers: weak-head reduction reads only Γ's *shape*
/// (length and base) — `reduce.rs`'s module doc says so, and `LocalSubst::id`
/// is the only consumer.
fn fresh<'v>(arena: &'v ValueArena<'v>, gamma: &LocalCtx, k: u32) -> (LocalCtx, Vec<&'v TmClo<'v>>) {
    let n = gamma.entries.len() as u32;
    let mut g = gamma.clone();
    let mut args = Vec::with_capacity(k as usize);
    for j in 0..k {
        g.entries.push(CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero });
        args.push(arena.tm(TmClo::val(Rc::new(Val::var(n + j)))));
    }
    (g, args)
}

impl<'a, 'v> Agree<'a, 'v> {
    fn new(
        psi: &'a GlobalCtx,
        transparent: bool,
        gamma: &LocalCtx,
        arena: &'v ValueArena<'v>,
    ) -> Agree<'a, 'v> {
        let defs = if transparent { Defs::transparent(psi) } else { Defs::opaque() };
        Agree { ev: Eval::new(FUEL, defs, gamma.base, arena), defs, arena }
    }

    fn lev(&self, a: &Level, b: &Level, what: &'static str) -> A {
        if a.equiv(b) { ok() } else { bad(what) }
    }

    // -- forcing on both sides ---------------------------------------------

    /// A 0-binder term sub-structure against its syntax.
    fn lazy_tm(&mut self, c: &'v TmClo<'v>, t: &Term, gamma: &LocalCtx, depth: u32) -> A {
        if depth == 0 {
            return ok();
        }
        let v = self.ev.force(c).map_err(|_| "evaluator out of fuel".to_string())?;
        let v = self.ev.delta_whnf(v).map_err(|_| "evaluator out of fuel".to_string())?;
        self.tm(&v, t, gamma, depth)
    }

    /// A term closure with `k` pending binders against the syntax of its
    /// body, in Γ extended by `k`.
    fn under_tm(
        &mut self,
        c: &'v TmClo<'v>,
        t: &Term,
        gamma: &LocalCtx,
        k: u32,
        depth: u32,
    ) -> A {
        if depth == 0 {
            return ok();
        }
        let (g, args) = fresh(self.arena, gamma, k);
        let v = self.ev.apply(c, &args).map_err(|_| "evaluator out of fuel".to_string())?;
        let v = self.ev.delta_whnf(v).map_err(|_| "evaluator out of fuel".to_string())?;
        self.tm(&v, t, &g, depth)
    }

    fn lazy_ty(&mut self, c: &'v TyClo<'v>, t: &Type, gamma: &LocalCtx, depth: u32) -> A {
        if depth == 0 {
            return ok();
        }
        let v = self.ev.force_ty(c).map_err(|_| "evaluator out of fuel".to_string())?;
        let v = self.ev.delta_whnf_ty(v).map_err(|_| "evaluator out of fuel".to_string())?;
        self.ty(&v, t, gamma, depth)
    }

    fn under_ty(
        &mut self,
        c: &'v TyClo<'v>,
        t: &Type,
        gamma: &LocalCtx,
        k: u32,
        depth: u32,
    ) -> A {
        if depth == 0 {
            return ok();
        }
        let (g, args) = fresh(self.arena, gamma, k);
        let v = self.ev.apply_ty(c, &args).map_err(|_| "evaluator out of fuel".to_string())?;
        let v = self.ev.delta_whnf_ty(v).map_err(|_| "evaluator out of fuel".to_string())?;
        self.ty(&v, t, &g, depth)
    }

    // -- types --------------------------------------------------------------

    /// `v ⊩ whnf(t)` for types.
    pub fn ty(&mut self, v: &Rc<VTy<'v>>, t: &Type, gamma: &LocalCtx, depth: u32) -> A {
        if depth == 0 {
            return ok();
        }
        let d = depth - 1;
        let w = whnf_type_delta(t, gamma, self.defs, FUEL)
            .map_err(|_| "rewriter out of fuel (type)".to_string())?;
        match (&**v, &w) {
            (VTy::Nat, Type::Nat) => ok(),
            (VTy::Ty(a), Type::Ty(b)) => self.lev(a, b, "Ty level"),
            (VTy::Unit { level: a }, Type::Unit { level: b })
            | (VTy::Empty { level: a }, Type::Empty { level: b })
            | (VTy::SEmpty { level: a }, Type::SEmpty { level: b }) => {
                self.lev(a, b, "nullary former level")
            }
            (
                VTy::Pi { dom_level: a1, cod_level: a2, dom, cod },
                Type::Pi { dom_level: b1, cod_level: b2, dom: d2, cod: c2 },
            ) => {
                self.lev(a1, b1, "Π dom level")?;
                self.lev(a2, b2, "Π cod level")?;
                self.lazy_ty(dom, d2, gamma, d)?;
                self.under_ty(cod, c2, gamma, 1, d)
            }
            (
                VTy::Sigma { fst_level: a1, snd_level: a2, fst, snd },
                Type::Sigma { fst_level: b1, snd_level: b2, fst: f2, snd: s2 },
            ) => {
                self.lev(a1, b1, "Σ fst level")?;
                self.lev(a2, b2, "Σ snd level")?;
                self.lazy_ty(fst, f2, gamma, d)?;
                self.under_ty(snd, s2, gamma, 1, d)
            }
            (
                VTy::W { shape_level: a1, pos_level: a2, shape, pos },
                Type::W { shape_level: b1, pos_level: b2, shape: s2, pos: p2 },
            ) => {
                self.lev(a1, b1, "W shape level")?;
                self.lev(a2, b2, "W pos level")?;
                self.lazy_ty(shape, s2, gamma, d)?;
                self.under_ty(pos, p2, gamma, 1, d)
            }
            (
                VTy::Wf { level: a, shape, arity },
                Type::Wf { level: b, shape: s2, arity: n2 },
            ) => {
                self.lev(a, b, "Wf level")?;
                self.lazy_ty(shape, s2, gamma, d)?;
                self.under_tm(arity, n2, gamma, 1, d)
            }
            (
                VTy::Sum { lhs_level: a1, rhs_level: a2, lhs, rhs },
                Type::Sum { lhs_level: b1, rhs_level: b2, lhs: l2, rhs: r2 },
            ) => {
                self.lev(a1, b1, "+ lhs level")?;
                self.lev(a2, b2, "+ rhs level")?;
                self.lazy_ty(lhs, l2, gamma, d)?;
                self.lazy_ty(rhs, r2, gamma, d)
            }
            (
                VTy::Id { level: a, ty, lhs, rhs },
                Type::Id { level: b, ty: t2, lhs: l2, rhs: r2 },
            )
            | (
                VTy::SEq { level: a, ty, lhs, rhs },
                Type::SEq { level: b, ty: t2, lhs: l2, rhs: r2 },
            ) => {
                self.lev(a, b, "Id/sEq level")?;
                self.lazy_ty(ty, t2, gamma, d)?;
                self.lazy_tm(lhs, l2, gamma, d)?;
                self.lazy_tm(rhs, r2, gamma, d)
            }
            (
                VTy::Vec { level: a, elem, len },
                Type::Vec { level: b, elem: e2, len: k2 },
            ) => {
                self.lev(a, b, "Vec level")?;
                self.lazy_ty(elem, e2, gamma, d)?;
                self.tm(&Rc::clone(len), k2, gamma, d)
            }
            (VTy::Fin { len }, Type::Fin { len: k2 }) => {
                self.tm(&Rc::clone(len), k2, gamma, d)
            }
            // Universe/global binders: entered by instantiation, at a closed
            // payload so that neither side needs a scope extension.
            (
                VTy::UPi { num_vars: a, level: la, body },
                Type::UPi { num_vars: b, level: lb, body: b2 },
            ) => {
                if a != b {
                    return bad("ΠΠ arity");
                }
                self.lev(la, lb, "ΠΠ level")?;
                let phi = vec![Level::Zero; *a as usize];
                let Some((benv, bbody)) = body.as_syn() else {
                    return bad("ΠΠ body is not a syntactic closure");
                };
                let vb = self
                    .ev
                    .eval_ty(&Rc::new(bbody.inst_univ(&phi)), &benv.clone())
                    .map_err(|_| "evaluator out of fuel".to_string())?;
                let vb = self
                    .ev
                    .delta_whnf_ty(vb)
                    .map_err(|_| "evaluator out of fuel".to_string())?;
                self.ty(&vb, &b2.inst_univ(&phi), gamma, d)
            }
            (VTy::CtxPi { level: la, body }, Type::CtxPi { level: lb, body: b2 }) => {
                self.lev(la, lb, "(g:Ctx)⇒ level")?;
                let payload = GlobalEntry::Ctx(LocalCtx::nil());
                self.instantiated_ty(body, b2, payload, gamma, d)
            }
            (
                VTy::TyPi { ctx: ca, arg_level: aa, body_level: ba, body },
                Type::TyPi { ctx: cb, arg_level: ab, body_level: bb, body: b2 },
            ) => {
                if ca != cb {
                    return bad("(U:Typ)⇒ index context");
                }
                self.lev(aa, ab, "(U:Typ)⇒ arg level")?;
                self.lev(ba, bb, "(U:Typ)⇒ body level")?;
                let payload = GlobalEntry::Ty(Rc::new(Type::Nat));
                self.instantiated_ty(body, b2, payload, gamma, d)
            }
            (
                VTy::CodeTy { ctx: ca, level: la },
                Type::CodeTy { ctx: cb, level: lb },
            ) => {
                if ca != cb {
                    return bad("□(Δ ⊢ Ty l) context");
                }
                self.lev(la, lb, "□(Δ ⊢ Ty l) level")
            }
            (
                VTy::CodeTm { ctx: ca, ty: ta, level: la },
                Type::CodeTm { ctx: cb, ty: tb, level: lb },
            ) => {
                if ca != cb || ta != tb {
                    return bad("□(Δ ⊢ T @ l) context/type");
                }
                self.lev(la, lb, "□(Δ ⊢ T @ l) level")
            }
            (
                VTy::Neutral(VNeTy::Global { var: a, subst: sa }),
                Type::GlobalTy { var: b, subst: sb },
            ) => {
                if a != b {
                    return bad("U^δ index");
                }
                self.subst(sa, sb, gamma, d)
            }
            (VTy::Neutral(VNeTy::El { level: a, tm }), Type::El { level: b, tm: t2 }) => {
                self.lev(a, b, "El level")?;
                self.tm(&Rc::clone(tm), t2, gamma, d)
            }
            _ => bad("type head constructor"),
        }
    }

    /// Enter a global binder on both sides with the same payload.
    fn instantiated_ty(
        &mut self,
        body: &'v TyClo<'v>,
        syn: &Type,
        payload: GlobalEntry,
        gamma: &LocalCtx,
        depth: u32,
    ) -> A {
        let sigma = GlobalSubst::single(payload);
        let Some((benv, bbody)) = body.as_syn() else {
            return bad("instantiated body is not a syntactic closure");
        };
        let (benv, bbody) = (benv.clone(), Rc::clone(bbody));
        let vb = self
            .ev
            .eval_ty(&Rc::new(bbody.apply_global(&sigma)), &benv)
            .map_err(|_| "evaluator out of fuel".to_string())?;
        let vb = self.ev.delta_whnf_ty(vb).map_err(|_| "evaluator out of fuel".to_string())?;
        self.ty(&vb, &syn.apply_global(&sigma), gamma, depth)
    }

    /// `δ ⊩ δ'` — pairwise on the step terms over identical tails.
    fn subst(&mut self, a: &VSubst<'v>, b: &LocalSubst, gamma: &LocalCtx, depth: u32) -> A {
        // The value's tail drops δ̂ and normalizes `·`'s base, because a
        // machine that substitutes nothing cannot renormalize them; see
        // [`VTail`]. Everything the tail still distinguishes is compared.
        if a.tail != VTail::of(b.tail, gamma.base) || a.terms.len() != b.terms.len() {
            return bad("δ tail/arity");
        }
        if depth == 0 {
            return ok();
        }
        for (va, tb) in a.terms.iter().zip(&b.terms) {
            let v = self
                .ev
                .delta_whnf(Rc::clone(va))
                .map_err(|_| "evaluator out of fuel".to_string())?;
            self.tm(&v, tb, gamma, depth)?;
        }
        ok()
    }

    // -- terms --------------------------------------------------------------

    /// `v ⊩ whnf(t)` for terms.
    pub fn tm(&mut self, v: &Rc<Val<'v>>, t: &Term, gamma: &LocalCtx, depth: u32) -> A {
        if depth == 0 {
            return ok();
        }
        let d = depth - 1;
        let w = whnf_term_delta(t, gamma, self.defs, FUEL)
            .map_err(|_| "rewriter out of fuel (term)".to_string())?;
        match (&**v, &w) {
            // -- encodings --
            (Val::TmNat, Term::TmNat) => ok(),
            (Val::TmTy(a), Term::TmTy(b)) => self.lev(a, b, "`Ty level"),
            (Val::TmUnit { level: a }, Term::TmUnit { level: b })
            | (Val::TmEmpty { level: a }, Term::TmEmpty { level: b })
            | (Val::TmSEmpty { level: a }, Term::TmSEmpty { level: b }) => {
                self.lev(a, b, "nullary encoding level")
            }
            (
                Val::TmPi { dom_level: a1, cod_level: a2, dom, cod },
                Term::TmPi { dom_level: b1, cod_level: b2, dom: d2, cod: c2 },
            )
            | (
                Val::TmSigma { fst_level: a1, snd_level: a2, fst: dom, snd: cod },
                Term::TmSigma { fst_level: b1, snd_level: b2, fst: d2, snd: c2 },
            )
            | (
                Val::TmW { shape_level: a1, pos_level: a2, shape: dom, pos: cod },
                Term::TmW { shape_level: b1, pos_level: b2, shape: d2, pos: c2 },
            ) => {
                self.lev(a1, b1, "encoding dom level")?;
                self.lev(a2, b2, "encoding cod level")?;
                self.lazy_tm(dom, d2, gamma, d)?;
                self.under_tm(cod, c2, gamma, 1, d)
            }
            (
                Val::TmWf { level: a, shape, arity },
                Term::TmWf { level: b, shape: s2, arity: n2 },
            ) => {
                self.lev(a, b, "`Wf level")?;
                self.lazy_tm(shape, s2, gamma, d)?;
                self.under_tm(arity, n2, gamma, 1, d)
            }
            (
                Val::TmId { level: a, ty, lhs, rhs },
                Term::TmId { level: b, ty: t2, lhs: l2, rhs: r2 },
            )
            | (
                Val::TmSEq { level: a, ty, lhs, rhs },
                Term::TmSEq { level: b, ty: t2, lhs: l2, rhs: r2 },
            ) => {
                self.lev(a, b, "`Id/`sEq level")?;
                self.lazy_tm(ty, t2, gamma, d)?;
                self.lazy_tm(lhs, l2, gamma, d)?;
                self.lazy_tm(rhs, r2, gamma, d)
            }
            (
                Val::TmSum { lhs_level: a1, rhs_level: a2, lhs, rhs },
                Term::TmSum { lhs_level: b1, rhs_level: b2, lhs: l2, rhs: r2 },
            ) => {
                self.lev(a1, b1, "`+ lhs level")?;
                self.lev(a2, b2, "`+ rhs level")?;
                self.lazy_tm(lhs, l2, gamma, d)?;
                self.lazy_tm(rhs, r2, gamma, d)
            }
            (
                Val::TmVec { level: a, elem, len },
                Term::TmVec { level: b, elem: e2, len: k2 },
            ) => {
                self.lev(a, b, "`Vec level")?;
                self.lazy_tm(elem, e2, gamma, d)?;
                self.lazy_tm(len, k2, gamma, d)
            }
            (Val::TmFin { len }, Term::TmFin { len: k2 }) => self.lazy_tm(len, k2, gamma, d),

            // -- data --
            (Val::Zero, Term::Zero) => ok(),
            (Val::Succ(a), Term::Succ(b)) => self.lazy_tm(a, b, gamma, d),
            (Val::NatRun { program, tail }, Term::Succ(b)) => {
                let pred = Val::nat_run_pred(self.arena, program, tail);
                self.lazy_tm(pred, b, gamma, d)
            }
            (Val::Refl { level: a, ty, tm }, Term::Refl { level: b, ty: t2, tm: m2 })
            | (Val::SRefl { level: a, ty, tm }, Term::SRefl { level: b, ty: t2, tm: m2 }) => {
                self.lev(a, b, "refl level")?;
                self.lazy_ty(ty, t2, gamma, d)?;
                self.lazy_tm(tm, m2, gamma, d)
            }
            (
                Val::Pair { fst_level: a1, snd_level: a2, fst_ty, snd_ty, fst, snd },
                Term::Pair {
                    fst_level: b1,
                    snd_level: b2,
                    fst_ty: ft2,
                    snd_ty: st2,
                    fst: f2,
                    snd: s2,
                },
            ) => {
                self.lev(a1, b1, "pair fst level")?;
                self.lev(a2, b2, "pair snd level")?;
                self.lazy_ty(fst_ty, ft2, gamma, d)?;
                self.under_ty(snd_ty, st2, gamma, 1, d)?;
                self.lazy_tm(fst, f2, gamma, d)?;
                self.lazy_tm(snd, s2, gamma, d)
            }
            (Val::Triv { level: a }, Term::Triv { level: b }) => self.lev(a, b, "⟨⟩ level"),
            (
                Val::Inl { lhs_level: a1, rhs_level: a2, lhs, rhs, val },
                Term::Inl { lhs_level: b1, rhs_level: b2, lhs: l2, rhs: r2, val: v2 },
            )
            | (
                Val::Inr { lhs_level: a1, rhs_level: a2, lhs, rhs, val },
                Term::Inr { lhs_level: b1, rhs_level: b2, lhs: l2, rhs: r2, val: v2 },
            ) => {
                self.lev(a1, b1, "inj lhs level")?;
                self.lev(a2, b2, "inj rhs level")?;
                self.lazy_ty(lhs, l2, gamma, d)?;
                self.lazy_ty(rhs, r2, gamma, d)?;
                self.lazy_tm(val, v2, gamma, d)
            }
            (
                Val::Sup { shape_level: a1, pos_level: a2, shape_ty, pos_ty, label, children },
                Term::Sup {
                    shape_level: b1,
                    pos_level: b2,
                    shape_ty: s2,
                    pos_ty: p2,
                    label: l2,
                    children: c2,
                },
            ) => {
                self.lev(a1, b1, "sup shape level")?;
                self.lev(a2, b2, "sup pos level")?;
                self.lazy_ty(shape_ty, s2, gamma, d)?;
                self.under_ty(pos_ty, p2, gamma, 1, d)?;
                self.lazy_tm(label, l2, gamma, d)?;
                self.lazy_tm(children, c2, gamma, d)
            }
            (
                Val::Supf { level: a, shape, arity, label, children },
                Term::Supf { level: b, shape: s2, arity: n2, label: l2, children: c2 },
            ) => {
                self.lev(a, b, "sup_f level")?;
                self.lazy_ty(shape, s2, gamma, d)?;
                self.under_tm(arity, n2, gamma, 1, d)?;
                self.lazy_tm(label, l2, gamma, d)?;
                self.lazy_tm(children, c2, gamma, d)
            }

            // -- functions: the closure case of the adequacy relation --
            (
                Val::Lam { dom_level: a1, cod_level: a2, dom, body },
                Term::Lam { dom_level: b1, cod_level: b2, dom: d2, body: b3 },
            ) => {
                self.lev(a1, b1, "λ dom level")?;
                self.lev(a2, b2, "λ cod level")?;
                self.lazy_ty(dom, d2, gamma, d)?;
                self.under_tm(body, b3, gamma, 1, d)
            }
            (
                Val::ULam { num_vars: a, level: la, body },
                Term::ULam { num_vars: b, level: lb, body: b2 },
            ) => {
                if a != b {
                    return bad("Λℓ⃗ arity");
                }
                self.lev(la, lb, "Λℓ⃗ level")?;
                let levels = vec![Level::Zero; *a as usize];
                let vb = self
                    .ev
                    .elim(Rc::clone(v), Elim::UApp { levels: levels.clone() })
                    .map_err(|_| "evaluator out of fuel".to_string())?;
                let vb =
                    self.ev.delta_whnf(vb).map_err(|_| "evaluator out of fuel".to_string())?;
                let _ = (body, b2);
                let syn = Term::UApp { fun: Rc::new(w.clone()), levels };
                self.tm(&vb, &syn, gamma, d)
            }
            (Val::CtxLam { level: la, body }, Term::CtxLam { level: lb, body: b2 }) => {
                self.lev(la, lb, "Λ(g) level")?;
                let _ = (body, b2);
                let vb = self
                    .ev
                    .elim(
                        Rc::clone(v),
                        Elim::CtxApp { ctx: LocalCtx::nil() },
                    )
                    .map_err(|_| "evaluator out of fuel".to_string())?;
                let vb =
                    self.ev.delta_whnf(vb).map_err(|_| "evaluator out of fuel".to_string())?;
                let syn = Term::CtxApp {
                    fun: Rc::new(w.clone()),
                    ctx: LocalCtx::nil(),
                };
                self.tm(&vb, &syn, gamma, d)
            }
            (
                Val::TyLam { ctx: ca, arg_level: aa, body_level: ba, body },
                Term::TyLam { ctx: cb, arg_level: ab, body_level: bb, body: b2 },
            ) => {
                if ca != cb {
                    return bad("Λ(U) index context");
                }
                self.lev(aa, ab, "Λ(U) arg level")?;
                self.lev(ba, bb, "Λ(U) body level")?;
                let _ = (body, b2);
                let arg: Rc<Type> = Rc::new(Type::Nat);
                let vb = self
                    .ev
                    .elim(Rc::clone(v), Elim::TyApp { arg: Rc::clone(&arg) })
                    .map_err(|_| "evaluator out of fuel".to_string())?;
                let vb =
                    self.ev.delta_whnf(vb).map_err(|_| "evaluator out of fuel".to_string())?;
                let syn = Term::TyApp { fun: Rc::new(w.clone()), arg };
                self.tm(&vb, &syn, gamma, d)
            }

            // -- code: syntactic equality, no environment anywhere near it --
            (Val::BoxTy(a), Term::BoxTy(b)) => {
                if a == b {
                    ok()
                } else {
                    bad("box type payload")
                }
            }
            (Val::BoxTm(a), Term::BoxTm(b)) => {
                if a == b {
                    ok()
                } else {
                    bad("box term payload")
                }
            }

            (Val::Neutral(n), _) => self.ne(n, &w, gamma, depth),
            _ => bad("term head constructor"),
        }
    }

    /// A neutral value against a neutral term: peel the spine from the
    /// outside, matching the syntax's outermost eliminator each time.
    fn ne(&mut self, n: &Rc<VNeutral<'v>>, w: &Term, gamma: &LocalCtx, depth: u32) -> A {
        if depth == 0 {
            return ok();
        }
        let d = depth - 1;
        let Some((last, rest)) = n.spine.split_last() else {
            return self.head(&n.head, w, gamma, d);
        };
        // The prefix of a glued neutral is never itself glued: its head is
        // the same head, and `delta_whnf` has already forced any definition
        // at it (that is what makes this recursion well-founded against a
        // δ-reduced syntax side).
        let prefix = Rc::new(VNeutral {
            head: n.head.clone(),
            spine: rest.to_vec(),
            unfold: None,
        });
        match (last, w) {
            (
                Elim::App { dom_level: a1, cod_level: a2, dom, cod, arg },
                Term::App {
                    fun,
                    dom_level: b1,
                    cod_level: b2,
                    dom: d2,
                    cod: c2,
                    arg: g2,
                },
            ) => {
                self.lev(a1, b1, "app dom level")?;
                self.lev(a2, b2, "app cod level")?;
                self.lazy_ty(dom, d2, gamma, d)?;
                self.under_ty(cod, c2, gamma, 1, d)?;
                self.lazy_tm(arg, g2, gamma, d)?;
                self.ne(&prefix, fun, gamma, depth)
            }
            (Elim::UApp { levels: a }, Term::UApp { fun, levels: b }) => {
                if a.len() != b.len() || !a.iter().zip(b).all(|(x, y)| x.equiv(y)) {
                    return bad("$ levels");
                }
                self.ne(&prefix, fun, gamma, depth)
            }
            (Elim::CtxApp { ctx: a }, Term::CtxApp { fun, ctx: b }) => {
                if a != b {
                    return bad("@Δ context");
                }
                self.ne(&prefix, fun, gamma, depth)
            }
            (Elim::TyApp { arg: a }, Term::TyApp { fun, arg: b }) => {
                if a != b {
                    return bad("@T type");
                }
                self.ne(&prefix, fun, gamma, depth)
            }
            (
                Elim::Fst { fst_level: a1, snd_level: a2, fst_ty, snd_ty },
                Term::Fst {
                    fst_level: b1,
                    snd_level: b2,
                    fst_ty: f2,
                    snd_ty: s2,
                    pair,
                },
            )
            | (
                Elim::Snd { fst_level: a1, snd_level: a2, fst_ty, snd_ty },
                Term::Snd {
                    fst_level: b1,
                    snd_level: b2,
                    fst_ty: f2,
                    snd_ty: s2,
                    pair,
                },
            ) => {
                self.lev(a1, b1, "proj fst level")?;
                self.lev(a2, b2, "proj snd level")?;
                self.lazy_ty(fst_ty, f2, gamma, d)?;
                self.under_ty(snd_ty, s2, gamma, 1, d)?;
                self.ne(&prefix, pair, gamma, depth)
            }
            (
                Elim::ElimNat { level: a, motive, base, step },
                Term::ElimNat { level: b, motive: m2, base: z2, step: s2, scrut },
            ) => {
                self.lev(a, b, "elim_Nat level")?;
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.lazy_tm(base, z2, gamma, d)?;
                self.under_tm(step, s2, gamma, 2, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::ElimEmpty { level: a, scrut_level: a2, motive },
                Term::ElimEmpty { level: b, scrut_level: b2, motive: m2, scrut },
            )
            | (
                Elim::ElimSEmpty { level: a, scrut_level: a2, motive },
                Term::ElimSEmpty { level: b, scrut_level: b2, motive: m2, scrut },
            ) => {
                self.lev(a, b, "elim_Empty motive level")?;
                self.lev(a2, b2, "elim_Empty scrutinee level")?;
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::Case {
                    lhs_level: a1,
                    rhs_level: a2,
                    motive_level: a3,
                    lhs,
                    rhs,
                    motive,
                    case_l,
                    case_r,
                },
                Term::Case {
                    lhs_level: b1,
                    rhs_level: b2,
                    motive_level: b3,
                    lhs: l2,
                    rhs: r2,
                    motive: m2,
                    case_l: cl2,
                    case_r: cr2,
                    scrut,
                },
            ) => {
                self.lev(a1, b1, "case lhs level")?;
                self.lev(a2, b2, "case rhs level")?;
                self.lev(a3, b3, "case motive level")?;
                self.lazy_ty(lhs, l2, gamma, d)?;
                self.lazy_ty(rhs, r2, gamma, d)?;
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.under_tm(case_l, cl2, gamma, 1, d)?;
                self.under_tm(case_r, cr2, gamma, 1, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::ElimW {
                    shape_level: a1,
                    pos_level: a2,
                    motive_level: a3,
                    shape,
                    pos,
                    motive,
                    step,
                    ..
                },
                Term::ElimW {
                    shape_level: b1,
                    pos_level: b2,
                    motive_level: b3,
                    shape: s2,
                    pos: p2,
                    motive: m2,
                    step: st2,
                    scrut,
                },
            ) => {
                self.lev(a1, b1, "elim_W shape level")?;
                self.lev(a2, b2, "elim_W pos level")?;
                self.lev(a3, b3, "elim_W motive level")?;
                self.lazy_ty(shape, s2, gamma, d)?;
                self.under_ty(pos, p2, gamma, 1, d)?;
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.under_tm(step, st2, gamma, 3, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::ElimWf { level: a1, motive_level: a2, shape, arity, motive, step, .. },
                Term::ElimWf {
                    level: b1,
                    motive_level: b2,
                    shape: s2,
                    arity: n2,
                    motive: m2,
                    step: st2,
                    scrut,
                },
            ) => {
                self.lev(a1, b1, "elim_Wf level")?;
                self.lev(a2, b2, "elim_Wf motive level")?;
                self.lazy_ty(shape, s2, gamma, d)?;
                self.under_tm(arity, n2, gamma, 1, d)?;
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.under_tm(step, st2, gamma, 3, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::J { ty_level: a1, motive_level: a2, ty, lhs, motive, case, rhs },
                Term::J {
                    ty_level: b1,
                    motive_level: b2,
                    ty: t2,
                    lhs: l2,
                    motive: m2,
                    case: c2,
                    rhs: r2,
                    proof,
                },
            ) => {
                self.lev(a1, b1, "J type level")?;
                self.lev(a2, b2, "J motive level")?;
                self.lazy_ty(ty, t2, gamma, d)?;
                self.lazy_tm(lhs, l2, gamma, d)?;
                self.under_ty(motive, m2, gamma, 2, d)?;
                self.lazy_tm(case, c2, gamma, d)?;
                self.lazy_tm(rhs, r2, gamma, d)?;
                self.ne(&prefix, proof, gamma, depth)
            }
            (
                Elim::Transp { ty_level: a1, motive_level: a2, ty, motive, lhs, rhs, tm },
                Term::Transp {
                    ty_level: b1,
                    motive_level: b2,
                    ty: t2,
                    motive: m2,
                    lhs: l2,
                    rhs: r2,
                    proof,
                    tm: x2,
                },
            ) => {
                self.lev(a1, b1, "transp type level")?;
                self.lev(a2, b2, "transp motive level")?;
                self.lazy_ty(ty, t2, gamma, d)?;
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.lazy_tm(lhs, l2, gamma, d)?;
                self.lazy_tm(rhs, r2, gamma, d)?;
                self.lazy_tm(tm, x2, gamma, d)?;
                self.ne(&prefix, proof, gamma, depth)
            }
            (
                Elim::LetBoxTy { motive_level: a1, code_level: a2, ctx: ca, motive, .. },
                Term::LetBoxTy {
                    motive_level: b1,
                    code_level: b2,
                    ctx: cb,
                    motive: m2,
                    scrut,
                    ..
                },
            ) => {
                self.lev(a1, b1, "letbox motive level")?;
                self.lev(a2, b2, "letbox code level")?;
                if ca != cb {
                    return bad("letbox context");
                }
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::LetBoxTm {
                    motive_level: a1,
                    code_level: a2,
                    ctx: ca,
                    ty: ta,
                    motive,
                    ..
                },
                Term::LetBoxTm {
                    motive_level: b1,
                    code_level: b2,
                    ctx: cb,
                    ty: tb,
                    motive: m2,
                    scrut,
                    ..
                },
            ) => {
                self.lev(a1, b1, "letbox motive level")?;
                self.lev(a2, b2, "letbox code level")?;
                if ca != cb || ta != tb {
                    return bad("letbox context/type");
                }
                self.under_ty(motive, m2, gamma, 1, d)?;
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::ElimCodeTy {
                    ty_motive_level: a1,
                    tm_motive_level: a2,
                    motives: ma,
                    branches: ba,
                    code_level: a3,
                    ctx: ca,
                    ..
                },
                Term::ElimCodeTy {
                    ty_motive_level: b1,
                    tm_motive_level: b2,
                    motives: mb,
                    branches: bb,
                    code_level: b3,
                    ctx: cb,
                    scrut,
                },
            ) => {
                self.lev(a1, b1, "elim^Typ ty motive level")?;
                self.lev(a2, b2, "elim^Typ tm motive level")?;
                self.lev(a3, b3, "elim^Typ code level")?;
                let _ = (ma, mb, ba, bb); // see the note above `head`
                if ca != cb {
                    return bad("elim^Typ context");
                }
                self.ne(&prefix, scrut, gamma, depth)
            }
            (
                Elim::ElimCodeTm {
                    ty_motive_level: a1,
                    tm_motive_level: a2,
                    motives: ma,
                    branches: ba,
                    code_level: a3,
                    ctx: ca,
                    ty: ta,
                    ..
                },
                Term::ElimCodeTm {
                    ty_motive_level: b1,
                    tm_motive_level: b2,
                    motives: mb,
                    branches: bb,
                    code_level: b3,
                    ctx: cb,
                    ty: tb,
                    scrut,
                },
            ) => {
                self.lev(a1, b1, "elim^Trm ty motive level")?;
                self.lev(a2, b2, "elim^Trm tm motive level")?;
                self.lev(a3, b3, "elim^Trm code level")?;
                let _ = (ma, mb, ba, bb); // see the note above `head`
                if ca != cb || ta != tb {
                    return bad("elim^Trm context/annotation");
                }
                self.ne(&prefix, scrut, gamma, depth)
            }
            _ => bad("neutral spine eliminator"),
        }
    }

    // Why the recursors' `motives`/`branches` are **not** compared here.
    //
    // They are the only Γ-scoped raw syntax a value carries: the motive and
    // branch telescopes extend Γ (as well as L and Ψ), so `apply_local`
    // descends into them (`subst.rs`'s `map_branches`) while `other_ty` /
    // `other_ctx` protect every *other* syntactic field — the Δ contexts,
    // the box payloads, `elim^Trm`'s annotation, `@Δ`, `@T`. So the rewriter
    // rewrites a neutral recursor's branches at every enclosing β and the
    // environment machine, having substituted nothing, does not. The two
    // agree only *through the elimination's environment*, which is why
    // [`Elim::ElimCodeTy`]/[`Elim::ElimCodeTm`] carry one.
    //
    // Comparing them here would need the branch telescopes' (univ, global,
    // local) arities and a matching scope extension on both sides — i.e.
    // `conv.rs`'s `rec_ca`, which stage 2b rewrites. Until then the standing
    // evidence for branch handling is [`stream4_code_recursors`], which
    // compares what the branches *compute*.

    /// The bottom of a spine: the head itself.
    fn head(&mut self, h: &Head<'v>, w: &Term, gamma: &LocalCtx, depth: u32) -> A {
        match (h, w) {
            // The two-part variable identity (design §3.2): a concrete entry
            // is a de Bruijn *level* from Γ's outer end, anything past the
            // concrete entries is a *depth* into the abstract prefix `g`.
            (Head::Var(lvl), Term::Var(LocalVar(i))) => {
                let n = gamma.entries.len() as u32;
                match n.checked_sub(1 + *i) {
                    Some(expect) if expect == *lvl => ok(),
                    _ => bad("local variable level"),
                }
            }
            (Head::BaseVar(depth_), Term::Var(LocalVar(i))) => {
                let n = gamma.entries.len() as u32;
                if *i >= n && *i - n == *depth_ {
                    ok()
                } else {
                    bad("abstract-prefix variable depth")
                }
            }
            (Head::Global { var: a, subst: sa }, Term::GlobalTm { var: b, subst: sb }) => {
                if a != b {
                    return bad("u^δ index");
                }
                self.subst(sa, sb, gamma, depth)
            }
            (Head::BoxedGlobalTy(a), Term::BoxTy(b)) => {
                if a == b {
                    ok()
                } else {
                    bad("blocked box(U^δ) payload")
                }
            }
            (Head::BoxedGlobalTm(a), Term::BoxTm(b)) => {
                if a == b {
                    ok()
                } else {
                    bad("blocked box(u^δ) payload")
                }
            }
            // Ill-typed stuck forms: `reduce.rs` is stuck too, but its stuck
            // shape is not a grammar the value domain mirrors. Well-typed
            // input never reaches here.
            (Head::Stuck(_), _) => ok(),
            _ => bad("neutral head"),
        }
    }
}

use heather_kernel::subst::{GlobalEntry, GlobalSubst};

// ---------------------------------------------------------------------------
// Drivers
// ---------------------------------------------------------------------------

/// `eval(t, ρ_Γ) ⊩ whnf(t)`, δ-transparent, reported by seed only.
fn check(
    seed: u64,
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    t: &Rc<Term>,
    what: &str,
) {
    for transparent in [true, false] {
        let arena = ValueArena::new();
        let mut a = Agree::new(psi, transparent, gamma, &arena);
        let v = a
            .ev
            .eval_tm(t, &Env::identity(&arena, gamma.entries.len() as u32))
            .unwrap_or_else(|_| panic!("seed {seed}: {what}: evaluator exhausted fuel"));
        let v = a
            .ev
            .delta_whnf(v)
            .unwrap_or_else(|_| panic!("seed {seed}: {what}: δ-unfolding exhausted fuel"));
        if let Err(why) = a.tm(&v, t, gamma, DEPTH) {
            panic!(
                "seed {seed}: {what}: evaluator disagrees with the rewriter \
                 (δ {}): {why} (term output suppressed)",
                if transparent { "transparent" } else { "opaque" }
            );
        }
    }
}

/// [`check`] for types.
fn check_ty(seed: u64, psi: &GlobalCtx, gamma: &LocalCtx, t: &Rc<Type>, what: &str) {
    for transparent in [true, false] {
        let arena = ValueArena::new();
        let mut a = Agree::new(psi, transparent, gamma, &arena);
        let v = a
            .ev
            .eval_ty(t, &Env::identity(&arena, gamma.entries.len() as u32))
            .unwrap_or_else(|_| panic!("seed {seed}: {what}: evaluator exhausted fuel"));
        let v = a
            .ev
            .delta_whnf_ty(v)
            .unwrap_or_else(|_| panic!("seed {seed}: {what}: δ-unfolding exhausted fuel"));
        if let Err(why) = a.ty(&v, t, gamma, DEPTH) {
            panic!(
                "seed {seed}: {what}: evaluator disagrees with the rewriter \
                 (δ {}): {why} (term output suppressed)",
                if transparent { "transparent" } else { "opaque" }
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Seed stream 1: generated well-typed triples, terms and their types
// ---------------------------------------------------------------------------

#[test]
fn stream1_generated_terms_and_types() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9e3779b97f4a7c15);
        let env = gen_wt_env(&mut r);
        let (t, ty, _) = gen_wt_term(&env, &mut r, BUDGET);
        check(seed, &env.psi, &env.gamma, &t, "generated term");
        check_ty(seed, &env.psi, &env.gamma, &ty, "generated type");
    }
}

// ---------------------------------------------------------------------------
// Seed stream 2: perturbed twins — β/η/letbox/elim_Nat expansions, i.e. the
// redex-rich shapes a whnf actually has to reduce
// ---------------------------------------------------------------------------

#[test]
fn stream2_perturbed_terms() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x517cc1b727220a95);
        let env = gen_wt_env(&mut r);
        let (t, ty, l) = gen_wt_term(&env, &mut r, BUDGET);
        let Some(p) = perturb_conv(&env, &mut r, &t, &ty, &l) else {
            panic!("seed {seed}: no perturbation applicable");
        };
        check(seed, &env.psi, &env.gamma, &p, "perturbed term");
    }
}

// ---------------------------------------------------------------------------
// Seed stream 3: open terms in a non-empty Γ over both `CtxBase` shapes, at a
// *checked* type — the position that is not synthesis
// ---------------------------------------------------------------------------

#[test]
fn stream3_open_terms_at_a_checked_type() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let mut env = gen_wt_env(&mut r);
        // Force a non-empty Γ: the abstract-prefix identity of design §3.2 is
        // only exercised by variables that reach past the concrete entries.
        env.gamma = gen_wt_ctx(&env, &mut r, 4, env.layer);
        if env.gamma.entries.is_empty() {
            env.gamma.entries.push(CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero });
        }
        let (ty, l) = gen_wt_type(&env, &mut r, BUDGET / 2);
        let Some(t) = gen_wt_term_at(&env, &mut r, BUDGET, &ty, &l) else { continue };
        check(seed, &env.psi, &env.gamma, &t, "checked-position term");
        check_ty(seed, &env.psi, &env.gamma, &ty, "checked-position type");
        // Every entry type of Γ, in its own prefix — types that mention the
        // context variable's own scope.
        for k in 0..env.gamma.entries.len() {
            let prefix =
                env.gamma.prefix(k);
            let ety = Rc::clone(&env.gamma.entries[k].ty);
            check_ty(seed, &env.psi, &prefix, &ety, "Γ entry type");
        }
    }
}

// ---------------------------------------------------------------------------
// Seed stream 4: boxed code under the identity code recursors — the 56
// branch telescopes, fired through the *shared* `beta_elim_*`
// ---------------------------------------------------------------------------

/// `(λ(_ : Nat). t↑) ze` — `t` wrapped in a β-redex, so that by the time it
/// is evaluated the environment is **one longer than the Γ its reduct lives
/// in**. That gap is what the shared β helpers see: `fire` materializes
/// `id_Γ` at the *term's* scope, not the value's, and the two stop coinciding
/// exactly here. `ty` is `t`'s own type, so the wrapper is well-typed.
fn under_beta(t: Rc<Term>, ty: &Type, level: &Level) -> Rc<Term> {
    Rc::new(Term::App {
        fun: Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: level.clone(),
            dom: Rc::new(Type::Nat),
            body: Rc::new(t.shift_local(1)),
        }),
        dom_level: Level::Zero,
        cod_level: level.clone(),
        dom: Rc::new(Type::Nat),
        cod: Rc::new(ty.shift_local(1)),
        arg: Rc::new(Term::Zero),
    })
}

#[test]
fn stream4_code_recursors() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xc3a5c85c97cb3127);
        let mut env = gen_wt_env(&mut r);
        env.layer = Layer::Meta; // recursors are layer-m forms
        let delta = gen_wt_ctx(&env, &mut r, 4, Layer::Prog);
        let ce = env.in_ctx(delta.clone(), Layer::Code);

        // elim^Typ over generated code of a type.
        let (code, cl) = gen_wt_type(&ce, &mut r, BUDGET);
        let cl2 = cl.clone();
        let t = Rc::new(Term::ElimCodeTy {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: identity_motives(),
            branches: identity_branches(),
            code_level: cl,
            ctx: delta.clone(),
            scrut: Rc::new(Term::BoxTy(code)),
        });
        check(seed, &env.psi, &env.gamma, &t, "identity elim^Typ");
        let ty = Type::CodeTy { ctx: delta.clone(), level: cl2 };
        let wrapped = under_beta(t, &ty, &Level::Zero);
        check(seed, &env.psi, &env.gamma, &wrapped, "identity elim^Typ under β");

        // elim^Trm over generated code of a term.
        let (code, cty, cl) = gen_wt_term(&ce, &mut r, BUDGET);
        let cl2 = cl.clone();
        let t = Rc::new(Term::ElimCodeTm {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: identity_motives(),
            branches: identity_branches(),
            code_level: cl,
            ctx: delta.clone(),
            ty: Rc::clone(&cty),
            scrut: Rc::new(Term::BoxTm(code)),
        });
        check(seed, &env.psi, &env.gamma, &t, "identity elim^Trm");
        let ty = Type::CodeTm { ctx: delta, ty: cty, level: cl2 };
        let wrapped = under_beta(t, &ty, &Level::Zero);
        check(seed, &env.psi, &env.gamma, &wrapped, "identity elim^Trm under β");
    }
}

// ---------------------------------------------------------------------------
// Seed stream 5: a definition-carrying Ψ — δ, and δ under a substitution
// whose payload is a redex (design §3.4, the domain's subtlest point)
// ---------------------------------------------------------------------------

/// `Ψ = (u : Trm_c(Δ ⊢ Nat @ 0) := body)` with `Δ = (·, x : Nat)`, so that
/// `u^{δ}` unfolds to `body[δ]` and the payload rides in the neutral's
/// substitution as a **value**.
fn defs_psi(body: Rc<Term>) -> (GlobalCtx, LocalCtx) {
    let delta = LocalCtx {
        base: CtxBase::Nil,
        entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
    };
    let psi = GlobalCtx::new(vec![GlobalBinding::defined_tm(
        delta.clone(),
        Layer::Code,
        Rc::new(Type::Nat),
        Level::Zero,
        body,
    )]);
    (psi, delta)
}

/// `elim_Nat (_. Nat) ze (x y. su y) scrut` — a redex whenever `scrut` is a
/// numeral, and neutral otherwise; the "expensive payload" of §3.4.
fn nat_rec(scrut: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::ElimNat {
        level: Level::Zero,
        motive: Rc::new(Type::Nat),
        base: Rc::new(Term::Zero),
        step: Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0))))),
        scrut,
    })
}

fn numeral(n: u32) -> Rc<Term> {
    let mut t = Rc::new(Term::Zero);
    for _ in 0..n {
        t = Rc::new(Term::Succ(t));
    }
    t
}

#[test]
fn stream5_definitions_and_delta_payloads() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xff51afd7ed558ccd);
        // The body is an arbitrary well-typed `Nat` term over Δ = (·, x:Nat)
        // — so the definition genuinely computes with its argument.
        let delta = LocalCtx {
            base: CtxBase::Nil,
            entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
        };
        let base_env = gen_wt_env(&mut r);
        let benv = base_env.in_ctx(delta.clone(), Layer::Prog);
        // Fall back to `x` itself: the definition must still mention its
        // index, or δ would be testing nothing.
        let body = gen_wt_term_at(&benv, &mut r, BUDGET, &Type::Nat, &Level::Zero)
            .unwrap_or_else(|| Rc::new(Term::Var(LocalVar(0))));
        let (psi, _) = defs_psi(body);

        // Γ = (·, y : Nat): a Γ-variable makes the payload's own reduct
        // neutral for half the cases.
        let gamma = LocalCtx {
            base: CtxBase::Nil,
            entries: (vec![CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }]).into(),
        };
        let payloads = [
            numeral((seed % 4) as u32),
            nat_rec(numeral((seed % 3) as u32)),
            nat_rec(Rc::new(Term::Var(LocalVar(0)))),
            nat_rec(nat_rec(numeral((seed % 3) as u32))),
        ];
        for (i, payload) in payloads.iter().enumerate() {
            let u = Rc::new(Term::GlobalTm {
                var: GlobalVar(0),
                subst: LocalSubst {
                    tail: SubstTail::Empty { len: 1, base: CtxBase::Nil },
                    terms: vec![Rc::clone(payload)],
                },
            });
            // The definition bare, under a constructor, and as the scrutinee
            // of an eliminator at three nesting depths.
            check(seed, &psi, &gamma, &u, &format!("u^δ (payload {i})"));
            let s = Rc::new(Term::Succ(Rc::clone(&u)));
            check(seed, &psi, &gamma, &s, &format!("su (u^δ) (payload {i})"));
            check(seed, &psi, &gamma, &nat_rec(Rc::clone(&u)), &format!("elim u^δ ({i})"));
            check(
                seed,
                &psi,
                &gamma,
                &nat_rec(nat_rec(Rc::clone(&u))),
                &format!("elim² u^δ ({i})"),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Fuel: exhaustion is never a verdict, and no thunk memoizes a failure
// ---------------------------------------------------------------------------

/// For **every** budget the evaluator either agrees with the rewriter or
/// reports `OutOfFuel`. It never returns a value that disagrees.
///
/// The two accountings are deliberately not identical — the machine's steps
/// are ch. 06's, but the *order* in which it reaches them differs, and
/// sharing makes total spend depend on the value graph (design §6). So the
/// property under test is the invariant, not a threshold: a test that
/// asserted a particular budget were insufficient would be asserting a cost
/// model.
#[test]
fn low_fuel_never_produces_a_wrong_answer() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x8ebc6af09c88c6e3);
        let env = gen_wt_env(&mut r);
        let (t, _, _) = gen_wt_term(&env, &mut r, BUDGET);
        let arena = ValueArena::new();
        let root = Env::identity(&arena, env.gamma.entries.len() as u32);
        let mut succeeded_somewhere = false;
        for budget in [0u64, 1, 2, 4, 8, 32, 256] {
            let mut a = Agree::new(&env.psi, true, &env.gamma, &arena);
            a.ev = Eval::new(budget, Defs::transparent(&env.psi), env.gamma.base, &arena);
            let Ok(v) = a.ev.eval_tm(&t, &root) else { continue };
            let Ok(v) = a.ev.delta_whnf(v) else { continue };
            succeeded_somewhere = true;
            // The agreement check itself needs a real budget; give it one.
            // Only the *evaluation under the small budget* is under test.
            let v2 = v;
            let mut b = Agree::new(&env.psi, true, &env.gamma, &arena);
            b.ev = Eval::new(FUEL, Defs::transparent(&env.psi), env.gamma.base, &arena);
            if let Err(why) = b.tm(&v2, &t, &env.gamma, 2) {
                panic!("seed {seed}: budget {budget} produced a wrong value: {why}");
            }
        }
        assert!(succeeded_somewhere, "seed {seed}: no budget in the sweep sufficed");
    }
}

/// A thunk that failed under a small budget must succeed when re-forced under
/// a larger one: **no thunk memoizes a failure** (design §6). Without this
/// rule a caller that retried with more fuel would inherit a poisoned node.
/// `elim_Nat (_. Nat) ze (x y. y) (numeral n)` — the *weak head* of this is
/// `ze`, and reaching it costs `n` fires: the recursion is in the induction
/// hypothesis, so a lazy machine must still walk the whole numeral. (Contrast
/// [`nat_rec`], whose whnf is one step because `su y` is already canonical —
/// which is exactly the laziness the machine is supposed to have.)
fn nat_drain(n: u32) -> Rc<Term> {
    Rc::new(Term::ElimNat {
        level: Level::Zero,
        motive: Rc::new(Type::Nat),
        base: Rc::new(Term::Zero),
        step: Rc::new(Term::Var(LocalVar(0))),
        scrut: numeral(n),
    })
}

#[test]
fn a_failed_thunk_is_not_poisoned() {
    let big = nat_drain(12);
    let gamma = LocalCtx::nil();
    let psi = GlobalCtx::default();
    let arena = ValueArena::new();

    // (a) an ordinary suspension.
    let clo = arena.tm(TmClo::syn(Env::empty(&arena), Rc::clone(&big)));
    let mut small = Eval::new(3, Defs::opaque(), gamma.base, &arena);
    assert!(small.force(clo).is_err(), "the small budget must not suffice");
    assert!(arena.memo_tm(clo).is_none(), "a failed force must memoize nothing");
    let mut large = Eval::new(FUEL, Defs::opaque(), gamma.base, &arena);
    let v = large.force(clo).expect("re-forcing under a larger budget must succeed");
    assert!(matches!(&*v, Val::Zero), "the drained recursion must reach ze");
    assert!(arena.memo_tm(clo).is_some(), "a successful result is cached");
    drop(v);

    // (b) a glued neutral's unfolding — the δ path, where the memo lives on
    //     the definition's body rather than on a sub-term.
    let (dpsi, _) = defs_psi(Rc::clone(&big));
    let u = Rc::new(Term::GlobalTm {
        var: GlobalVar(0),
        subst: LocalSubst {
            tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
            terms: vec![Rc::new(Term::Zero)],
        },
    });
    let mut small = Eval::new(4, Defs::transparent(&dpsi), gamma.base, &arena);
    let glued = small
        .eval_tm(&u, &Env::empty(&arena))
        .expect("building the glued neutral is one step");
    let unfold = match &*glued {
        Val::Neutral(n) => n.unfold.clone().expect("a definition is glued"),
        _ => panic!("u^δ must evaluate to a neutral"),
    };
    assert!(small.force(unfold).is_err(), "the small budget must not suffice");
    assert!(arena.memo_tm(unfold).is_none(), "a failed δ-unfold must memoize nothing");
    let mut large = Eval::new(FUEL, Defs::transparent(&dpsi), gamma.base, &arena);
    assert!(
        large.force(unfold).is_ok(),
        "re-forcing the same unfolding under a larger budget must succeed"
    );
    let _ = psi;
}

/// The rewriter and the evaluator agree on *which* inputs are cheap: with a
/// budget of zero, anything with a redex at the head fails on both.
#[test]
fn zero_fuel_reduces_nothing() {
    let gamma = LocalCtx::nil();
    let t = nat_rec(numeral(1));
    let arena = ValueArena::new();
    let mut ev = Eval::new(0, Defs::opaque(), gamma.base, &arena);
    assert!(ev.eval_tm(&t, &Env::empty(&arena)).is_err(), "a redex must cost fuel");
    assert!(
        whnf_term_delta(&t, &gamma, Defs::opaque(), 0).is_err(),
        "the rewriter agrees"
    );
}
