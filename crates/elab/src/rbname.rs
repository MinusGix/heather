//! The naming half of the readback (`docs/projected-tuple-tower-design.md`
//! §11.2/§11.4): the sharing the readback's memo already found, written down
//! as **names** instead of as copies.
//!
//! `rbemit.rs` hands this module a root `Type` whose interior is an `Rc`
//! **graph** — one node per distinct sub-value — but whose *meaning* is the
//! tree that graph expands to, because the term language has no `let`. This
//! module picks the nodes whose sharing is worth a Ψ definition (§11.2's
//! measured rule: name a shared node when naming it saves at least
//! [`THRESHOLD`] nodes), rebuilds the graph with each named node replaced by
//! `u^δ`, and hands back the bodies so the caller can mint them.
//!
//! Three things decide whether a shared node can be named at all, and the
//! whole module is organized around them:
//!
//! - **It must be a term.** A Ψ *type* binding has no body
//!   (`GlobalBinding::Ty`), so only `GlobalBinding::Tm`'s `body` is a sharing
//!   node; a shared *type* can be named only where it is already `El c` and
//!   the naming falls on `c`. Type nodes that clear the threshold are counted
//!   and declined.
//! - **Its context must be spellable.** A mint is `Δ ⊢ body : T` with
//!   `Δ = Γ` extended by the binders the node sits under, and those binder
//!   types are read off the *syntax* — kernel syntax is fully annotated
//!   (ch. 04), so `Π`'s codomain sits under `dom`, `elim_Nat`'s step under
//!   `Nat` and the motive, and so on ([`slots_tm`]/[`slots_ty`]'s `Scope`).
//!   A scope this walk cannot spell — a code payload in another Δ, a
//!   universe or context binder, a branch whose binder needs an
//!   instantiation — is `Scope::Foreign`, and nothing under it is named.
//! - **Its context must be the *same* everywhere it occurs.** One `Rc` can be
//!   reached by two paths; if their binder frames differ, the node's de
//!   Bruijn indices mean different things at the two sites and a single
//!   binding cannot serve both. Frames are interned, so the test is a pointer
//!   comparison, and a mismatch poisons the whole subtree.
//!
//! Two of those three are also **counting modes**, because the round's step 0
//! is a measurement: `choose`'s `allow_types` prices what a device that minted
//! a type's *code* would emit, and its `minimal` prices a mint scoped in the
//! innermost entries its body actually reaches into rather than in every
//! binder above it. Neither is a spelling this module writes — the rebuild
//! leaves those nodes inline — and §12.5 of the design doc is what they
//! measured.
//!
//! The module is deliberately pure syntax: it never touches a value, which is
//! what makes it testable on hand-built terms and reusable at any emission
//! site that has an `Rc`-shared answer.

use std::collections::HashMap;
use std::sync::Arc as Rc;
use std::sync::OnceLock;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, Term, Type,
};

/// §11.2's measured unit of sharing: name a shared node when naming it saves
/// at least this many nodes. `0` (name everything shared) is both 30× more
/// declarations and slightly *worse* in nodes — a name costs its body plus a
/// reference per use, and most shared nodes are small.
pub(crate) const THRESHOLD: u64 = 64;

/// The thresholds the instrument prices on one walk — §11.2's table, re-asked
/// of the *emitted* graph rather than of the value graph's memo.
const THRESHOLDS: [u64; 5] = [0, 16, 64, 1_024, 16_384];

/// One child slot of a syntax node.
#[derive(Clone)]
pub(crate) enum Kid {
    Tm(Rc<Term>),
    Ty(Rc<Type>),
}

/// The scope a child sits in, relative to its parent's.
pub(crate) enum Scope {
    /// The same context.
    Same,
    /// Under binders whose types — scoped in the context as it grows — the
    /// former above carries.
    Under(Vec<(Rc<Type>, Level)>),
    /// A scope this walk does not spell: a code payload in another Δ, a
    /// universe or context binder, an eliminator branch whose binder type
    /// needs an instantiation. Nothing below it is named. The payload is how
    /// many **local** binders the child sits under anyway — needed because a
    /// node *above* a foreign one still has to know which variables reach it
    /// — and [`ANOTHER_CTX`] for a child whose variables address a different
    /// Γ entirely.
    Foreign(u32),
}

/// A `Foreign` child scoped in a context of its own (a boxed payload, a code
/// recursor's type argument): none of its variables address the ambient Γ, so
/// it constrains nothing above it.
pub(crate) const ANOTHER_CTX: u32 = u32::MAX;

fn under(ty: &Rc<Type>, level: &Level) -> Scope {
    Scope::Under(vec![(Rc::clone(ty), level.clone())])
}

fn el(level: &Level, tm: &Rc<Term>) -> Rc<Type> {
    Rc::new(Type::El {
        level: level.clone(),
        tm: Rc::clone(tm),
    })
}

// -- the one child map -----------------------------------------------------
//
// Two matches over each kernel sort, and they are a pair: `slots_*` lists a
// node's children in a fixed order with the scope each sits in, `rebuild_*`
// puts a node back together from a list in that same order. Everything else
// in the module is scope-independent.

pub(crate) fn slots_ty(t: &Type) -> Vec<(Kid, Scope)> {
    let tm = |t: &Rc<Term>, s| (Kid::Tm(Rc::clone(t)), s);
    let ty = |t: &Rc<Type>, s| (Kid::Ty(Rc::clone(t)), s);
    match t {
        Type::Nat
        | Type::Ty(_)
        | Type::SEmpty { .. }
        | Type::Unit { .. }
        | Type::Empty { .. }
        | Type::CodeTy { .. } => Vec::new(),
        Type::Pi { dom_level, dom, cod, .. } => {
            vec![ty(dom, Scope::Same), ty(cod, under(dom, dom_level))]
        }
        Type::Sigma { fst_level, fst, snd, .. } => {
            vec![ty(fst, Scope::Same), ty(snd, under(fst, fst_level))]
        }
        Type::W { shape_level, shape, pos, .. } => {
            vec![ty(shape, Scope::Same), ty(pos, under(shape, shape_level))]
        }
        Type::Wf { level, shape, arity } => {
            vec![ty(shape, Scope::Same), tm(arity, under(shape, level))]
        }
        Type::Sum { lhs, rhs, .. } => vec![ty(lhs, Scope::Same), ty(rhs, Scope::Same)],
        Type::El { tm: t, .. } => vec![tm(t, Scope::Same)],
        Type::Id { ty: t, lhs, rhs, .. } | Type::SEq { ty: t, lhs, rhs, .. } => vec![
            ty(t, Scope::Same),
            tm(lhs, Scope::Same),
            tm(rhs, Scope::Same),
        ],
        Type::Squash { ty: t, .. } => vec![ty(t, Scope::Same)],
        Type::Vec { elem, len, .. } => vec![ty(elem, Scope::Same), tm(len, Scope::Same)],
        Type::Fin { len } => vec![tm(len, Scope::Same)],
        Type::UPi { body, .. } | Type::CtxPi { body, .. } | Type::TyPi { body, .. } => {
            vec![ty(body, Scope::Foreign(0))]
        }
        Type::CodeTm { ty: t, .. } => vec![ty(t, Scope::Foreign(ANOTHER_CTX))],
        Type::GlobalTy { subst, .. } => subst
            .terms
            .iter()
            .map(|t| tm(t, Scope::Same))
            .collect(),
    }
}

pub(crate) fn rebuild_ty(t: &Type, kids: &[Kid]) -> Type {
    let tm = |i: usize| match &kids[i] {
        Kid::Tm(t) => Rc::clone(t),
        Kid::Ty(_) => unreachable!("a term slot was answered with a type"),
    };
    let ty = |i: usize| match &kids[i] {
        Kid::Ty(t) => Rc::clone(t),
        Kid::Tm(_) => unreachable!("a type slot was answered with a term"),
    };
    match t {
        Type::Nat
        | Type::Ty(_)
        | Type::SEmpty { .. }
        | Type::Unit { .. }
        | Type::Empty { .. }
        | Type::CodeTy { .. } => t.clone(),
        Type::Pi { dom_level, cod_level, .. } => Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: ty(0),
            cod: ty(1),
        },
        Type::Sigma { fst_level, snd_level, .. } => Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: ty(0),
            snd: ty(1),
        },
        Type::W { shape_level, pos_level, .. } => Type::W {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            shape: ty(0),
            pos: ty(1),
        },
        Type::Wf { level, .. } => Type::Wf {
            level: level.clone(),
            shape: ty(0),
            arity: tm(1),
        },
        Type::Sum { lhs_level, rhs_level, .. } => Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: ty(0),
            rhs: ty(1),
        },
        Type::El { level, .. } => Type::El {
            level: level.clone(),
            tm: tm(0),
        },
        Type::Id { level, .. } => Type::Id {
            level: level.clone(),
            ty: ty(0),
            lhs: tm(1),
            rhs: tm(2),
        },
        Type::SEq { level, .. } => Type::SEq {
            level: level.clone(),
            ty: ty(0),
            lhs: tm(1),
            rhs: tm(2),
        },
        Type::Squash { level, .. } => Type::Squash {
            level: level.clone(),
            ty: ty(0),
        },
        Type::Vec { level, .. } => Type::Vec {
            level: level.clone(),
            elem: ty(0),
            len: tm(1),
        },
        Type::Fin { .. } => Type::Fin { len: tm(0) },
        Type::UPi { num_vars, level, .. } => Type::UPi {
            num_vars: *num_vars,
            level: level.clone(),
            body: ty(0),
        },
        Type::CtxPi { level, .. } => Type::CtxPi {
            level: level.clone(),
            body: ty(0),
        },
        Type::TyPi { ctx, arg_level, body_level, .. } => Type::TyPi {
            ctx: ctx.clone(),
            arg_level: arg_level.clone(),
            body_level: body_level.clone(),
            body: ty(0),
        },
        Type::CodeTm { ctx, level, .. } => Type::CodeTm {
            ctx: ctx.clone(),
            ty: ty(0),
            level: level.clone(),
        },
        Type::GlobalTy { var, subst } => Type::GlobalTy {
            var: *var,
            subst: LocalSubst {
                tail: subst.tail,
                terms: (0..kids.len()).map(tm).collect(),
            },
        },
    }
}

pub(crate) fn slots_tm(t: &Term) -> Vec<(Kid, Scope)> {
    let tm = |t: &Rc<Term>, s| (Kid::Tm(Rc::clone(t)), s);
    let ty = |t: &Rc<Type>, s| (Kid::Ty(Rc::clone(t)), s);
    match t {
        Term::Var(_)
        | Term::TmNat
        | Term::TmTy(_)
        | Term::Zero
        | Term::NatLit(_)
        | Term::TmSEmpty { .. }
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::Triv { .. } => Vec::new(),
        Term::Succ(t) => vec![tm(t, Scope::Same)],
        Term::TmPi { dom_level, dom, cod, .. } => vec![
            tm(dom, Scope::Same),
            tm(cod, under(&el(dom_level, dom), dom_level)),
        ],
        Term::TmSigma { fst_level, fst, snd, .. } => vec![
            tm(fst, Scope::Same),
            tm(snd, under(&el(fst_level, fst), fst_level)),
        ],
        Term::TmW { shape_level, shape, pos, .. } => vec![
            tm(shape, Scope::Same),
            tm(pos, under(&el(shape_level, shape), shape_level)),
        ],
        Term::TmWf { level, shape, arity } => vec![
            tm(shape, Scope::Same),
            tm(arity, under(&el(level, shape), level)),
        ],
        Term::TmId { ty: t, lhs, rhs, .. } | Term::TmSEq { ty: t, lhs, rhs, .. } => vec![
            tm(t, Scope::Same),
            tm(lhs, Scope::Same),
            tm(rhs, Scope::Same),
        ],
        Term::TmSquash { ty: t, .. } => vec![tm(t, Scope::Same)],
        Term::TmSum { lhs, rhs, .. } => vec![tm(lhs, Scope::Same), tm(rhs, Scope::Same)],
        Term::TmVec { elem, len, .. } => vec![tm(elem, Scope::Same), tm(len, Scope::Same)],
        Term::TmFin { len } => vec![tm(len, Scope::Same)],
        // The step's two binders are `n : Nat` and `ih : M[n]`, and `M` read
        // under its own binder *is* `M[n]` in that context — which is why a
        // motive can be a binder type here and cannot be under `elim_W`.
        Term::ElimNat { level, motive, base, step, scrut } => vec![
            ty(motive, under(&Rc::new(Type::Nat), &Level::Zero)),
            tm(base, Scope::Same),
            tm(
                step,
                Scope::Under(vec![
                    (Rc::new(Type::Nat), Level::Zero),
                    (Rc::clone(motive), level.clone()),
                ]),
            ),
            tm(scrut, Scope::Same),
        ],
        Term::Refl { ty: t, tm: v, .. }
        | Term::SRefl { ty: t, tm: v, .. }
        | Term::Squash { ty: t, tm: v, .. } => vec![ty(t, Scope::Same), tm(v, Scope::Same)],
        Term::J { ty: t, lhs, motive, case, rhs, proof, .. } => vec![
            ty(t, Scope::Same),
            tm(lhs, Scope::Same),
            // Two binders, the second an `Id` over the first: spellable, but
            // it needs a shift the rest of this table does not, and a motive
            // is not where the shared mass is.
            ty(motive, Scope::Foreign(2)),
            tm(case, Scope::Same),
            tm(rhs, Scope::Same),
            tm(proof, Scope::Same),
        ],
        Term::Transp { ty_level, ty: t, motive, lhs, rhs, proof, tm: v, .. } => vec![
            ty(t, Scope::Same),
            ty(motive, under(t, ty_level)),
            tm(lhs, Scope::Same),
            tm(rhs, Scope::Same),
            tm(proof, Scope::Same),
            tm(v, Scope::Same),
        ],
        Term::ElimEmpty { scrut_level, motive, scrut, .. } => {
            let empty = Rc::new(Type::Empty { level: scrut_level.clone() });
            vec![
                ty(motive, under(&empty, scrut_level)),
                tm(scrut, Scope::Same),
            ]
        }
        Term::ElimSEmpty { scrut_level, motive, scrut, .. } => {
            let empty = Rc::new(Type::SEmpty { level: scrut_level.clone() });
            vec![
                ty(motive, under(&empty, scrut_level)),
                tm(scrut, Scope::Same),
            ]
        }
        Term::ElimSquash { src_level, src_ty, motive, case, scrut, .. } => {
            let sq = Rc::new(Type::Squash {
                level: src_level.clone(),
                ty: Rc::clone(src_ty),
            });
            vec![
                ty(src_ty, Scope::Same),
                ty(motive, under(&sq, src_level)),
                tm(case, under(src_ty, src_level)),
                tm(scrut, Scope::Same),
            ]
        }
        // Superseded by docs/intro-by-type-design.md; see rbcount.rs.
        Term::PairAt { ty: t, fst, snd } => {
            vec![ty(t, Scope::Same), tm(fst, Scope::Same), tm(snd, Scope::Same)]
        }
        Term::InlAt { ty: t, val: x }
        | Term::InrAt { ty: t, val: x }
        | Term::FstAt { ty: t, pair: x }
        | Term::SndAt { ty: t, pair: x } => {
            vec![ty(t, Scope::Same), tm(x, Scope::Same)]
        }
        Term::Pair { fst_level, fst_ty, snd_ty, fst, snd, .. } => vec![
            ty(fst_ty, Scope::Same),
            ty(snd_ty, under(fst_ty, fst_level)),
            tm(fst, Scope::Same),
            tm(snd, Scope::Same),
        ],
        Term::Fst { fst_level, fst_ty, snd_ty, pair, .. }
        | Term::Snd { fst_level, fst_ty, snd_ty, pair, .. } => vec![
            ty(fst_ty, Scope::Same),
            ty(snd_ty, under(fst_ty, fst_level)),
            tm(pair, Scope::Same),
        ],
        Term::Inl { lhs, rhs, val, .. } | Term::Inr { lhs, rhs, val, .. } => vec![
            ty(lhs, Scope::Same),
            ty(rhs, Scope::Same),
            tm(val, Scope::Same),
        ],
        Term::Case { lhs_level, rhs_level, lhs, rhs, motive, case_l, case_r, scrut, .. } => {
            let sum = Rc::new(Type::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            });
            let lmax = Level::join(lhs_level.clone(), rhs_level.clone());
            vec![
                ty(lhs, Scope::Same),
                ty(rhs, Scope::Same),
                ty(motive, under(&sum, &lmax)),
                tm(case_l, under(lhs, lhs_level)),
                tm(case_r, under(rhs, rhs_level)),
                tm(scrut, Scope::Same),
            ]
        }
        Term::Sup { shape_level, shape_ty, pos_ty, label, children, .. } => vec![
            ty(shape_ty, Scope::Same),
            ty(pos_ty, under(shape_ty, shape_level)),
            tm(label, Scope::Same),
            tm(children, Scope::Same),
        ],
        Term::ElimW { shape_level, pos_level, shape, pos, motive, step, scrut, .. } => {
            let w = Rc::new(Type::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
            });
            let lmax = Level::join(shape_level.clone(), pos_level.clone());
            vec![
                ty(shape, Scope::Same),
                ty(pos, under(shape, shape_level)),
                ty(motive, under(&w, &lmax)),
                // Three binders, the third an instantiated motive under a
                // shift: not spelled here.
                tm(step, Scope::Foreign(3)),
                tm(scrut, Scope::Same),
            ]
        }
        Term::Supf { level, shape, arity, label, children } => vec![
            ty(shape, Scope::Same),
            tm(arity, under(shape, level)),
            tm(label, Scope::Same),
            tm(children, Scope::Same),
        ],
        Term::ElimWf { level, shape, arity, motive, step, scrut, .. } => {
            let wf = Rc::new(Type::Wf {
                level: level.clone(),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
            });
            vec![
                ty(shape, Scope::Same),
                tm(arity, under(shape, level)),
                ty(motive, under(&wf, level)),
                tm(step, Scope::Foreign(3)),
                tm(scrut, Scope::Same),
            ]
        }
        Term::Lam { dom_level, dom, body, .. } => vec![
            ty(dom, Scope::Same),
            tm(body, under(dom, dom_level)),
        ],
        Term::App { fun, dom_level, dom, cod, arg, .. } => vec![
            tm(fun, Scope::Same),
            ty(dom, Scope::Same),
            ty(cod, under(dom, dom_level)),
            tm(arg, Scope::Same),
        ],
        // A universe or context binder is not a local one, so the body's
        // variables still address this Γ; a `TyLam`'s body addresses `ctx`.
        Term::ULam { body, .. } | Term::CtxLam { body, .. } => vec![tm(body, Scope::Foreign(0))],
        Term::TyLam { body, .. } => vec![tm(body, Scope::Foreign(ANOTHER_CTX))],
        Term::UApp { fun, .. } | Term::CtxApp { fun, .. } => vec![tm(fun, Scope::Same)],
        Term::TyApp { fun, arg } => vec![tm(fun, Scope::Same), ty(arg, Scope::Foreign(ANOTHER_CTX))],
        Term::BoxTy(t) => vec![ty(t, Scope::Foreign(ANOTHER_CTX))],
        Term::BoxTm(t) => vec![tm(t, Scope::Foreign(ANOTHER_CTX))],
        Term::LetBoxTy { motive, body, scrut, .. } => vec![
            ty(motive, Scope::Foreign(1)),
            tm(body, Scope::Foreign(0)),
            tm(scrut, Scope::Same),
        ],
        Term::LetBoxTm { ty: t, motive, body, scrut, .. } => vec![
            ty(t, Scope::Foreign(ANOTHER_CTX)),
            ty(motive, Scope::Foreign(1)),
            tm(body, Scope::Foreign(0)),
            tm(scrut, Scope::Same),
        ],
        Term::ElimCodeTy { scrut, .. } => vec![tm(scrut, Scope::Same)],
        Term::ElimCodeTm { ty: t, scrut, .. } => {
            vec![ty(t, Scope::Foreign(ANOTHER_CTX)), tm(scrut, Scope::Same)]
        }
        Term::GlobalTm { subst, .. } => subst.terms.iter().map(|t| tm(t, Scope::Same)).collect(),
    }
}

pub(crate) fn rebuild_tm(t: &Term, kids: &[Kid]) -> Term {
    let tm = |i: usize| match &kids[i] {
        Kid::Tm(t) => Rc::clone(t),
        Kid::Ty(_) => unreachable!("a term slot was answered with a type"),
    };
    let ty = |i: usize| match &kids[i] {
        Kid::Ty(t) => Rc::clone(t),
        Kid::Tm(_) => unreachable!("a type slot was answered with a term"),
    };
    match t {
        Term::Var(_)
        | Term::TmNat
        | Term::TmTy(_)
        | Term::Zero
        | Term::NatLit(_)
        | Term::TmSEmpty { .. }
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::Triv { .. } => t.clone(),
        Term::Succ(_) => Term::Succ(tm(0)),
        Term::TmPi { dom_level, cod_level, .. } => Term::TmPi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: tm(0),
            cod: tm(1),
        },
        Term::TmSigma { fst_level, snd_level, .. } => Term::TmSigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: tm(0),
            snd: tm(1),
        },
        Term::TmW { shape_level, pos_level, .. } => Term::TmW {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            shape: tm(0),
            pos: tm(1),
        },
        Term::TmWf { level, .. } => Term::TmWf {
            level: level.clone(),
            shape: tm(0),
            arity: tm(1),
        },
        Term::TmId { level, .. } => Term::TmId {
            level: level.clone(),
            ty: tm(0),
            lhs: tm(1),
            rhs: tm(2),
        },
        Term::TmSEq { level, .. } => Term::TmSEq {
            level: level.clone(),
            ty: tm(0),
            lhs: tm(1),
            rhs: tm(2),
        },
        Term::TmSquash { level, .. } => Term::TmSquash {
            level: level.clone(),
            ty: tm(0),
        },
        Term::TmSum { lhs_level, rhs_level, .. } => Term::TmSum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: tm(0),
            rhs: tm(1),
        },
        Term::TmVec { level, .. } => Term::TmVec {
            level: level.clone(),
            elem: tm(0),
            len: tm(1),
        },
        Term::TmFin { .. } => Term::TmFin { len: tm(0) },
        Term::ElimNat { level, .. } => Term::ElimNat {
            level: level.clone(),
            motive: ty(0),
            base: tm(1),
            step: tm(2),
            scrut: tm(3),
        },
        Term::Refl { level, .. } => Term::Refl {
            level: level.clone(),
            ty: ty(0),
            tm: tm(1),
        },
        Term::SRefl { level, .. } => Term::SRefl {
            level: level.clone(),
            ty: ty(0),
            tm: tm(1),
        },
        Term::Squash { level, .. } => Term::Squash {
            level: level.clone(),
            ty: ty(0),
            tm: tm(1),
        },
        Term::J { ty_level, motive_level, .. } => Term::J {
            ty_level: ty_level.clone(),
            motive_level: motive_level.clone(),
            ty: ty(0),
            lhs: tm(1),
            motive: ty(2),
            case: tm(3),
            rhs: tm(4),
            proof: tm(5),
        },
        Term::Transp { ty_level, motive_level, .. } => Term::Transp {
            ty_level: ty_level.clone(),
            motive_level: motive_level.clone(),
            ty: ty(0),
            motive: ty(1),
            lhs: tm(2),
            rhs: tm(3),
            proof: tm(4),
            tm: tm(5),
        },
        Term::ElimEmpty { level, scrut_level, .. } => Term::ElimEmpty {
            level: level.clone(),
            scrut_level: scrut_level.clone(),
            motive: ty(0),
            scrut: tm(1),
        },
        Term::ElimSEmpty { level, scrut_level, .. } => Term::ElimSEmpty {
            level: level.clone(),
            scrut_level: scrut_level.clone(),
            motive: ty(0),
            scrut: tm(1),
        },
        Term::ElimSquash { src_level, dst_level, .. } => Term::ElimSquash {
            src_level: src_level.clone(),
            dst_level: dst_level.clone(),
            src_ty: ty(0),
            motive: ty(1),
            case: tm(2),
            scrut: tm(3),
        },
        Term::PairAt { .. } => Term::PairAt { ty: ty(0), fst: tm(1), snd: tm(2) },
        Term::InlAt { .. } => Term::InlAt { ty: ty(0), val: tm(1) },
        Term::InrAt { .. } => Term::InrAt { ty: ty(0), val: tm(1) },
        Term::FstAt { .. } => Term::FstAt { ty: ty(0), pair: tm(1) },
        Term::SndAt { .. } => Term::SndAt { ty: ty(0), pair: tm(1) },
        Term::Pair { fst_level, snd_level, .. } => Term::Pair {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: ty(0),
            snd_ty: ty(1),
            fst: tm(2),
            snd: tm(3),
        },
        Term::Fst { fst_level, snd_level, .. } => Term::Fst {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: ty(0),
            snd_ty: ty(1),
            pair: tm(2),
        },
        Term::Snd { fst_level, snd_level, .. } => Term::Snd {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: ty(0),
            snd_ty: ty(1),
            pair: tm(2),
        },
        Term::Inl { lhs_level, rhs_level, .. } => Term::Inl {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: ty(0),
            rhs: ty(1),
            val: tm(2),
        },
        Term::Inr { lhs_level, rhs_level, .. } => Term::Inr {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: ty(0),
            rhs: ty(1),
            val: tm(2),
        },
        Term::Case { lhs_level, rhs_level, motive_level, .. } => Term::Case {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            motive_level: motive_level.clone(),
            lhs: ty(0),
            rhs: ty(1),
            motive: ty(2),
            case_l: tm(3),
            case_r: tm(4),
            scrut: tm(5),
        },
        Term::Sup { shape_level, pos_level, .. } => Term::Sup {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            shape_ty: ty(0),
            pos_ty: ty(1),
            label: tm(2),
            children: tm(3),
        },
        Term::ElimW { shape_level, pos_level, motive_level, .. } => Term::ElimW {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            motive_level: motive_level.clone(),
            shape: ty(0),
            pos: ty(1),
            motive: ty(2),
            step: tm(3),
            scrut: tm(4),
        },
        Term::Supf { level, .. } => Term::Supf {
            level: level.clone(),
            shape: ty(0),
            arity: tm(1),
            label: tm(2),
            children: tm(3),
        },
        Term::ElimWf { level, motive_level, .. } => Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: ty(0),
            arity: tm(1),
            motive: ty(2),
            step: tm(3),
            scrut: tm(4),
        },
        Term::Lam { dom_level, cod_level, .. } => Term::Lam {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: ty(0),
            body: tm(1),
        },
        Term::App { dom_level, cod_level, .. } => Term::App {
            fun: tm(0),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: ty(1),
            cod: ty(2),
            arg: tm(3),
        },
        Term::ULam { num_vars, level, .. } => Term::ULam {
            num_vars: *num_vars,
            level: level.clone(),
            body: tm(0),
        },
        Term::CtxLam { level, .. } => Term::CtxLam {
            level: level.clone(),
            body: tm(0),
        },
        Term::TyLam { ctx, arg_level, body_level, .. } => Term::TyLam {
            ctx: ctx.clone(),
            arg_level: arg_level.clone(),
            body_level: body_level.clone(),
            body: tm(0),
        },
        Term::UApp { levels, .. } => Term::UApp {
            fun: tm(0),
            levels: levels.clone(),
        },
        Term::CtxApp { ctx, .. } => Term::CtxApp {
            fun: tm(0),
            ctx: ctx.clone(),
        },
        Term::TyApp { .. } => Term::TyApp {
            fun: tm(0),
            arg: ty(1),
        },
        Term::BoxTy(_) => Term::BoxTy(ty(0)),
        Term::BoxTm(_) => Term::BoxTm(tm(0)),
        Term::LetBoxTy { motive_level, code_level, ctx, .. } => Term::LetBoxTy {
            motive_level: motive_level.clone(),
            code_level: code_level.clone(),
            ctx: ctx.clone(),
            motive: ty(0),
            body: tm(1),
            scrut: tm(2),
        },
        Term::LetBoxTm { motive_level, code_level, ctx, .. } => Term::LetBoxTm {
            motive_level: motive_level.clone(),
            code_level: code_level.clone(),
            ctx: ctx.clone(),
            ty: ty(0),
            motive: ty(1),
            body: tm(2),
            scrut: tm(3),
        },
        Term::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ..
        } => Term::ElimCodeTy {
            ty_motive_level: ty_motive_level.clone(),
            tm_motive_level: tm_motive_level.clone(),
            motives: Rc::clone(motives),
            branches: Rc::clone(branches),
            code_level: code_level.clone(),
            ctx: ctx.clone(),
            scrut: tm(0),
        },
        Term::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ..
        } => Term::ElimCodeTm {
            ty_motive_level: ty_motive_level.clone(),
            tm_motive_level: tm_motive_level.clone(),
            motives: Rc::clone(motives),
            branches: Rc::clone(branches),
            code_level: code_level.clone(),
            ctx: ctx.clone(),
            ty: ty(0),
            scrut: tm(1),
        },
        Term::GlobalTm { var, subst } => Term::GlobalTm {
            var: *var,
            subst: LocalSubst {
                tail: subst.tail,
                terms: (0..kids.len()).map(tm).collect(),
            },
        },
    }
}

// -- the binder frames -----------------------------------------------------

/// One binder chain, interned so that two paths reaching the same node under
/// the same binders share a frame **by pointer** — which is what makes the
/// "is this node in one context or two?" test O(1).
struct Frame {
    parent: Option<Rc<Frame>>,
    binder: Option<(Rc<Type>, Level)>,
    poison: bool,
    depth: u32,
}

#[derive(Default)]
struct Frames {
    table: HashMap<(usize, usize, bool), Rc<Frame>>,
}

impl Frames {
    fn child(
        &mut self,
        parent: &Rc<Frame>,
        binder: Option<(Rc<Type>, Level)>,
        poison: bool,
    ) -> Rc<Frame> {
        let key = (
            Rc::as_ptr(parent) as usize,
            binder.as_ref().map_or(0, |(t, _)| Rc::as_ptr(t) as usize),
            poison,
        );
        if let Some(f) = self.table.get(&key) {
            return Rc::clone(f);
        }
        let depth = parent.depth + u32::from(binder.is_some());
        let f = Rc::new(Frame {
            parent: Some(Rc::clone(parent)),
            binder,
            poison: poison || parent.poison,
            depth,
        });
        self.table.insert(key, Rc::clone(&f));
        f
    }
}

/// How many nodes a type has, giving up at `budget`. The structural
/// comparison below is the only place this module walks a *tree* rather than
/// the graph, so it is the only place that has to be bounded: two
/// structurally equal copies of an exponential annotation would otherwise cost
/// their own size to compare.
fn size_up_to(t: &Type, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    for (kid, _) in slots_ty(t) {
        let ok = match kid {
            Kid::Ty(t) => size_up_to(&t, budget),
            Kid::Tm(_) => {
                // A term child is compared by pointer only; counting it is
                // enough to keep the budget honest.
                if *budget == 0 {
                    return false;
                }
                *budget -= 1;
                true
            }
        };
        if !ok {
            return false;
        }
    }
    true
}

/// The budget of [`size_up_to`]: a binder type this side of it is compared
/// structurally, past it only by pointer. Binder types are annotations, which
/// are small wherever a name is worth having.
const COMPARE_BUDGET: u32 = 256;

/// How deep into the ambient context a piece of syntax reaches: the smallest
/// `k` such that it is well scoped in the **innermost `k`** entries. `0` is a
/// closed piece. Memoized on `Rc` identity, so one pass over the graph costs
/// the graph.
///
/// The measure deliberately ignores a global reference's substitution *tail*
/// (`δ̂ = |Γ|`), which pins the syntax to one ambient length: rewriting the
/// tail is what `apply_local` does when a body is strengthened out of binders
/// it does not use, and this function's whole purpose is to say how far that
/// can go.
fn free_of(kid: &Kid, memo: &mut HashMap<(usize, bool), u32>) -> u32 {
    let (key, slots, leaf) = match kid {
        Kid::Tm(t) => (
            (Rc::as_ptr(t) as usize, true),
            slots_tm(t),
            match &**t {
                Term::Var(v) => v.0 + 1,
                _ => 0,
            },
        ),
        Kid::Ty(t) => ((Rc::as_ptr(t) as usize, false), slots_ty(t), 0),
    };
    if let Some(&f) = memo.get(&key) {
        return f;
    }
    // A cycle is impossible in syntax; the entry guards a re-entry anyway.
    memo.insert(key, 0);
    let mut free = leaf;
    for (child, scope) in &slots {
        let under = match scope {
            Scope::Same => 0,
            Scope::Under(b) => b.len() as u32,
            Scope::Foreign(k) => *k,
        };
        if under == ANOTHER_CTX {
            continue;
        }
        free = free.max(free_of(child, memo).saturating_sub(under));
    }
    memo.insert(key, free);
    free
}

/// The binder chain of a frame, innermost first.
fn chain_of(frame: &Rc<Frame>) -> Vec<(Rc<Type>, Level)> {
    let mut chain = Vec::new();
    let mut cur: Option<&Rc<Frame>> = Some(frame);
    while let Some(f) = cur {
        if let Some(b) = f.binder.as_ref() {
            chain.push(b.clone());
        }
        cur = f.parent.as_ref();
    }
    chain
}

/// How many innermost entries a mint for a node of reach `free` under `chain`
/// actually needs: `free` itself, closed up so that every entry's **type** is
/// scoped inside the block too (a binder whose type mentions an outer one
/// drags that one in). Bounded above by the whole context, which is §11.4's
/// Δ and always sufficient.
fn min_ctx(
    chain: &[(Rc<Type>, Level)],
    gamma_len: u32,
    free: u32,
    memo: &mut HashMap<(usize, bool), u32>,
) -> u32 {
    let total = gamma_len + chain.len() as u32;
    let mut k = free.min(total);
    loop {
        let mut need = k;
        for (j, (ty, _)) in chain.iter().enumerate().take(k as usize) {
            need = need.max(j as u32 + 1 + free_of(&Kid::Ty(Rc::clone(ty)), memo));
        }
        if need <= k || k == total {
            return k;
        }
        k = need.min(total);
    }
}

/// How many **innermost** binders two frames agree on — the measure a
/// *minimal* Δ replaces [`same_frame`]'s all-or-nothing test with. Two paths
/// into one shared node may bind different things further out and still be
/// one mint, as long as the block the body actually reaches into is the same.
/// [`u32::MAX`] when the chains agree entirely.
fn agreeing_prefix(a: &Rc<Frame>, b: &Rc<Frame>) -> u32 {
    if Rc::ptr_eq(a, b) {
        return u32::MAX;
    }
    let (ca, cb) = (chain_of(a), chain_of(b));
    if ca.len() != cb.len() || a.poison != b.poison {
        return 0;
    }
    for (j, ((x, lx), (y, ly))) in ca.iter().zip(cb.iter()).enumerate() {
        if Rc::ptr_eq(x, y) {
            continue;
        }
        let mut budget = COMPARE_BUDGET;
        if !size_up_to(x, &mut budget) || lx != ly || **x != **y {
            return j as u32;
        }
    }
    u32::MAX
}

/// Whether two frames are the same **context**. Interning makes the pointer
/// test decide it whenever the two paths spelled their binders with the same
/// `Rc`s; a shared node reached through two copies of one type would
/// otherwise read as "two contexts" and lose its name for no reason, so the
/// slow path compares the chains structurally. It runs at most once per extra
/// occurrence of a node, and only when the pointers already disagree.
fn same_frame(a: &Rc<Frame>, b: &Rc<Frame>) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    if a.depth != b.depth || a.poison != b.poison {
        return false;
    }
    match (a.binder.as_ref(), b.binder.as_ref()) {
        (None, None) => {}
        (Some((x, lx)), Some((y, ly))) => {
            if !Rc::ptr_eq(x, y) {
                let mut budget = COMPARE_BUDGET;
                if !size_up_to(x, &mut budget) || lx != ly || **x != **y {
                    return false;
                }
            }
        }
        _ => return false,
    }
    match (a.parent.as_ref(), b.parent.as_ref()) {
        (None, None) => true,
        (Some(x), Some(y)) => same_frame(x, y),
        _ => false,
    }
}

/// `Γ` extended by a frame's binders — the `Δ` a mint under it is scoped in.
fn ctx_of(gamma: &LocalCtx, frame: &Rc<Frame>) -> LocalCtx {
    let mut chain: Vec<(Rc<Type>, Level)> = Vec::new();
    let mut cur: Option<&Rc<Frame>> = Some(frame);
    while let Some(f) = cur {
        if let Some((ty, level)) = f.binder.as_ref() {
            chain.push((Rc::clone(ty), level.clone()));
        }
        cur = f.parent.as_ref();
    }
    let mut out = gamma.clone();
    for (ty, level) in chain.into_iter().rev() {
        out = out.extended(ty, level);
    }
    out
}

// -- the plan --------------------------------------------------------------

struct Node {
    frame: Rc<Frame>,
    kids: Vec<u32>,
    /// How many binders each child sits under, parallel to `kids`.
    binders: Vec<u32>,
    is_tm: bool,
    indeg: u32,
    /// How many innermost entries a mint for this node needs: its own reach,
    /// closed up so every entry's type is inside the block
    /// ([`min_ctx`]). §11.4's Δ is the whole context; this is the smallest
    /// one that serves.
    min_k: u32,
    /// How many innermost entries **every** occurrence of this node agrees
    /// on. `u32::MAX` until a second occurrence disagrees.
    agree: u32,
    /// Set when the node is reached under two different binder frames: its
    /// indices mean different things at the two sites, so no name can serve
    /// both, and the whole subtree is out.
    ambiguous: bool,
}

/// What the naming could not take, and why — §11.4's open questions as
/// counters rather than as prose.
#[derive(Default, Clone, Copy)]
pub(crate) struct Declines {
    /// Cleared the threshold but is a **type** node: a Ψ type binding has no
    /// body, so there is nothing to name it with.
    pub(crate) type_node: u64,
    /// Cleared the threshold but sits in a scope this walk does not spell.
    pub(crate) foreign: u64,
    /// Cleared the threshold but occurs under two different binder frames.
    pub(crate) ambiguous: u64,
    /// Cleared the threshold but the reserved block was full.
    pub(crate) over_cap: u64,
    /// The nodes the declines above would have saved, had they been minted.
    pub(crate) lost: u64,
}

/// What the caller does with a chosen name: mint `Δ ⊢ body` and answer with
/// the `GlobalVar` its reference uses, or **decline**. A decline leaves the
/// component inline, which is stage one's behaviour and always safe — it is
/// how a reserved block that is full, a body the kernel will not type, and a
/// mint that would mention an unsolved goal all come out.
///
/// Mints arrive in dependency order: every reference in `body` is to one the
/// minter has already accepted.
pub(crate) type Minter<'a> = dyn FnMut(&LocalCtx, &Rc<Term>) -> Option<GlobalVar> + 'a;

pub(crate) struct Naming {
    /// The named spelling. The instrument counts and discards it; the landing
    /// the next pass makes is what puts it on the default path, which is why
    /// nothing outside this module's tests reads it yet.
    #[allow(dead_code)]
    pub(crate) root: Rc<Type>,
    /// Names the minter accepted.
    pub(crate) minted: u32,
    /// Names it chose and the minter refused.
    pub(crate) refused: u32,
    /// The tree the root expands to with nothing named — the naive readback's
    /// own output.
    pub(crate) naive: u64,
    /// The tree the root expands to *with* the names, plus every minted body.
    pub(crate) emitted: u64,
    pub(crate) declines: Declines,
}

struct Plan<'a> {
    gamma: &'a LocalCtx,
    nodes: Vec<Node>,
    tm_ids: HashMap<usize, u32>,
    ty_ids: HashMap<usize, u32>,
    finish: Vec<u32>,
    frames: Frames,
    free_memo: HashMap<(usize, bool), u32>,
}

impl<'a> Plan<'a> {
    fn visit(&mut self, kid: &Kid, frame: &Rc<Frame>) -> u32 {
        let (key, is_tm) = match kid {
            Kid::Tm(t) => (Rc::as_ptr(t) as usize, true),
            Kid::Ty(t) => (Rc::as_ptr(t) as usize, false),
        };
        let map = if is_tm { &self.tm_ids } else { &self.ty_ids };
        if let Some(&id) = map.get(&key) {
            self.nodes[id as usize].indeg += 1;
            let seen = Rc::clone(&self.nodes[id as usize].frame);
            if !same_frame(&seen, frame) {
                self.poison(id);
                let p = agreeing_prefix(&seen, frame);
                self.limit(id, p);
            }
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(Node {
            frame: Rc::clone(frame),
            kids: Vec::new(),
            binders: Vec::new(),
            is_tm,
            indeg: 1,
            min_k: 0,
            agree: u32::MAX,
            ambiguous: false,
        });
        if is_tm {
            self.tm_ids.insert(key, id);
        } else {
            self.ty_ids.insert(key, id);
        }
        let slots = match kid {
            Kid::Tm(t) => slots_tm(t),
            Kid::Ty(t) => slots_ty(t),
        };
        let mut kids = Vec::with_capacity(slots.len());
        let mut binders = Vec::with_capacity(slots.len());
        for (child, scope) in &slots {
            let child_frame = match scope {
                Scope::Same => Rc::clone(frame),
                Scope::Under(bs) => {
                    let mut f = Rc::clone(frame);
                    for b in bs {
                        f = self.frames.child(&f, Some(b.clone()), false);
                    }
                    f
                }
                Scope::Foreign(_) => self.frames.child(frame, None, true),
            };
            binders.push(match scope {
                Scope::Same => 0,
                Scope::Under(bs) => bs.len() as u32,
                Scope::Foreign(k) => *k,
            });
            kids.push(self.visit(child, &child_frame));
        }
        self.nodes[id as usize].kids = kids;
        self.nodes[id as usize].binders = binders;
        let free = free_of(kid, &mut self.free_memo);
        let chain = chain_of(frame);
        let g = self.gamma.entries.len() as u32;
        self.nodes[id as usize].min_k = min_ctx(&chain, g, free, &mut self.free_memo);
        self.finish.push(id);
        id
    }

    /// Record that every occurrence of `id` agrees on at most `bound`
    /// innermost entries, and carry the same bound down — a child one binder
    /// in agrees on one more.
    fn limit(&mut self, id: u32, bound: u32) {
        if bound >= self.nodes[id as usize].agree {
            return;
        }
        self.nodes[id as usize].agree = bound;
        let kids = self.nodes[id as usize].kids.clone();
        let binders = self.nodes[id as usize].binders.clone();
        for (k, b) in kids.into_iter().zip(binders) {
            if b == ANOTHER_CTX {
                continue;
            }
            self.limit(k, bound.saturating_add(b));
        }
    }

    /// A node reached in two contexts, and everything under it: no name can
    /// serve both sites, so the subtree is out of the device entirely.
    fn poison(&mut self, id: u32) {
        if self.nodes[id as usize].ambiguous {
            return;
        }
        self.nodes[id as usize].ambiguous = true;
        let kids = self.nodes[id as usize].kids.clone();
        for k in kids {
            self.poison(k);
        }
    }

    /// What a reference to a node under `frame` costs where its body used to
    /// be spelled: the `GlobalTm` and its identity substitution's payloads
    /// (`LocalSubst::id`), plus the `El` when the occurrence is a type.
    fn ref_cost(&self, n: usize, minimal: bool) -> u64 {
        if minimal {
            return 1 + u64::from(self.nodes[n].min_k);
        }
        let frame = &self.nodes[n].frame;
        1 + self.gamma.entries.len() as u64 + u64::from(frame.depth)
    }
}

/// Pick the nodes worth naming, then rebuild the graph with each replaced by
/// `u^δ`. `cap` is the reserved block's size: a mint past it declines and its
/// component stays inline, which is always safe.
///
/// `var_of(j)` is the `GlobalVar` the `j`-th mint is referenced by — the
/// caller's business, because it depends on how the block was reserved
/// (§11.4: the goal arena's padding, numbered from the innermost end).
/// The graph the naming works over: one node per distinct `Rc`, with the
/// binder frame it sits under and the tree it expands to. Built once; a
/// threshold is then a cheap fold over it ([`choose`]), which is what lets the
/// instrument price several thresholds on one walk.
fn plan_of<'a>(root: &Rc<Type>, gamma: &'a LocalCtx) -> (Plan<'a>, u32) {
    let root_frame = Rc::new(Frame {
        parent: None,
        binder: None,
        // A context with an abstract base is a `meta fn`'s, where a mint's Δ
        // would have to mention the context variable: out of scope here.
        poison: !matches!(gamma.base, CtxBase::Nil),
        depth: 0,
    });
    let mut plan = Plan {
        gamma,
        nodes: Vec::new(),
        tm_ids: HashMap::new(),
        ty_ids: HashMap::new(),
        finish: Vec::new(),
        frames: Frames::default(),
        free_memo: HashMap::new(),
    };
    let root_id = plan.visit(&Kid::Ty(Rc::clone(root)), &root_frame);
    (plan, root_id)
}

/// One threshold's answer over a built [`Plan`]: which nodes are named, what
/// the spelling then costs, and what cleared the bar and could not be taken.
pub(crate) struct Choice {
    named: Vec<bool>,
    pub(crate) mints: u32,
    pub(crate) naive: u64,
    pub(crate) emitted: u64,
    pub(crate) declines: Declines,
}

fn choose(
    plan: &Plan<'_>,
    root_id: u32,
    cap: u32,
    threshold: u64,
    allow_types: bool,
    minimal: bool,
) -> Choice {
    let mut declines = Declines::default();
    let mut naive = vec![0u64; plan.nodes.len()];
    let mut cost = vec![0u64; plan.nodes.len()];
    let mut named = vec![false; plan.nodes.len()];
    let mut mints = 0u32;
    // Bottom-up: a node's cost is its own node plus its children's, with a
    // named child charged a reference. `finish` is a completion order, so one
    // forward pass over it is the fold.
    for &n in &plan.finish {
        let n = n as usize;
        let mut c = 1u64;
        let mut tree = 1u64;
        for &k in &plan.nodes[n].kids {
            let k = k as usize;
            tree = tree.saturating_add(naive[k]);
            c = c.saturating_add(if named[k] {
                plan.ref_cost(k, minimal)
            } else {
                cost[k]
            });
        }
        naive[n] = tree;
        cost[n] = c;
        if n as u32 == root_id {
            continue;
        }
        let shares = u64::from(plan.nodes[n].indeg).saturating_sub(1);
        let refc = plan.ref_cost(n, minimal);
        let saving = shares.saturating_mul(c.saturating_sub(refc));
        if shares == 0 || saving < threshold {
            continue;
        }
        let mut decline = |slot: &mut u64| {
            *slot += 1;
            declines.lost += saving;
        };
        if !plan.nodes[n].is_tm && !allow_types {
            decline(&mut declines.type_node);
            continue;
        }
        // §11.4's Δ is "Γ extended by the binders the node sits under", and
        // then a node reached under two chains cannot be named at all. With a
        // **minimal** Δ — the innermost entries the body actually reaches
        // into, the rest strengthened away — the two chains only have to
        // agree that far.
        let ok = if minimal {
            plan.nodes[n].min_k <= plan.nodes[n].agree
        } else {
            !plan.nodes[n].ambiguous
        };
        if !ok {
            decline(&mut declines.ambiguous);
            continue;
        }
        if plan.nodes[n].frame.poison {
            decline(&mut declines.foreign);
            continue;
        }
        if mints >= cap {
            decline(&mut declines.over_cap);
            continue;
        }
        // A **type** node is named only in the instrument's counting mode
        // (`allow_types`): the spelling would be `El (u^δ)` over a minted
        // *code*, which the rebuild below does not write, so such a node is
        // counted and left inline.
        named[n] = true;
        mints += 1;
    }
    let mut emitted = cost[root_id as usize];
    for n in 0..plan.nodes.len() {
        if named[n] {
            emitted = emitted.saturating_add(cost[n]);
        }
    }
    Choice {
        named,
        mints,
        naive: naive[root_id as usize],
        emitted,
        declines,
    }
}

/// Plan and rebuild in one call — the entry the landed device uses, and the
/// one this module's tests are written against. The instrument goes through
/// [`plan_of`]/[`choose`]/[`build_from`] instead, because it prices several
/// thresholds on one walk.
#[allow(dead_code)]
pub(crate) fn name(
    root: &Rc<Type>,
    gamma: &LocalCtx,
    cap: u32,
    threshold: u64,
    allow_types: bool,
    minter: &mut Minter<'_>,
) -> Naming {
    let (plan, root_id) = plan_of(root, gamma);
    let choice = choose(&plan, root_id, cap, threshold, allow_types, false);
    build_from(&plan, &choice, root, gamma, minter)
}

/// The rebuild: the graph with every named node replaced by `u^δ`, and the
/// bodies in dependency order. Split out so the instrument can price several
/// thresholds on one [`plan_of`] and still rebuild exactly once.
fn build_from(
    plan: &Plan<'_>,
    choice: &Choice,
    root: &Rc<Type>,
    gamma: &LocalCtx,
    minter: &mut Minter<'_>,
) -> Naming {
    let mut build = Build {
        plan,
        named: &choice.named,
        gamma,
        minter,
        tm_out: HashMap::new(),
        ty_out: HashMap::new(),
        minted: 0,
        refused: 0,
    };
    let root_out = match build.go(&Kid::Ty(Rc::clone(root))) {
        Kid::Ty(t) => t,
        Kid::Tm(_) => unreachable!(),
    };
    Naming {
        root: root_out,
        minted: build.minted,
        refused: build.refused,
        naive: choice.naive,
        emitted: choice.emitted,
        declines: choice.declines,
    }
}

struct Build<'a, 'm> {
    plan: &'a Plan<'a>,
    named: &'a [bool],
    gamma: &'a LocalCtx,
    minter: &'a mut Minter<'m>,
    tm_out: HashMap<usize, Rc<Term>>,
    ty_out: HashMap<usize, Rc<Type>>,
    minted: u32,
    refused: u32,
}

impl Build<'_, '_> {
    fn go(&mut self, kid: &Kid) -> Kid {
        match kid {
            Kid::Tm(t) => {
                let key = Rc::as_ptr(t) as usize;
                if let Some(out) = self.tm_out.get(&key) {
                    return Kid::Tm(Rc::clone(out));
                }
                let Some(&id) = self.plan.tm_ids.get(&key) else {
                    // Never visited (a subtree the planner did not enter):
                    // keep it verbatim, which names nothing and is always
                    // safe.
                    return Kid::Tm(Rc::clone(t));
                };
                let kids = self.kids(&slots_tm(t));
                let rebuilt = if kids.changed {
                    Rc::new(rebuild_tm(t, &kids.kids))
                } else {
                    Rc::clone(t)
                };
                // A named node the strict rule would refuse is never minted
                // here: `choose`'s `minimal` and `allow_types` are counting
                // modes, and this is where that stays true.
                let out = if self.named[id as usize]
                    && !self.plan.nodes[id as usize].ambiguous
                {
                    let ctx = ctx_of(self.gamma, &self.plan.nodes[id as usize].frame);
                    match (self.minter)(&ctx, &rebuilt) {
                        Some(var) => {
                            self.minted += 1;
                            Rc::new(Term::GlobalTm {
                                var,
                                subst: LocalSubst::id(&ctx),
                            })
                        }
                        None => {
                            self.refused += 1;
                            rebuilt
                        }
                    }
                } else {
                    rebuilt
                };
                self.tm_out.insert(key, Rc::clone(&out));
                Kid::Tm(out)
            }
            Kid::Ty(t) => {
                let key = Rc::as_ptr(t) as usize;
                if let Some(out) = self.ty_out.get(&key) {
                    return Kid::Ty(Rc::clone(out));
                }
                let kids = self.kids(&slots_ty(t));
                let out = if kids.changed {
                    Rc::new(rebuild_ty(t, &kids.kids))
                } else {
                    Rc::clone(t)
                };
                self.ty_out.insert(key, Rc::clone(&out));
                Kid::Ty(out)
            }
        }
    }

    fn kids(&mut self, slots: &[(Kid, Scope)]) -> Kids {
        let mut out = Vec::with_capacity(slots.len());
        let mut changed = false;
        for (child, _) in slots {
            let new = self.go(child);
            changed |= !same(child, &new);
            out.push(new);
        }
        Kids { kids: out, changed }
    }
}

struct Kids {
    kids: Vec<Kid>,
    changed: bool,
}

fn same(a: &Kid, b: &Kid) -> bool {
    match (a, b) {
        (Kid::Tm(a), Kid::Tm(b)) => Rc::ptr_eq(a, b),
        (Kid::Ty(a), Kid::Ty(b)) => Rc::ptr_eq(a, b),
        _ => false,
    }
}

// -- the spike's instrument ------------------------------------------------
//
// `HEATHER_RB=name`: run the readback and the naming at `build_ctor`, count
// what would be emitted, and **discard** the answer. The item still checks
// against the rewriter's reduct, so nothing on the commit path moves — this
// is the brief's step 0, the mints in a scratch world, counted.

pub(crate) fn counting() -> bool {
    static M: OnceLock<bool> = OnceLock::new();
    *M.get_or_init(|| std::env::var("HEATHER_RB").ok().as_deref() == Some("name"))
}

/// The reserved block's size — §11.4's "a mint that overflows the block
/// declines". The spike's default is generous; the landed device's comes from
/// the same counter.
pub(crate) fn cap() -> u32 {
    static M: OnceLock<u32> = OnceLock::new();
    *M.get_or_init(|| {
        std::env::var("HEATHER_RB_CAP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256)
    })
}

/// The Ψ slot a reserved-but-unminted block entry holds while the block is
/// padding. Never referenced: a mint past the block declines.
pub(crate) fn placeholder() -> GlobalBinding {
    GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: Rc::new(Type::Nat),
        level: Level::Zero,
        body: None,
    }
}

/// Ψ with a mint block of `cap` reserved slots at its innermost end, and the
/// local context and type the readback is given re-scoped into it. Every
/// reference the readback then writes is already numbered past the block —
/// the goal arena's own discipline (`goals.rs`'s `configure`), which is why
/// §11.4 proposes that mechanism and not an eager push.
pub(crate) fn padded(world: &GlobalCtx, cap: u32) -> GlobalCtx {
    let mut bindings = world.bindings.to_vec();
    bindings.extend((0..cap).map(|_| placeholder()));
    GlobalCtx::new(bindings)
}

pub(crate) fn at_build_ctor(world: &GlobalCtx, gamma: &LocalCtx, ty: &Type, fuel: u64) {
    if !counting() {
        return;
    }
    let (m, i) = crate::stats::current_item().unwrap_or(("-".into(), "-".into()));
    let cap = cap();
    let t0 = std::time::Instant::now();
    let padded_world = padded(world, cap);
    let gamma = gamma.shift_global(cap);
    let ty = ty.shift_global(cap);
    let Some(root) = crate::rbemit::whnf_type_from_value(&padded_world, &gamma, &ty, fuel) else {
        eprintln!("rb name item={m}::{i} DECLINED");
        return;
    };
    let root = Rc::new(root);
    // One walk, every threshold: the plan is the expensive half, and a
    // threshold is a fold over it. `ty=` is the same fold with shared **type**
    // nodes counted as nameable — what a device that minted a type's *code*
    // and spelled the occurrence `El (u^δ)` would emit (`code.rs`'s
    // `code_of` is that encoder, already in the tree). Counting only.
    let (plan, root_id) = plan_of(&root, &gamma);
    let mut cols = String::new();
    for t in THRESHOLDS {
        let tm = choose(&plan, root_id, cap, t, false, false);
        let ty = choose(&plan, root_id, cap, t, true, false);
        let min = choose(&plan, root_id, cap, t, true, true);
        cols.push_str(&format!(
            " T{t}={}/{}|ty={}/{}|min={}/{}",
            tm.mints, tm.emitted, ty.mints, ty.emitted, min.mints, min.emitted
        ));
    }
    let choice = choose(
        &plan,
        root_id,
        cap,
        THRESHOLD,
        std::env::var("HEATHER_RB_TYCODE").is_ok(),
        false,
    );

    // The minter the landed device would install, minus the commit path: each
    // mint's statement is **inferred** — kernel syntax is fully annotated
    // (ch. 04), so the readback has to supply only `Δ` — and the binding goes
    // into the scratch block, which is what makes the *next* mint's body
    // checkable against it. A refusal is a decline, so a mint the kernel will
    // not type leaves its component inline and the mints after it are still
    // measured honestly (an installed placeholder would fail every body that
    // referenced it and count one fault as many).
    let typing = std::env::var("HEATHER_RB_TYPE").is_ok();
    let mut slots = padded_world.bindings.to_vec();
    let world_base = world.bindings.len();
    let mut typed = 0u64;
    let mut untyped = 0u64;
    let mut stmt_nodes = 0u64;
    let mut next = 0u32;
    let mut minter = |ctx: &LocalCtx, body: &Rc<Term>| -> Option<GlobalVar> {
        if next >= cap {
            return None;
        }
        let j = next;
        if typing {
            let here = GlobalCtx::new(slots.clone());
            match heather_kernel::typing::infer_term(&here, 0, Layer::Code, ctx, body, fuel) {
                Ok((ty, level)) => {
                    typed += 1;
                    stmt_nodes += crate::rbcount::count_ty(&ty).nodes;
                    slots[world_base + j as usize] = GlobalBinding::defined_tm(
                        ctx.clone(),
                        Layer::Code,
                        Rc::new(ty),
                        level,
                        Rc::clone(body),
                    );
                }
                Err(e) => {
                    untyped += 1;
                    // Sixteen times the fuel, to separate "the kernel will not
                    // have this term" from "the kernel ran out of steps
                    // deciding": a mint's body is a *deep* normal form, and
                    // the conversions its annotations ask for are the round's
                    // own cost.
                    let richer = heather_kernel::typing::infer_term(
                        &here,
                        0,
                        Layer::Code,
                        ctx,
                        body,
                        fuel.saturating_mul(16),
                    );
                    let shown = format!("{body:?}");
                    eprintln!(
                        "rb name item={m}::{i} UNTYPED mint={j} ctx={} nodes={} err={e:?} \
                         retry={} body={}",
                        ctx.entries.len(),
                        crate::rbcount::count_tm(body).nodes,
                        if richer.is_ok() { "ok" } else { "fail" },
                        &shown[..shown.len().min(400)],
                    );
                    return None;
                }
            }
        }
        next += 1;
        Some(GlobalVar(cap - 1 - j))
    };
    let naming = build_from(&plan, &choice, &root, &gamma, &mut minter);
    drop(minter);

    // Does the readback's own answer type at all, before any naming? The
    // control for §12.6: a mint the kernel refuses is either a `Δ` this walk
    // derived wrongly or a sub-term that was never typable, and the root says
    // which.
    if std::env::var("HEATHER_RB_CHECK").is_ok() {
        let verdict =
            heather_kernel::typing::infer_type(&padded_world, 0, Layer::Code, &gamma, &root, fuel);
        eprintln!(
            "rb name item={m}::{i} ROOT={} err={:?}",
            if verdict.is_ok() { "ok" } else { "FAIL" },
            verdict.err(),
        );
    }

    let us = t0.elapsed().as_micros();
    let d = naming.declines;
    eprintln!(
        "rb name item={m}::{i} naive={} emitted={} mints={} stmt={stmt_nodes} typed={typed} \
         untyped={untyped} refused={} dty={} dforeign={} damb={} dcap={} dlost={} \
         us={us}{cols}",
        naming.naive,
        naming.emitted,
        naming.minted,
        naming.refused,
        d.type_node,
        d.foreign,
        d.ambiguous,
        d.over_cap,
        d.lost,
    );
}

#[cfg(test)]
mod tests {
    use heather_kernel::term::LocalVar;

    use super::*;

    const FUEL: u64 = 1 << 20;

    /// A `Succ` chain, which is `n` nodes of shared mass over whatever it
    /// bottoms out at — the smallest thing that can clear [`THRESHOLD`].
    fn chain(n: usize, base: Term) -> Rc<Term> {
        let mut t = Rc::new(base);
        for _ in 0..n {
            t = Rc::new(Term::Succ(t));
        }
        t
    }

    fn nat() -> Rc<Type> {
        Rc::new(Type::Nat)
    }

    fn id_of(lhs: &Rc<Term>, rhs: &Rc<Term>) -> Type {
        Type::Id {
            level: Level::Zero,
            ty: nat(),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        }
    }

    /// The test harness's minter: collect every `Δ ⊢ body` and hand back the
    /// reference the reserved block's `j`-th slot has.
    fn named(root: Type, gamma: &LocalCtx, cap: u32) -> (Naming, Vec<(LocalCtx, Rc<Term>)>) {
        let mut mints: Vec<(LocalCtx, Rc<Term>)> = Vec::new();
        let out = {
            let mut minter = |ctx: &LocalCtx, body: &Rc<Term>| {
                let j = mints.len() as u32;
                if j >= cap {
                    return None;
                }
                mints.push((ctx.clone(), Rc::clone(body)));
                Some(GlobalVar(cap - 1 - j))
            };
            name(&Rc::new(root), gamma, cap, THRESHOLD, false, &mut minter)
        };
        (out, mints)
    }

    /// The device's whole content: a sub-term spelled twice becomes one
    /// binding and two references, and the emitted count falls by its mass.
    #[test]
    fn a_shared_term_is_minted_once_and_referenced_at_both_sites() {
        let big = chain(200, Term::Zero);
        let (out, mints) = named(id_of(&big, &big), &LocalCtx::nil(), 8);
        assert_eq!(mints.len(), 1);
        assert_eq!(out.naive, 404);
        // The root is `Id(Nat; u^δ; u^δ)` — four nodes — plus the body.
        assert_eq!(out.emitted, 4 + 201);
        let Type::Id { lhs, rhs, .. } = &*out.root else {
            panic!("expected an `Id`, got {:?}", out.root);
        };
        assert!(matches!(&**lhs, Term::GlobalTm { var, .. } if *var == GlobalVar(7)));
        assert!(Rc::ptr_eq(lhs, rhs), "the two sites share one reference");
        assert!(mints[0].0.entries.is_empty());
    }

    /// The same, one binder down: the mint's `Δ` is `Γ` **extended by the
    /// binder the node sits under** (§11.4), and the use site is `u^δ` under
    /// that context's identity substitution — which is what makes naming
    /// anything but a closed sub-value possible at all. The named answer is
    /// checked by the kernel against a Ψ that holds the mint, which is the
    /// whole round's obligation in one assertion.
    #[test]
    fn a_mint_under_a_binder_carries_its_context_and_the_kernel_takes_it() {
        let big = chain(200, Term::Var(LocalVar(0)));
        let root = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: nat(),
            cod: Rc::new(id_of(&big, &big)),
        };
        let (out, mints) = named(root, &LocalCtx::nil(), 1);
        assert_eq!(mints.len(), 1);
        let (ctx, body) = &mints[0];
        assert_eq!(ctx.entries.len(), 1, "the binder is in the mint's Δ");

        let (ty, level) = heather_kernel::typing::infer_term(
            &GlobalCtx::new(Vec::new()),
            0,
            Layer::Code,
            ctx,
            body,
            FUEL,
        )
        .expect("a mint's type is inferable — kernel syntax is fully annotated");
        let psi = GlobalCtx::new(vec![GlobalBinding::defined_tm(
            ctx.clone(),
            Layer::Code,
            Rc::new(ty),
            level,
            Rc::clone(body),
        )]);
        heather_kernel::typing::check_type(
            &psi,
            0,
            Layer::Code,
            &LocalCtx::nil(),
            &out.root,
            &Level::Zero,
            FUEL,
        )
        .expect("the named answer is a type in the Ψ that holds its mints");
    }

    /// A shared **type** is not nameable: a Ψ type binding has no body, so
    /// there is nothing for a name to unfold to. It is counted, not guessed
    /// at.
    #[test]
    fn a_shared_type_node_declines_and_is_counted() {
        let mut big = nat();
        for _ in 0..100 {
            big = Rc::new(Type::Sigma {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst: nat(),
                snd: big,
            });
        }
        let root = Type::Sum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: Rc::clone(&big),
            rhs: Rc::clone(&big),
        };
        let (out, mints) = named(root, &LocalCtx::nil(), 8);
        assert!(mints.is_empty());
        assert_eq!(out.declines.type_node, 1);
        assert!(out.declines.lost > 0);
    }

    /// One `Rc` reached under two *different* binders is two different terms:
    /// its indices mean different things, and no single binding serves both.
    #[test]
    fn a_node_under_two_different_binders_is_not_named() {
        let big = chain(200, Term::Var(LocalVar(0)));
        let inner = Rc::new(id_of(&big, &big));
        let pi = |dom: Rc<Type>| {
            Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom,
                cod: Rc::clone(&inner),
            })
        };
        let root = Type::Sum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: pi(nat()),
            rhs: pi(Rc::new(Type::Unit { level: Level::Zero })),
        };
        let (out, mints) = named(root, &LocalCtx::nil(), 8);
        assert!(mints.is_empty(), "no mint may serve two contexts");
        assert!(out.declines.ambiguous > 0);
    }

    /// The reserved block is a *capacity*, and overflowing it is not an
    /// error: the component stays inline, which is stage one's behaviour and
    /// always safe.
    #[test]
    fn a_mint_past_the_reserved_block_declines_and_leaves_the_component_inline() {
        let big = chain(200, Term::Zero);
        let root = id_of(&big, &big);
        let (out, mints) = named(root.clone(), &LocalCtx::nil(), 0);
        assert!(mints.is_empty());
        assert_eq!(out.declines.over_cap, 1);
        assert_eq!(out.emitted, out.naive);
        assert_eq!(*out.root, root);
    }
}
