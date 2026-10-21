//! Export of checked kernel declarations to Lean 4 and Rocq (Coq), through
//! one target-neutral intermediate language (`docs/export-fragment-design.md`).
//!
//! Prototype scope, stated by what it refuses: the translation is
//! syntax-directed over kernel terms, total on the *layer-free* fragment
//! (no `box`, `letbox`, code recursors, context or type meta-functions, no
//! global type variables, no universe polymorphism, empty local contexts on
//! globals) and refuses everything else with a named [`Refusal`]. A
//! declaration that mentions a refused one is refused too, so what is printed
//! is closed.
//!
//! The intermediate language [`Hx`] is a pure type system with constants:
//! every kernel former becomes an application of a **prelude constant**
//! (`Hx.pair`, `Hx.J`, `Hx.elimNat`, …) to all of its annotations. The two
//! printers are then dumb, and the only per-target trusted text is the hand
//! written prelude (`prelude/Hx.lean`, `prelude/Hx.v`). Checked spellings
//! (`pair@`, `fst@`, …) carry no components; they become [`Hx::Hole`]s that
//! the target's elaborator fills from the expected or inferred type. That is
//! the one place the prototype leans on an elaborator, and the design doc
//! says how a typed exporter removes it.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{Defs, whnf_term_delta, whnf_type_delta};
use heather_kernel::subst::local_bound_ty;
use heather_kernel::term::{CtxBase, GlobalBinding, GlobalCtx, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type};
use heather_kernel::typing::{DEFAULT_FUEL, spell_checked_in_code, spell_checked_in_code_ty};
use std::cell::RefCell;
use std::sync::Arc as Rc;
use std::fmt::Write as _;

mod wf;

/// A universe level of the exported fragment: closed, because the library is
/// universe-monomorphic (`UPi` is layer m, which declarations never use).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lvl(pub u64);

/// The intermediate language: de Bruijn terms over prelude constants.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Hx {
    Var(u32),
    /// `Type l` (Russell): the image of both `Ty l` and the code `TmTy l`.
    Sort(Lvl),
    Pi(Box<Hx>, Box<Hx>),
    Lam(Box<Hx>, Box<Hx>),
    App(Box<Hx>, Box<Hx>),
    /// A prelude constant at explicit levels.
    Const(&'static str, Vec<Lvl>),
    /// An exported declaration, by absolute Ψ index.
    Global(usize),
    /// A constant only the target has, by Heather-style key, at raw target
    /// levels: a `Wf` realisation's constructors, recursor and helpers
    /// (`wf.rs`).
    Named(String, Vec<u64>),
    NatLit(String),
    /// A component the kernel term does not spell (a checked spelling's
    /// erased annotation); the target elaborator recovers it.
    Hole,
}

/// `Wf` has a realisation per target still to build: native inductives in
/// Lean, the positivity bypass in Rocq (design §5.1).
const WF: &str = "Wf (no target realisation yet: issues/export-wf-native-inductives.md)";

/// Why a term or declaration is outside the fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal(pub String);

type R<T> = Result<T, Refusal>;

fn refuse<T>(what: &str) -> R<T> {
    Err(Refusal(what.to_string()))
}

fn lvl(l: &Level) -> R<Lvl> {
    Ok(Lvl(match l {
        Level::Zero => 0,
        Level::Succ(l) => lvl(l)?.0 + 1,
        Level::Max(a, b) => lvl(a)?.0.max(lvl(b)?.0),
        Level::Var(_) => return refuse("universe variable (level polymorphism)"),
        Level::Omega => return refuse("level ω"),
    }))
}

fn app(f: Hx, args: Vec<Hx>) -> Hx {
    args.into_iter().fold(f, |f, a| Hx::App(Box::new(f), Box::new(a)))
}

fn konst(name: &'static str, levels: &[&Level], args: Vec<Hx>) -> R<Hx> {
    let levels = levels.iter().map(|l| lvl(l)).collect::<R<Vec<_>>>()?;
    Ok(app(Hx::Const(name, levels), args))
}

fn lam(dom: Hx, body: Hx) -> Hx {
    Hx::Lam(Box::new(dom), Box::new(body))
}

/// A binder whose domain the prelude constant's type determines: printed as
/// a hole, which both targets infer from the expected type.
fn bind(body: Hx) -> Hx {
    lam(Hx::Hole, body)
}

/// The translation of one declaration's types and terms. `at` is the
/// declaration's absolute Ψ index, which resolves its global variables.
struct Tr<'a> {
    at: usize,
    /// The declaration's own Ψ prefix: what its globals unfold to.
    psi: &'a GlobalCtx,
    /// One entry per enclosing binder, innermost last: the canonical element
    /// of its domain when that domain is a closed singleton. Closed, so it
    /// needs no shifting to be used under further binders.
    ctx: RefCell<Vec<Option<Hx>>>,
    /// The tier-1 declarations met so far (`wf.rs`).
    wf: &'a wf::WfTable,
}

/// Fuel for the exporter's own reductions (the collapse test); a type that
/// does not settle within it is simply not collapsed.
const FUEL: u64 = 1 << 16;

fn lmax(a: &Level, b: &Level) -> Level {
    Level::max(a.clone(), b.clone())
}

impl Tr<'_> {
    /// The level of `t` when `t` is a **closed singleton**: a closed type
    /// whose whnf is `Unit`, an `sEq` between convertible endpoints, or a
    /// non-dependent `Σ` of singletons. Heather's η makes every two terms of
    /// such a type convertible, neutrals included; the targets' structure η
    /// does not reach two neutrals (design §5.2). So a term whose type is
    /// known to be a closed singleton translates to that type's canonical
    /// element ([`Self::canon`]), and a neutral the exporter cannot see the
    /// type of meets it through structure η, which fires against a
    /// constructor. The type itself is translated as written: collapsing it
    /// to `Unit` would disagree with the δ-unfolding of an open definition
    /// that reaches the same type only by substitution.
    fn singleton(&self, t: &Type) -> Option<Level> {
        if !matches!(t, Type::Unit { .. } | Type::SEq { .. } | Type::Sigma { .. } | Type::El { .. } | Type::Vec { .. }) {
            return None;
        }
        if local_bound_ty(&Rc::new(t.clone())) != 0 {
            return None;
        }
        let nil = LocalCtx::nil();
        let w = whnf_type_delta(t, &nil, Defs::transparent(self.psi), FUEL).ok()?;
        match &w {
            Type::Unit { level } => Some(level.clone()),
            Type::SEq { level, lhs, rhs, .. } => {
                let l = whnf_term_delta(lhs, &nil, Defs::transparent(self.psi), FUEL).ok()?;
                let r = whnf_term_delta(rhs, &nil, Defs::transparent(self.psi), FUEL).ok()?;
                (l == r).then(|| level.clone())
            }
            Type::Sigma { fst_level, snd_level, fst, snd } if local_bound_ty(snd) == 0 => {
                self.singleton(fst)?;
                self.singleton(snd)?;
                Some(lmax(fst_level, snd_level))
            }
            _ => None,
        }
    }

    /// The canonical element of a closed singleton ([`Self::singleton`]):
    /// `tt`, `srefl`, or a pair of canonical elements.
    fn canon(&self, t: &Type) -> Option<R<Hx>> {
        self.singleton(t)?;
        let nil = LocalCtx::nil();
        let w = whnf_type_delta(t, &nil, Defs::transparent(self.psi), FUEL).ok()?;
        Some(match &w {
            Type::Unit { level } => konst("tt", &[level], vec![]),
            Type::SEq { level, ty, lhs, .. } => (|| konst("srefl", &[level], vec![self.ty(ty)?, self.tm(lhs)?]))(),
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                let (a, b) = (self.canon(fst)?, self.canon(snd)?);
                (|| konst(
                    "pair",
                    &[fst_level, snd_level],
                    vec![self.ty(fst)?, self.lam_ty(fst, snd)?, a?, b?],
                ))()
            }
            _ => return None,
        })
    }

    /// Translate under one binder whose domain is `dom` (`None` when the
    /// exporter does not have it at hand).
    fn under<T>(&self, dom: Option<&Type>, f: impl FnOnce() -> R<T>) -> R<T> {
        let entry = match dom.and_then(|d| self.canon(d)) {
            Some(c) => Some(c?),
            None => None,
        };
        self.ctx.borrow_mut().push(entry);
        let out = f();
        self.ctx.borrow_mut().pop();
        out
    }

    /// `fun (x : dom) => cod` for a type family.
    fn lam_ty(&self, dom: &Type, cod: &Type) -> R<Hx> {
        Ok(lam(self.ty(dom)?, self.under(Some(dom), || self.ty(cod))?))
    }

    /// `fun (x : dom) => f()`, with `f` translated under the binder.
    fn bound(&self, dom: &Type, f: impl FnOnce() -> R<Hx>) -> R<Hx> {
        Ok(lam(self.ty(dom)?, self.under(Some(dom), f)?))
    }

    /// `n` binders the prelude constant's type determines, none of them at
    /// a domain the exporter has at hand.
    fn binds<T>(&self, n: usize, f: impl FnOnce() -> R<T>) -> R<T> {
        match n {
            0 => f(),
            _ => self.under(None, || self.binds(n - 1, f)),
        }
    }

    fn global(&self, var: u32, subst: &LocalSubst) -> R<Hx> {
        match subst.tail {
            // `·^k`: the empty substitution weakened to the ambient Γ — a
            // closed global used under k binders.
            SubstTail::Empty { base: CtxBase::Nil, .. } if subst.terms.is_empty() => {}
            _ => return refuse("global with a non-empty local substitution"),
        }
        match self.at.checked_sub(1 + var as usize) {
            Some(abs) => Ok(Hx::Global(abs)),
            None => refuse("global variable out of scope"),
        }
    }

    fn ty(&self, t: &Type) -> R<Hx> {
        Ok(match t {
            Type::Nat => Hx::Const("Nat", vec![]),
            Type::Pi { dom, cod, .. } => Hx::Pi(Box::new(self.ty(dom)?), Box::new(self.under(Some(dom), || self.ty(cod))?)),
            Type::Ty(l) => Hx::Sort(lvl(l)?),
            Type::El { tm, .. } => self.tm(tm)?,
            Type::Id { level, ty, lhs, rhs } => konst("Id", &[level], vec![self.ty(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Type::SEq { level, ty, lhs, rhs } => konst("SEq", &[level], vec![self.ty(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Type::SEmpty { level } => konst("SEmpty", &[level], vec![])?,
            Type::Squash { level, ty } => konst("Squash", &[level], vec![self.ty(ty)?])?,
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                konst("Sig", &[fst_level, snd_level], vec![self.ty(fst)?, self.lam_ty(fst, snd)?])?
            }
            Type::Unit { level } => konst("Unit", &[level], vec![])?,
            Type::Empty { level } => konst("Empty", &[level], vec![])?,
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                konst("Sum", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?])?
            }
            Type::W { shape_level, pos_level, shape, pos } => {
                konst("W", &[shape_level, pos_level], vec![self.ty(shape)?, self.lam_ty(shape, pos)?])?
            }
            Type::Vec { level, elem, len } => konst("Vec", &[level], vec![self.ty(elem)?, self.tm(len)?])?,
            Type::Fin { len } => konst("Fin", &[], vec![self.tm(len)?])?,
            Type::Wf { shape, .. } => self.wf_type(shape)?,
            Type::DVec { .. } | Type::IWf { .. } => return refuse("DVec/IWf (no code yet; not in declarations)"),
            Type::UPi { .. } => return refuse("ΠΠ (universe polymorphism)"),
            Type::GlobalTy { .. } => return refuse("global type variable (layer c/p meta binding)"),
            Type::CtxPi { .. } | Type::TyPi { .. } => return refuse("context/type meta-function"),
            Type::CodeTy { .. } | Type::CodeTm { .. } => return refuse("contextual (boxed) type"),
        })
    }

    /// The type of a term the exporter can read off without inference, when
    /// that type is closed: a variable's domain is in `ctx` already, so this
    /// covers globals, applications and projections.
    fn known_ty(&self, t: &Term) -> Option<Type> {
        match t {
            Term::GlobalTm { var, subst } if subst.terms.is_empty() => {
                let abs = self.at.checked_sub(1 + var.0 as usize)?;
                match self.psi.bindings.get(abs)? {
                    GlobalBinding::Tm { ctx, ty, .. } if ctx.is_empty() => Some((**ty).clone()),
                    _ => None,
                }
            }
            Term::App { cod, .. } if local_bound_ty(cod) == 0 => Some((**cod).clone()),
            Term::Fst { fst_ty, .. } => Some((**fst_ty).clone()),
            Term::Snd { snd_ty, .. } if local_bound_ty(snd_ty) == 0 => Some((**snd_ty).clone()),
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, .. } => Some(Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: fst_ty.clone(),
                snd: snd_ty.clone(),
            }),
            Term::SRefl { level, ty, tm } => {
                Some(Type::SEq { level: level.clone(), ty: ty.clone(), lhs: tm.clone(), rhs: tm.clone() })
            }
            _ => None,
        }
    }

    fn tm(&self, t: &Term) -> R<Hx> {
        if let Term::Var(v) = t {
            let ctx = self.ctx.borrow();
            if let Some(Some(c)) = ctx.len().checked_sub(1 + v.0 as usize).map(|i| &ctx[i]) {
                return Ok(c.clone());
            }
        }
        if let Some(c) = self.known_ty(t).and_then(|ty| self.canon(&ty)) {
            return c;
        }
        Ok(match t {
            Term::Var(v) => Hx::Var(v.0),
            // ---- codes decode to themselves (Tarski → Russell) ----
            Term::TmNat => Hx::Const("Nat", vec![]),
            Term::TmPi { dom, cod, .. } => Hx::Pi(Box::new(self.tm(dom)?), Box::new(self.binds(1, || self.tm(cod))?)),
            Term::TmTy(l) => Hx::Sort(lvl(l)?),
            Term::TmId { level, ty, lhs, rhs } => konst("Id", &[level], vec![self.tm(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Term::TmSEq { level, ty, lhs, rhs } => konst("SEq", &[level], vec![self.tm(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Term::TmSEmpty { level } => konst("SEmpty", &[level], vec![])?,
            Term::TmSquash { level, ty } => konst("Squash", &[level], vec![self.tm(ty)?])?,
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                konst("Sig", &[fst_level, snd_level], vec![self.tm(fst)?, lam(self.tm(fst)?, self.binds(1, || self.tm(snd))?)])?
            }
            Term::TmUnit { level } => konst("Unit", &[level], vec![])?,
            Term::TmEmpty { level } => konst("Empty", &[level], vec![])?,
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                konst("Sum", &[lhs_level, rhs_level], vec![self.tm(lhs)?, self.tm(rhs)?])?
            }
            Term::TmW { shape_level, pos_level, shape, pos } => {
                konst("W", &[shape_level, pos_level], vec![self.tm(shape)?, lam(self.tm(shape)?, self.binds(1, || self.tm(pos))?)])?
            }
            Term::TmVec { level, elem, len } => konst("Vec", &[level], vec![self.tm(elem)?, self.tm(len)?])?,
            Term::TmFin { len } => konst("Fin", &[], vec![self.tm(len)?])?,
            Term::TmWf { level, shape, .. } => self.wf_type(&Type::El { level: level.clone(), tm: shape.clone() })?,
            // ---- Nat ----
            Term::Zero => Hx::NatLit("0".into()),
            Term::NatLit(n) => Hx::NatLit(n.to_string()),
            Term::Succ(n) => konst("succ", &[], vec![self.tm(n)?])?,
            Term::ElimNat { level, motive, base, step, scrut } => konst(
                "elimNat",
                &[level],
                vec![
                    self.bound(&Type::Nat, || self.ty(motive))?,
                    self.tm(base)?,
                    self.bound(&Type::Nat, || self.bound(motive, || self.tm(step)))?,
                    self.tm(scrut)?,
                ],
            )?,
            // ---- Id ----
            Term::Refl { level, ty, tm } => konst("refl", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => konst(
                "J",
                &[ty_level, motive_level],
                vec![
                    self.ty(ty)?,
                    self.tm(lhs)?,
                    self.bound(ty, || {
                        let id = Type::Id {
                            level: ty_level.clone(),
                            ty: Rc::new(ty.shift_local(1)),
                            lhs: Rc::new(lhs.shift_local(1)),
                            rhs: Rc::new(Term::Var(LocalVar(0))),
                        };
                        self.bound(&id, || self.ty(motive))
                    })?,
                    self.tm(case)?,
                    self.tm(rhs)?,
                    self.tm(proof)?,
                ],
            )?,
            // ---- strict equality and squash ----
            Term::SRefl { level, ty, tm } => konst("srefl", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            // At a singleton equality the transport is its payload: the two
            // endpoints convert, which is the strip rule.
            Term::Transp { ty_level, ty, lhs, rhs, tm, .. }
                if self
                    .singleton(&Type::SEq { level: ty_level.clone(), ty: ty.clone(), lhs: lhs.clone(), rhs: rhs.clone() })
                    .is_some() =>
            {
                self.tm(tm)?
            }
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => konst(
                "transp",
                &[ty_level, motive_level],
                vec![
                    self.ty(ty)?,
                    self.bound(ty, || self.ty(motive))?,
                    self.tm(lhs)?,
                    self.tm(rhs)?,
                    self.tm(proof)?,
                    self.tm(tm)?,
                ],
            )?,
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                konst(
                    "elimSEmpty",
                    &[level, scrut_level],
                    vec![self.bound(&Type::SEmpty { level: scrut_level.clone() }, || self.ty(motive))?, self.tm(scrut)?],
                )?
            }
            Term::Squash { level, ty, tm } => konst("squash", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => konst(
                "elimSquash",
                &[src_level, dst_level],
                vec![
                    self.ty(src_ty)?,
                    self.bound(&Type::Squash { level: src_level.clone(), ty: src_ty.clone() }, || self.ty(motive))?,
                    self.bound(src_ty, || self.tm(case))?,
                    self.tm(scrut)?,
                ],
            )?,
            // ---- Σ ----
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => konst(
                "pair",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, self.lam_ty(fst_ty, snd_ty)?, self.tm(fst)?, self.tm(snd)?],
            )?,
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => konst(
                "fst",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, self.lam_ty(fst_ty, snd_ty)?, self.tm(pair)?],
            )?,
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => konst(
                "snd",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, self.lam_ty(fst_ty, snd_ty)?, self.tm(pair)?],
            )?,
            // ---- checked spellings: the components are the target's to infer ----
            Term::PairAt { ty, fst, snd } => self.at_ty(ty, "pair", 2, vec![self.tm(fst)?, self.tm(snd)?])?,
            Term::InlAt { ty, val } => self.at_ty(ty, "inl", 2, vec![self.tm(val)?])?,
            Term::InrAt { ty, val } => self.at_ty(ty, "inr", 2, vec![self.tm(val)?])?,
            Term::FstAt { pair } => app(Hx::Const("fst", vec![]), vec![Hx::Hole, Hx::Hole, self.tm(pair)?]),
            Term::SndAt { pair } => app(Hx::Const("snd", vec![]), vec![Hx::Hole, Hx::Hole, self.tm(pair)?]),
            Term::AppAt { fun, arg } => app(self.tm(fun)?, vec![self.tm(arg)?]),
            // ---- Unit, Empty, sums ----
            Term::Triv { level } => konst("tt", &[level], vec![])?,
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                konst(
                    "elimEmpty",
                    &[level, scrut_level],
                    vec![self.bound(&Type::Empty { level: scrut_level.clone() }, || self.ty(motive))?, self.tm(scrut)?],
                )?
            }
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
                konst("inl", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?, self.tm(val)?])?
            }
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
                konst("inr", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?, self.tm(val)?])?
            }
            Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, scrut } => konst(
                "case",
                &[lhs_level, rhs_level, motive_level],
                vec![
                    self.ty(lhs)?,
                    self.ty(rhs)?,
                    self.bound(
                        &Type::Sum {
                            lhs_level: lhs_level.clone(),
                            rhs_level: rhs_level.clone(),
                            lhs: lhs.clone(),
                            rhs: rhs.clone(),
                        },
                        || self.ty(motive),
                    )?,
                    self.bound(lhs, || self.tm(case_l))?,
                    self.bound(rhs, || self.tm(case_r))?,
                    self.tm(scrut)?,
                ],
            )?,
            // ---- W and Wf ----
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => konst(
                "sup",
                &[shape_level, pos_level],
                vec![self.ty(shape_ty)?, self.lam_ty(shape_ty, pos_ty)?, self.tm(label)?, self.tm(children)?],
            )?,
            Term::ElimW { shape_level, pos_level, motive_level, shape, pos, motive, step, scrut } => konst(
                "elimW",
                &[shape_level, pos_level, motive_level],
                vec![
                    self.ty(shape)?,
                    self.lam_ty(shape, pos)?,
                    self.bound(
                        &Type::W {
                            shape_level: shape_level.clone(),
                            pos_level: pos_level.clone(),
                            shape: shape.clone(),
                            pos: pos.clone(),
                        },
                        || self.ty(motive),
                    )?,
                    // The step's `f` and `ih` domains are left to the target
                    // (a hole): the kernel route refuses it.
                    lam(self.ty(shape)?, bind(bind(self.under(Some(shape), || self.binds(2, || self.tm(step)))?))),
                    self.tm(scrut)?,
                ],
            )?,
            Term::Supf { shape, label, children, .. } => self.wf_supf(shape, label, children)?,
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                self.wf_elim(level, motive_level, shape, arity, motive, step, scrut)?
            }
            Term::Supi { .. } | Term::ElimIWf { .. } => return refuse("IWf (no code yet; not in declarations)"),
            // ---- functions ----
            Term::Lam { dom, body, .. } => lam(self.ty(dom)?, self.under(Some(dom), || self.tm(body))?),
            Term::App { fun, arg, .. } => app(self.tm(fun)?, vec![self.tm(arg)?]),
            Term::GlobalTm { var, subst } => self.global(var.0, subst)?,
            Term::ULam { .. } | Term::UApp { .. } => return refuse("universe abstraction/application"),
            Term::CtxLam { .. } | Term::CtxApp { .. } | Term::TyLam { .. } | Term::TyApp { .. } => {
                return refuse("context/type meta-function");
            }
            Term::BoxTy(_) | Term::BoxTm(_) | Term::LetBoxTy { .. } | Term::LetBoxTm { .. } => {
                return refuse("box/letbox (code layer)");
            }
            Term::ElimCodeTy { .. } | Term::ElimCodeTm { .. } => return refuse("code recursor"),
        })
    }

    /// A checked-spelling intro: `ty`, when present, is the un-reduced type
    /// it was checked at; the prelude constant's own components are holes.
    fn at_ty(&self, ty: &Option<std::sync::Arc<Type>>, name: &'static str, holes: usize, args: Vec<Hx>) -> R<Hx> {
        let mut all = vec![Hx::Hole; holes];
        all.extend(args);
        let t = app(Hx::Const(name, vec![]), all);
        Ok(match ty {
            Some(ty) => app(Hx::Const("the", vec![]), vec![self.ty(ty)?, t]),
            None => t,
        })
    }
}

/// One exported declaration.
#[derive(Clone, Debug)]
pub struct Decl {
    pub abs: usize,
    /// The module-qualified Heather name (`nat::Nat::add`), when the
    /// binding has one.
    pub name: Option<String>,
    pub ty: Hx,
    /// The definition's body, or the proof of a theorem; `None` for an
    /// assumption (an axiom, or a theorem whose proof Ψ did not keep) and
    /// for an inductive.
    pub body: Option<Hx>,
    /// Set when the binding is a tier-1 type code realised as a native
    /// inductive (`wf.rs`); `ty` is then the inductive's type.
    pub inductive: Option<Inductive>,
    /// Target-only definitions to declare just before this one (the
    /// eliminators it is the first to use) and just after it.
    pub before: Vec<Aux>,
    pub after: Vec<Aux>,
}

/// A native inductive: its parameters are the first `nparams` binders of its
/// type and of each constructor's.
#[derive(Clone, Debug)]
pub struct Inductive {
    pub nparams: usize,
    /// Each constructor's key and full type.
    pub ctors: Vec<(String, Hx)>,
}

/// A definition the target needs that Ψ has no binding for.
#[derive(Clone, Debug)]
pub struct Aux {
    pub name: String,
    pub ty: Hx,
    pub body: Hx,
}

/// What the exporter reads: Ψ, plus what the elaborator knows beside it.
/// The kernel crate cannot see the elaborator, so the two are lookups.
pub struct Source<'a> {
    pub psi: &'a GlobalCtx,
    /// A theorem's proof by absolute index, when Ψ itself keeps none
    /// (`Elaborator::export_proof`).
    pub proof: &'a dyn Fn(usize) -> Option<std::sync::Arc<Term>>,
    /// A binding's module-qualified name (`Elaborator::global_key_at`).
    pub name: &'a dyn Fn(usize) -> Option<String>,
    /// A nominal tag's constructor names, in declaration order
    /// (`Elaborator::constructor_names`): what a native inductive's
    /// constructors are called.
    pub ctors: &'a dyn Fn(u64) -> Option<Vec<String>>,
}

impl<'a> Source<'a> {
    /// Ψ alone: sealed proofs only, and no names.
    pub fn psi(psi: &'a GlobalCtx) -> Source<'a> {
        Source { psi, proof: &|_| None, name: &|_| None, ctors: &|_| None }
    }
}

/// One binding's export: its index, its Heather name, and the declaration
/// or why it was refused.
#[derive(Clone, Debug)]
pub struct Exported {
    pub abs: usize,
    pub name: Option<String>,
    pub decl: R<Decl>,
}

/// Translate every binding of Ψ. A binding is refused when it is outside the
/// fragment *or mentions a refused binding*, so the `Ok` declarations are
/// closed under dependency.
pub fn export(src: &Source) -> Vec<Exported> {
    let psi = src.psi;
    let mut out: Vec<Exported> = Vec::new();
    let mut refused = vec![false; psi.bindings.len()];
    let table = wf::WfTable::default();
    for (abs, b) in psi.bindings.iter().enumerate() {
        let prefix = psi.prefix(abs);
        let tr = Tr { at: abs, psi: &prefix, ctx: RefCell::new(Vec::new()), wf: &table };
        let mut name = (src.name)(abs);
        table.wanted.borrow_mut().clear();
        let decl = (|| -> R<Decl> {
            let GlobalBinding::Tm { ctx, ty, body, level, .. } = b else {
                return refuse("context or type global binding");
            };
            if ctx.len() != 0 {
                return refuse("global over a non-empty local context Δ");
            }
            let proof = body.clone().or_else(|| psi.sealed_proof(abs).cloned()).or_else(|| (src.proof)(abs));
            // The checked spellings first: the kernel's own `⌊·⌋` writes
            // each one's components back, so the translation never guesses
            // them (design §5.6). Statements are types, checked at layer p.
            let nil = LocalCtx::nil();
            let spelled_ty = spell_checked_in_code_ty(&prefix, 0, Layer::Prog, &nil, ty.clone(), level, DEFAULT_FUEL)
                .map_err(|e| Refusal(format!("statement spelling: {e:?}")))?;
            // A body the eager checker cannot spell (it refused two of the
            // 387 bindings in the `list` closure) keeps its checked
            // spellings, which print as holes for the target to fill.
            let spelled = proof.map(|t| {
                spell_checked_in_code(&prefix, 0, Layer::Code, &nil, Rc::clone(&t), ty, level, DEFAULT_FUEL).unwrap_or(t)
            });
            if let Some(code) = body {
                if let Some(w) = tr.register_wf(name.as_deref(), code, ty_tag_ctors(src, &prefix, code))? {
                    name = Some(w.key.clone());
                    return tr.wf_inductive(&w, tr.ty(&spelled_ty)?);
                }
            }
            let mut d = Decl {
                abs,
                name: name.clone(),
                ty: tr.ty(&spelled_ty)?,
                body: spelled.map(|t| tr.tm(&t)).transpose()?,
                inductive: None,
                before: Vec::new(),
                after: Vec::new(),
            };
            // The eliminators this declaration is the first to use, each
            // translated where its declaration is.
            let wanted = std::mem::take(&mut *table.wanted.borrow_mut());
            for (tag, ml) in wanted {
                if !table.emitted.borrow_mut().insert((tag, ml)) {
                    continue;
                }
                let w = table.by_tag.borrow()[&tag].clone();
                let at = Tr { at: w.abs, psi: &w.psi, ctx: RefCell::new(Vec::new()), wf: &table };
                match at.wf_elim_def(&w, ml) {
                    Ok(aux) => d.before.push(aux),
                    Err(e) => {
                        table.emitted.borrow_mut().remove(&(tag, ml));
                        return Err(e);
                    }
                }
            }
            if let Some(dep) = mentions(&d).into_iter().find(|&g| refused[g]) {
                let dep = (src.name)(dep).unwrap_or_else(|| format!("g{dep}"));
                return Err(Refusal(format!("mentions refused declaration {dep}")));
            }
            Ok(d)
        })();
        refused[abs] = decl.is_err();
        out.push(Exported { abs, name, decl });
    }
    out
}

/// The constructor names of the tier-1 declaration whose type code `code`
/// is, by the tag its shape carries (read again by `register_wf`; here only
/// to name things).
fn ty_tag_ctors(src: &Source, prefix: &GlobalCtx, code: &Term) -> Option<Vec<String>> {
    let (mut cur, mut depth) = (code, 0);
    while let Term::Lam { body, .. } = cur {
        (cur, depth) = (body, depth + 1);
    }
    let Term::TmWf { level, shape, .. } = cur else { return None };
    let shape = Type::El { level: level.clone(), tm: Rc::clone(shape) };
    (src.ctors)(Tr::tag_in(prefix, &shape, depth)?)
}

fn mentions(d: &Decl) -> Vec<usize> {
    fn go(t: &Hx, out: &mut Vec<usize>) {
        match t {
            Hx::Global(g) => out.push(*g),
            Hx::Pi(a, b) | Hx::Lam(a, b) | Hx::App(a, b) => {
                go(a, out);
                go(b, out);
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(&d.ty, &mut out);
    if let Some(b) = &d.body {
        go(b, &mut out);
    }
    for (_, t) in d.inductive.iter().flat_map(|i| &i.ctors) {
        go(t, &mut out);
    }
    for a in d.before.iter().chain(&d.after) {
        go(&a.ty, &mut out);
        go(&a.body, &mut out);
    }
    out.retain(|&g| g != d.abs);
    out
}

// ---------------------------------------------------------------------------
// Printers. Both name bound variables `x<depth>` and globals `g<abs>`.

/// Which target a printer writes for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Lean,
    Coq,
}

struct Printer {
    target: Target,
    out: String,
    /// The target spelling of each exported binding, by absolute index.
    names: Vec<String>,
}

/// Lean's keywords that can also be Heather name components; a component
/// that is one, or is not a plain identifier, is written `«…»`.
const LEAN_KEYWORDS: &[&str] = &[
    "fun", "at", "by", "do", "then", "else", "if", "let", "in", "have", "show", "from", "match", "with", "end",
    "where", "deriving", "instance", "structure", "class", "theorem", "def", "axiom", "example", "open",
    "namespace", "section", "universe", "variable", "import", "Type", "Sort", "Prop", "forall", "exists",
    "calc", "mut", "for", "unless", "return", "try", "catch", "finally", "local", "private", "protected",
];

fn plain_ident(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// The target spelling of a module-qualified Heather name. Lean keeps the
/// structure (`nat::Nat::add` is `Heather.nat.Nat.add`); Rocq identifiers
/// have no dots inside a file, so its components join with `__`.
fn target_name(target: Target, key: &str) -> String {
    let parts: Vec<&str> = key.split("::").collect();
    match target {
        Target::Lean => {
            let parts: Vec<String> = parts
                .iter()
                .map(|p| if plain_ident(p) && !LEAN_KEYWORDS.contains(p) { p.to_string() } else { format!("«{p}»") })
                .collect();
            format!("Heather.{}", parts.join("."))
        }
        Target::Coq => {
            let parts: Vec<String> = parts
                .iter()
                .map(|p| p.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect())
                .collect();
            format!("H__{}", parts.join("__"))
        }
    }
}

/// One spelling per binding: its name where it has one, `g<abs>` where it
/// has none or where the name is already taken.
fn spellings(target: Target, exported: &[Exported]) -> Vec<String> {
    let mut seen = std::collections::HashSet::new();
    let len = exported.iter().map(|e| e.abs + 1).max().unwrap_or(0);
    let mut names = (0..len).map(|g| format!("g{g}")).collect::<Vec<_>>();
    for e in exported {
        if let Some(key) = &e.name {
            let n = target_name(target, key);
            if seen.insert(n.clone()) {
                names[e.abs] = n;
            }
        }
    }
    names
}

impl Printer {
    fn level(&self, l: Lvl) -> String {
        match self.target {
            Target::Lean => l.0.to_string(),
            // Closed levels are a chain of global universes in the prelude
            // (Rocq instances cannot be algebraic, and need not be here).
            Target::Coq if l.0 == 0 => "Set".into(),
            Target::Coq => format!("Hx.u{}", l.0),
        }
    }

    /// Print `t`, parenthesised only where it is an argument (`arg`) and not
    /// an atom. Lean's parser is far from linear in parenthesis nesting: a
    /// fully parenthesised library file spent nearly all its check time
    /// parsing.
    fn term(&mut self, t: &Hx, depth: u32, arg: bool) {
        let atom = match t {
            Hx::Var(_) | Hx::Hole | Hx::NatLit(_) => true,
            // Rocq parses `f @c` as a syntax error, so there a constant is
            // an atom only in head position.
            Hx::Const(..) | Hx::Global(_) | Hx::Named(..) => self.target == Target::Lean,
            Hx::Sort(_) => self.target == Target::Coq,
            Hx::Pi(..) | Hx::Lam(..) | Hx::App(..) => false,
        };
        let open = arg && !atom;
        if open {
            self.out.push('(');
        }
        match t {
            Hx::Var(i) => {
                let _ = write!(self.out, "x{}", depth - 1 - i);
            }
            Hx::Sort(l) => {
                let _ = match self.target {
                    Target::Lean => write!(self.out, "Type {}", self.level(*l)),
                    Target::Coq => write!(self.out, "Type@{{{}}}", self.level(*l)),
                };
            }
            Hx::Pi(a, b) => {
                let _ = write!(self.out, "forall (x{depth} : ");
                self.term(a, depth, false);
                self.out.push_str("), ");
                self.term(b, depth + 1, false);
            }
            Hx::Lam(a, b) => {
                let _ = write!(self.out, "fun (x{depth} : ");
                self.term(a, depth, false);
                self.out.push_str(") => ");
                self.term(b, depth + 1, false);
            }
            Hx::App(..) => {
                let mut spine = Vec::new();
                let mut head = t;
                while let Hx::App(f, a) = head {
                    spine.push(a);
                    head = f;
                }
                match head {
                    Hx::Const(..) | Hx::Global(_) | Hx::Named(..) => self.atom(head),
                    _ => self.term(head, depth, true),
                }
                for a in spine.into_iter().rev() {
                    self.out.push(' ');
                    self.term(a, depth, true);
                }
            }
            Hx::Const(..) | Hx::Global(_) | Hx::Named(..) => self.atom(t),
            Hx::NatLit(n) => {
                let _ = write!(self.out, "({n} : Hx.Nat)");
            }
            Hx::Hole => self.out.push('_'),
        }
        if open {
            self.out.push(')');
        }
    }

    fn def(&mut self, name: &str, ty: &Hx, body: Option<&Hx>) {
        let kw = match (self.target, body) {
            (Target::Lean, Some(_)) => "@[reducible] def",
            (Target::Lean, None) => "axiom",
            (Target::Coq, Some(_)) => "Definition",
            (Target::Coq, None) => "Axiom",
        };
        let _ = write!(self.out, "{kw} {name} : ");
        self.term(ty, 0, false);
        if let Some(b) = body {
            self.out.push_str(" :=\n  ");
            self.term(b, 0, false);
        }
        self.out.push_str(match self.target {
            Target::Lean => "\n\n",
            Target::Coq => ".\n\n",
        });
    }

    /// A native inductive, its parameters as binders. Rocq has no
    /// realisation of `Wf` here (design §5.1), so it gets a comment.
    fn inductive(&mut self, name: &str, ty: &Hx, ind: &Inductive) {
        if self.target == Target::Coq {
            let _ = writeln!(self.out, "(* {name}: refused: Wf is realised for Lean only *)\n");
            return;
        }
        let strip = |mut t: &Hx, out: &mut Vec<Hx>| {
            for _ in 0..ind.nparams {
                let Hx::Pi(a, b) = t else { unreachable!("an inductive's parameters are binders") };
                out.push((**a).clone());
                t = b;
            }
            t.clone()
        };
        let mut params = Vec::new();
        let rest = strip(ty, &mut params);
        let _ = write!(self.out, "inductive {name}");
        for (i, a) in params.iter().enumerate() {
            let _ = write!(self.out, " (x{i} : ");
            self.term(a, i as u32, false);
            self.out.push(')');
        }
        self.out.push_str(" : ");
        self.term(&rest, ind.nparams as u32, false);
        self.out.push_str(" where\n");
        for (key, cty) in &ind.ctors {
            let short = key.rsplit("::").next().unwrap_or(key);
            let short = if plain_ident(short) && !LEAN_KEYWORDS.contains(&short) { short.to_string() } else { format!("«{short}»") };
            let _ = write!(self.out, "  | {short} : ");
            let c = strip(cty, &mut Vec::new());
            self.term(&c, ind.nparams as u32, false);
            self.out.push('\n');
        }
        self.out.push('\n');
    }

    /// A constant or global, explicit (`@`), with its levels.
    fn atom(&mut self, t: &Hx) {
        match t {
            Hx::Const(name, levels) => {
                let _ = write!(self.out, "@Hx.{name}");
                if !levels.is_empty() {
                    let ls: Vec<String> = levels.iter().map(|l| self.level(*l)).collect();
                    let _ = match self.target {
                        Target::Lean => write!(self.out, ".{{{}}}", ls.join(", ")),
                        Target::Coq => write!(self.out, "@{{{}}}", ls.join(" ")),
                    };
                }
            }
            Hx::Global(g) => {
                let _ = write!(self.out, "@{}", self.names[*g]);
            }
            Hx::Named(key, levels) => {
                let _ = write!(self.out, "@{}", target_name(self.target, key));
                if !levels.is_empty() {
                    let ls: Vec<String> = levels.iter().map(|l| l.to_string()).collect();
                    let _ = match self.target {
                        Target::Lean => write!(self.out, ".{{{}}}", ls.join(", ")),
                        Target::Coq => write!(self.out, "@{{{}}}", ls.join(" ")),
                    };
                }
            }
            _ => unreachable!("atom: a constant or a global"),
        }
    }
}

/// Print the exported declarations as a source file for `target`, which
/// imports the prelude. Refused declarations become comments naming why.
pub fn print(target: Target, decls: &[Exported]) -> String {
    let mut p = Printer { target, out: String::new(), names: spellings(target, decls) };
    p.out.push_str(match target {
        Target::Lean => "import Hx\n\nset_option autoImplicit false\nset_option linter.unusedVariables false\nnoncomputable section\n\n",
        Target::Coq => "Require Import Hx.\n\n",
    });
    for e in decls {
        let name = p.names[e.abs].clone();
        match &e.decl {
            Err(Refusal(why)) => {
                let _ = match target {
                    Target::Lean => writeln!(p.out, "-- {name}: refused: {why}\n"),
                    Target::Coq => writeln!(p.out, "(* {name}: refused: {why} *)\n"),
                };
            }
            Ok(d) => {
                for a in &d.before {
                    p.def(&target_name(target, &a.name), &a.ty, Some(&a.body));
                }
                match &d.inductive {
                    Some(ind) => p.inductive(&name, &d.ty, ind),
                    None => p.def(&name, &d.ty, d.body.as_ref()),
                }
                for a in &d.after {
                    p.def(&target_name(target, &a.name), &a.ty, Some(&a.body));
                }
            }
        }
    }
    p.out
}

/// Hash-consed nodes for [`print_kernel`]: one line per distinct subterm,
/// children named by their line number among the node lines.
struct Dag {
    out: String,
    ids: std::collections::HashMap<Hx, usize>,
    names: Vec<String>,
    /// Declarations the kernel route skipped, which their dependents skip.
    skipped: std::collections::HashSet<usize>,
}

impl Dag {
    fn node(&mut self, t: &Hx) -> Result<usize, String> {
        if let Some(&id) = self.ids.get(t) {
            return Ok(id);
        }
        let line = match t {
            Hx::Var(i) => format!("v\t{i}"),
            Hx::Sort(l) => format!("s\t{}", l.0),
            Hx::Pi(a, b) => format!("p\t{}\t{}", self.node(a)?, self.node(b)?),
            Hx::Lam(a, b) => format!("l\t{}\t{}", self.node(a)?, self.node(b)?),
            Hx::App(f, a) => format!("a\t{}\t{}", self.node(f)?, self.node(a)?),
            Hx::Const(name, levels) => {
                let mut s = format!("c\t{name}");
                for l in levels {
                    let _ = write!(s, "\t{}", l.0);
                }
                s
            }
            Hx::Global(g) if self.skipped.contains(g) => return Err(format!("mentions skipped {}", self.names[*g])),
            Hx::Global(g) => format!("g\t{}", self.names[*g]),
            Hx::Named(key, levels) => {
                let mut s = format!("g\t{key}");
                for l in levels {
                    let _ = write!(s, "\t{l}");
                }
                s
            }
            Hx::NatLit(n) => format!("n\t{n}"),
            Hx::Hole => return Err("a hole (a component only the target's elaborator can infer)".into()),
        };
        let id = self.ids.len();
        self.out.push_str(&line);
        self.out.push('\n');
        self.ids.insert(t.clone(), id);
        Ok(id)
    }
}

/// Print the exported declarations for Lean's **kernel**: the hash-consed
/// line format `prelude/Import.lean` reads and hands to `addDecl`, with no
/// parser and no elaborator in between (design §5.6). Names are Heather
/// keys (`nat::Nat::add`, or `g<abs>` where a binding has none or shares
/// one), which the importer roots at `Heather`. A declaration with a hole,
/// or one mentioning such a declaration, is written as skipped (`x`).
pub fn print_kernel(decls: &[Exported]) -> String {
    let mut seen = std::collections::HashSet::new();
    let len = decls.iter().map(|e| e.abs + 1).max().unwrap_or(0);
    let mut names = (0..len).map(|g| format!("g{g}")).collect::<Vec<_>>();
    for e in decls {
        if let Some(key) = &e.name {
            if seen.insert(key.clone()) {
                names[e.abs] = key.clone();
            }
        }
    }
    let mut dag = Dag { out: String::new(), ids: Default::default(), names, skipped: Default::default() };
    for e in decls {
        let name = dag.names[e.abs].clone();
        let line = match &e.decl {
            Err(Refusal(why)) => Err(format!("refused: {why}")),
            Ok(d) => (|| {
                let mut lines = Vec::new();
                let aux = |dag: &mut Dag, a: &Aux| -> Result<String, String> {
                    Ok(format!("d\t{}\t{}\t{}", a.name, dag.node(&a.ty)?, dag.node(&a.body)?))
                };
                for a in &d.before {
                    lines.push(aux(&mut dag, a)?);
                }
                let ty = dag.node(&d.ty)?;
                lines.push(match (&d.inductive, &d.body) {
                    (Some(ind), _) => {
                        let mut l = format!("i\t{name}\t{}\t{ty}", ind.nparams);
                        for (key, cty) in &ind.ctors {
                            let _ = write!(l, "\t{key}\t{}", dag.node(cty)?);
                        }
                        l
                    }
                    (None, Some(b)) => format!("d\t{name}\t{ty}\t{}", dag.node(b)?),
                    (None, None) => format!("ax\t{name}\t{ty}"),
                });
                for a in &d.after {
                    lines.push(aux(&mut dag, a)?);
                }
                Ok(lines.join("\n"))
            })(),
        };
        match line {
            Ok(line) => {
                dag.out.push_str(&line);
                dag.out.push('\n');
            }
            Err(why) => {
                dag.skipped.insert(e.abs);
                let _ = writeln!(dag.out, "x\t{name}\t{why}");
            }
        }
    }
    dag.out
}
