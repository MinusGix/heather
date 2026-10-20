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

use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, GlobalBinding, GlobalCtx, LocalSubst, SubstTail, Term, Type};
use std::fmt::Write as _;

/// A universe level of the exported fragment: closed, because the library is
/// universe-monomorphic (`UPi` is layer m, which declarations never use).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lvl(pub u64);

/// The intermediate language: de Bruijn terms over prelude constants.
#[derive(Clone, Debug, PartialEq, Eq)]
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
    NatLit(String),
    /// A component the kernel term does not spell (a checked spelling's
    /// erased annotation); the target elaborator recovers it.
    Hole,
}

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
struct Tr {
    at: usize,
}

impl Tr {
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
            Type::Pi { dom, cod, .. } => Hx::Pi(Box::new(self.ty(dom)?), Box::new(self.ty(cod)?)),
            Type::Ty(l) => Hx::Sort(lvl(l)?),
            Type::El { tm, .. } => self.tm(tm)?,
            Type::Id { level, ty, lhs, rhs } => konst("Id", &[level], vec![self.ty(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Type::SEq { level, ty, lhs, rhs } => konst("SEq", &[level], vec![self.ty(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Type::SEmpty { level } => konst("SEmpty", &[level], vec![])?,
            Type::Squash { level, ty } => konst("Squash", &[level], vec![self.ty(ty)?])?,
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                konst("Sig", &[fst_level, snd_level], vec![self.ty(fst)?, lam(self.ty(fst)?, self.ty(snd)?)])?
            }
            Type::Unit { level } => konst("Unit", &[level], vec![])?,
            Type::Empty { level } => konst("Empty", &[level], vec![])?,
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                konst("Sum", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?])?
            }
            Type::W { shape_level, pos_level, shape, pos } => {
                konst("W", &[shape_level, pos_level], vec![self.ty(shape)?, lam(self.ty(shape)?, self.ty(pos)?)])?
            }
            Type::Vec { level, elem, len } => konst("Vec", &[level], vec![self.ty(elem)?, self.tm(len)?])?,
            Type::Fin { len } => konst("Fin", &[], vec![self.tm(len)?])?,
            Type::Wf { level, shape, arity } => {
                konst("Wf", &[level], vec![self.ty(shape)?, lam(self.ty(shape)?, self.tm(arity)?)])?
            }
            Type::DVec { .. } | Type::IWf { .. } => return refuse("DVec/IWf (no code yet; not in declarations)"),
            Type::UPi { .. } => return refuse("ΠΠ (universe polymorphism)"),
            Type::GlobalTy { .. } => return refuse("global type variable (layer c/p meta binding)"),
            Type::CtxPi { .. } | Type::TyPi { .. } => return refuse("context/type meta-function"),
            Type::CodeTy { .. } | Type::CodeTm { .. } => return refuse("contextual (boxed) type"),
        })
    }

    fn tm(&self, t: &Term) -> R<Hx> {
        Ok(match t {
            Term::Var(v) => Hx::Var(v.0),
            // ---- codes decode to themselves (Tarski → Russell) ----
            Term::TmNat => Hx::Const("Nat", vec![]),
            Term::TmPi { dom, cod, .. } => Hx::Pi(Box::new(self.tm(dom)?), Box::new(self.tm(cod)?)),
            Term::TmTy(l) => Hx::Sort(lvl(l)?),
            Term::TmId { level, ty, lhs, rhs } => konst("Id", &[level], vec![self.tm(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Term::TmSEq { level, ty, lhs, rhs } => konst("SEq", &[level], vec![self.tm(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Term::TmSEmpty { level } => konst("SEmpty", &[level], vec![])?,
            Term::TmSquash { level, ty } => konst("Squash", &[level], vec![self.tm(ty)?])?,
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                konst("Sig", &[fst_level, snd_level], vec![self.tm(fst)?, lam(self.tm(fst)?, self.tm(snd)?)])?
            }
            Term::TmUnit { level } => konst("Unit", &[level], vec![])?,
            Term::TmEmpty { level } => konst("Empty", &[level], vec![])?,
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                konst("Sum", &[lhs_level, rhs_level], vec![self.tm(lhs)?, self.tm(rhs)?])?
            }
            Term::TmW { shape_level, pos_level, shape, pos } => {
                konst("W", &[shape_level, pos_level], vec![self.tm(shape)?, lam(self.tm(shape)?, self.tm(pos)?)])?
            }
            Term::TmVec { level, elem, len } => konst("Vec", &[level], vec![self.tm(elem)?, self.tm(len)?])?,
            Term::TmFin { len } => konst("Fin", &[], vec![self.tm(len)?])?,
            Term::TmWf { level, shape, arity } => {
                konst("Wf", &[level], vec![self.tm(shape)?, lam(self.tm(shape)?, self.tm(arity)?)])?
            }
            // ---- Nat ----
            Term::Zero => Hx::NatLit("0".into()),
            Term::NatLit(n) => Hx::NatLit(n.to_string()),
            Term::Succ(n) => konst("succ", &[], vec![self.tm(n)?])?,
            Term::ElimNat { level, motive, base, step, scrut } => konst(
                "elimNat",
                &[level],
                vec![bind(self.ty(motive)?), self.tm(base)?, bind(bind(self.tm(step)?)), self.tm(scrut)?],
            )?,
            // ---- Id ----
            Term::Refl { level, ty, tm } => konst("refl", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => konst(
                "J",
                &[ty_level, motive_level],
                vec![
                    self.ty(ty)?,
                    self.tm(lhs)?,
                    bind(bind(self.ty(motive)?)),
                    self.tm(case)?,
                    self.tm(rhs)?,
                    self.tm(proof)?,
                ],
            )?,
            // ---- strict equality and squash ----
            Term::SRefl { level, ty, tm } => konst("srefl", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => konst(
                "transp",
                &[ty_level, motive_level],
                vec![self.ty(ty)?, bind(self.ty(motive)?), self.tm(lhs)?, self.tm(rhs)?, self.tm(proof)?, self.tm(tm)?],
            )?,
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                konst("elimSEmpty", &[level, scrut_level], vec![bind(self.ty(motive)?), self.tm(scrut)?])?
            }
            Term::Squash { level, ty, tm } => konst("squash", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => konst(
                "elimSquash",
                &[src_level, dst_level],
                vec![self.ty(src_ty)?, bind(self.ty(motive)?), bind(self.tm(case)?), self.tm(scrut)?],
            )?,
            // ---- Σ ----
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => konst(
                "pair",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, lam(self.ty(fst_ty)?, self.ty(snd_ty)?), self.tm(fst)?, self.tm(snd)?],
            )?,
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => konst(
                "fst",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, lam(self.ty(fst_ty)?, self.ty(snd_ty)?), self.tm(pair)?],
            )?,
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => konst(
                "snd",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, lam(self.ty(fst_ty)?, self.ty(snd_ty)?), self.tm(pair)?],
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
                konst("elimEmpty", &[level, scrut_level], vec![bind(self.ty(motive)?), self.tm(scrut)?])?
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
                    bind(self.ty(motive)?),
                    bind(self.tm(case_l)?),
                    bind(self.tm(case_r)?),
                    self.tm(scrut)?,
                ],
            )?,
            // ---- W and Wf ----
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => konst(
                "sup",
                &[shape_level, pos_level],
                vec![self.ty(shape_ty)?, lam(self.ty(shape_ty)?, self.ty(pos_ty)?), self.tm(label)?, self.tm(children)?],
            )?,
            Term::ElimW { shape_level, pos_level, motive_level, shape, pos, motive, step, scrut } => konst(
                "elimW",
                &[shape_level, pos_level, motive_level],
                vec![
                    self.ty(shape)?,
                    lam(self.ty(shape)?, self.ty(pos)?),
                    bind(self.ty(motive)?),
                    bind(bind(bind(self.tm(step)?))),
                    self.tm(scrut)?,
                ],
            )?,
            Term::Supf { level, shape, arity, label, children } => konst(
                "supf",
                &[level],
                vec![self.ty(shape)?, lam(self.ty(shape)?, self.tm(arity)?), self.tm(label)?, self.tm(children)?],
            )?,
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => konst(
                "elimWf",
                &[level, motive_level],
                vec![
                    self.ty(shape)?,
                    lam(self.ty(shape)?, self.tm(arity)?),
                    bind(self.ty(motive)?),
                    bind(bind(bind(self.tm(step)?))),
                    self.tm(scrut)?,
                ],
            )?,
            Term::Supi { .. } | Term::ElimIWf { .. } => return refuse("IWf (no code yet; not in declarations)"),
            // ---- functions ----
            Term::Lam { dom, body, .. } => lam(self.ty(dom)?, self.tm(body)?),
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
    pub ty: Hx,
    /// The definition's body, or the proof of a theorem; `None` for an
    /// assumption (an axiom, or a theorem whose proof Ψ did not keep).
    pub body: Option<Hx>,
}

/// Translate every binding of Ψ from absolute index `from`. A binding is
/// refused when it is outside the fragment *or mentions a refused binding*,
/// so the `Ok` declarations are closed under dependency.
pub fn export(psi: &GlobalCtx) -> Vec<(usize, R<Decl>)> {
    let mut out: Vec<(usize, R<Decl>)> = Vec::new();
    let mut refused = vec![false; psi.bindings.len()];
    for (abs, b) in psi.bindings.iter().enumerate() {
        let tr = Tr { at: abs };
        let decl = (|| -> R<Decl> {
            let GlobalBinding::Tm { ctx, ty, body, .. } = b else {
                return refuse("context or type global binding");
            };
            if ctx.len() != 0 {
                return refuse("global over a non-empty local context Δ");
            }
            let proof = body.clone().or_else(|| psi.sealed_proof(abs).cloned());
            let d = Decl {
                abs,
                ty: tr.ty(ty)?,
                body: proof.map(|t| tr.tm(&t)).transpose()?,
            };
            if let Some(dep) = mentions(&d).into_iter().find(|&g| refused[g]) {
                return Err(Refusal(format!("mentions refused declaration g{dep}")));
            }
            Ok(d)
        })();
        refused[abs] = decl.is_err();
        out.push((abs, decl));
    }
    out
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

    fn term(&mut self, t: &Hx, depth: u32) {
        match t {
            Hx::Var(i) => {
                let _ = write!(self.out, "x{}", depth - 1 - i);
            }
            Hx::Sort(l) => {
                let s = match self.target {
                    Target::Lean => format!("Type {}", self.level(*l)),
                    Target::Coq => format!("Type@{{{}}}", self.level(*l)),
                };
                let _ = write!(self.out, "({s})");
            }
            Hx::Pi(a, b) => {
                let _ = write!(self.out, "(forall (x{depth} : ");
                self.term(a, depth);
                self.out.push_str("), ");
                self.term(b, depth + 1);
                self.out.push(')');
            }
            Hx::Lam(a, b) => {
                let _ = write!(self.out, "(fun (x{depth} : ");
                self.term(a, depth);
                self.out.push_str(") => ");
                self.term(b, depth + 1);
                self.out.push(')');
            }
            Hx::App(..) => {
                let mut spine = Vec::new();
                let mut head = t;
                while let Hx::App(f, a) = head {
                    spine.push(a);
                    head = f;
                }
                self.out.push('(');
                self.term(head, depth);
                for a in spine.into_iter().rev() {
                    self.out.push(' ');
                    self.term(a, depth);
                }
                self.out.push(')');
            }
            // Parenthesised: Rocq parses `f @c` as a syntax error.
            Hx::Const(name, levels) => {
                let _ = write!(self.out, "(@Hx.{name}");
                if !levels.is_empty() {
                    let ls: Vec<String> = levels.iter().map(|l| self.level(*l)).collect();
                    let _ = match self.target {
                        Target::Lean => write!(self.out, ".{{{}}}", ls.join(", ")),
                        Target::Coq => write!(self.out, "@{{{}}}", ls.join(" ")),
                    };
                }
                self.out.push(')');
            }
            Hx::Global(g) => {
                let _ = write!(self.out, "(@g{g})");
            }
            Hx::NatLit(n) => {
                let _ = write!(self.out, "({n} : Hx.Nat)");
            }
            Hx::Hole => self.out.push('_'),
        }
    }
}

/// Print the exported declarations as a source file for `target`, which
/// imports the prelude. Refused declarations become comments naming why.
pub fn print(target: Target, decls: &[(usize, R<Decl>)]) -> String {
    let mut p = Printer { target, out: String::new() };
    p.out.push_str(match target {
        Target::Lean => "import Hx\n\nset_option autoImplicit false\nset_option linter.unusedVariables false\nnoncomputable section\n\n",
        Target::Coq => "Require Import Hx.\n\n",
    });
    for (abs, d) in decls {
        match d {
            Err(Refusal(why)) => {
                let _ = match target {
                    Target::Lean => writeln!(p.out, "-- g{abs}: refused: {why}\n"),
                    Target::Coq => writeln!(p.out, "(* g{abs}: refused: {why} *)\n"),
                };
            }
            Ok(d) => {
                let kw = match (target, &d.body) {
                    (Target::Lean, Some(_)) => "@[reducible] def",
                    (Target::Lean, None) => "axiom",
                    (Target::Coq, Some(_)) => "Definition",
                    (Target::Coq, None) => "Axiom",
                };
                let _ = write!(p.out, "{kw} g{abs} : ");
                p.term(&d.ty, 0);
                if let Some(b) = &d.body {
                    p.out.push_str(" :=\n  ");
                    p.term(b, 0);
                }
                p.out.push_str(match target {
                    Target::Lean => "\n\n",
                    Target::Coq => ".\n\n",
                });
            }
        }
    }
    p.out
}
