//! Budget-bounded, syntax-flavored `Debug` for the recursive kernel types.
//!
//! Substitution produces terms whose printed tree can be enormous (and, with
//! sharing, astronomically larger than the memory they occupy). A derived
//! `Debug` will happily build that entire string in RAM — which has OOM'd a
//! machine before it OOM'd a process. These impls make *any* `{:?}` safe:
//! a thread-local node budget is armed at the outermost format call, every
//! node consumes one unit, and an exhausted node prints `…` without
//! recursing, so output size and traversal work are both hard-bounded.
//!
//! The output is compact surface-ish syntax (`λ`, `Π`, `□`, `x0`, `u1^δ`),
//! not derive-style records — meant for reading terms while debugging the
//! kernel, not for round-tripping.

use std::cell::Cell;
use std::fmt;

use crate::level::Level;
use crate::term::{Branches, CtxBase, LocalCtx, LocalSubst, Motives, SubstTail, Term, Type};

/// Maximum nodes printed per outermost format call (bounds output size and
/// total work).
const NODE_BUDGET: isize = 512;

/// Maximum nesting depth printed (bounds stack: debug-build formatter frames
/// are several KB each, and test threads get a 2 MB stack).
const DEPTH_BUDGET: u32 = 64;

thread_local! {
    /// Remaining node budget; negative means "no format call in progress".
    static REMAINING: Cell<isize> = const { Cell::new(-1) };
    /// Current nesting depth within the outermost format call.
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Wrap one node's formatting: arms the budget at the outermost call,
/// consumes one unit per node, and prints `…` instead of recursing when
/// either the node budget or the depth budget is spent.
fn node(
    f: &mut fmt::Formatter<'_>,
    body: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    REMAINING.with(|r| {
        DEPTH.with(|d| {
            let outermost = r.get() < 0;
            if outermost {
                r.set(NODE_BUDGET);
                d.set(0);
            }
            let res = if r.get() == 0 || d.get() >= DEPTH_BUDGET {
                f.write_str("…")
            } else {
                r.set(r.get() - 1);
                d.set(d.get() + 1);
                let res = body(f);
                d.set(d.get() - 1);
                res
            };
            if outermost {
                r.set(-1);
            }
            res
        })
    })
}

impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            // Collapse `1 + (1 + …)` prefixes into a numeral.
            let mut n = 0u64;
            let mut cur = self;
            while let Level::Succ(inner) = cur {
                n += 1;
                cur = inner;
            }
            if n > 0 && !matches!(cur, Level::Zero) {
                write!(f, "{n}+")?;
            }
            match cur {
                Level::Zero => write!(f, "{n}"),
                Level::Var(v) => write!(f, "ℓ{}", v.0),
                Level::Max(a, b) => write!(f, "({a:?} ⊔ {b:?})"),
                Level::Omega => f.write_str("ω"),
                Level::Succ(_) => unreachable!(),
            }
        })
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Type::Nat => f.write_str("Nat"),
            Type::Pi { dom_level, cod_level, dom, cod } => {
                write!(f, "Π[{dom_level:?},{cod_level:?}]({dom:?}). {cod:?}")
            }
            Type::Ty(l) => write!(f, "Ty {l:?}"),
            Type::UPi { num_vars, level, body } => {
                write!(f, "ΠΠ[{num_vars}ℓ@{level:?}]. {body:?}")
            }
            Type::El { level, tm } => write!(f, "El[{level:?}]({tm:?})"),
            Type::Id { level, ty, lhs, rhs } => {
                write!(f, "Id[{level:?}]({ty:?}; {lhs:?}; {rhs:?})")
            }
            Type::GlobalTy { var, subst } => write!(f, "U{}^{subst:?}", var.0),
            Type::CtxPi { level, body } => write!(f, "Π[g:Ctx@{level:?}]. {body:?}"),
            Type::TyPi { ctx, arg_level, body_level, body } => {
                write!(f, "Π[U:Typ({ctx:?},{arg_level:?})@{body_level:?}]. {body:?}")
            }
            Type::CodeTy { ctx, level } => write!(f, "□({ctx:?} ⊢ Ty {level:?})"),
            Type::CodeTm { ctx, ty, level } => {
                write!(f, "□({ctx:?} ⊢ {ty:?} @ {level:?})")
            }
        })
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Term::Var(v) => write!(f, "x{}", v.0),
            Term::TmNat => f.write_str("«Nat»"),
            Term::TmPi { dom_level, cod_level, dom, cod } => {
                write!(f, "«Π[{dom_level:?},{cod_level:?}]({dom:?}). {cod:?}»")
            }
            Term::TmTy(l) => write!(f, "«Ty {l:?}»"),
            Term::TmId { level, ty, lhs, rhs } => {
                write!(f, "«Id[{level:?}]({ty:?}; {lhs:?}; {rhs:?})»")
            }
            Term::Zero => f.write_str("0"),
            Term::Succ(t) => write!(f, "S({t:?})"),
            Term::ElimNat { level, motive, base, step, scrut } => write!(
                f,
                "elimN[{level:?}](M {motive:?}; z {base:?}; s {step:?}; {scrut:?})"
            ),
            Term::Refl { level, ty, tm } => write!(f, "refl[{level:?}]({ty:?}; {tm:?})"),
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => write!(
                f,
                "J[{ty_level:?},{motive_level:?}]({ty:?}; a {lhs:?}; M {motive:?}; c {case:?}; {rhs:?}; {proof:?})"
            ),
            Term::Lam { dom_level, cod_level, dom, body } => {
                write!(f, "λ[{dom_level:?},{cod_level:?}]({dom:?}). {body:?}")
            }
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => write!(
                f,
                "app({fun:?}; [{dom_level:?},{cod_level:?}] {dom:?} → {cod:?}; {arg:?})"
            ),
            Term::ULam { num_vars, level, body } => {
                write!(f, "Λ[{num_vars}ℓ@{level:?}]. {body:?}")
            }
            Term::UApp { fun, levels } => {
                write!(f, "({fun:?} $")?;
                for l in levels {
                    write!(f, " {l:?}")?;
                }
                f.write_str(")")
            }
            Term::GlobalTm { var, subst } => write!(f, "u{}^{subst:?}", var.0),
            Term::CtxLam { level, body } => write!(f, "Λ[g:Ctx@{level:?}]. {body:?}"),
            Term::CtxApp { fun, ctx } => write!(f, "capp({fun:?}, {ctx:?})"),
            Term::TyLam { ctx, arg_level, body_level, body } => {
                write!(f, "Λ[U:Typ({ctx:?},{arg_level:?})@{body_level:?}]. {body:?}")
            }
            Term::TyApp { fun, arg } => write!(f, "tapp({fun:?}, {arg:?})"),
            Term::BoxTy(t) => write!(f, "box({t:?})"),
            Term::BoxTm(t) => write!(f, "box({t:?})"),
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => write!(
                f,
                "letboxT[{motive_level:?},{code_level:?}]({ctx:?}; M {motive:?}; U. {body:?}; {scrut:?})"
            ),
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => write!(
                f,
                "letboxt[{motive_level:?},{code_level:?}]({ctx:?} ⊢ {ty:?}; M {motive:?}; u. {body:?}; {scrut:?})"
            ),
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                scrut,
            } => write!(
                f,
                "elimTy[{ty_motive_level:?},{tm_motive_level:?}]({motives:?}; {branches:?}; @{code_level:?} {ctx:?}; {scrut:?})"
            ),
            Term::ElimCodeTm {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                ty,
                scrut,
            } => write!(
                f,
                "elimTm[{ty_motive_level:?},{tm_motive_level:?}]({motives:?}; {branches:?}; @{code_level:?} {ctx:?} ⊢ {ty:?}; {scrut:?})"
            ),
        })
    }
}

impl fmt::Debug for LocalCtx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            f.write_str("(")?;
            match self.base {
                CtxBase::Nil => f.write_str("·")?,
                CtxBase::Var(g) => write!(f, "g{}", g.0)?,
            }
            for e in &self.entries {
                write!(f, ", {:?}@{:?}", e.ty, e.level)?;
            }
            f.write_str(")")
        })
    }
}

impl fmt::Debug for LocalSubst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            f.write_str("{")?;
            match self.tail {
                SubstTail::Empty { len, base: CtxBase::Nil } => write!(f, "·^{len}")?,
                SubstTail::Empty { len, base: CtxBase::Var(g) } => {
                    write!(f, "·^{len}_g{}", g.0)?
                }
                SubstTail::Wk { len, ctx_var } => write!(f, "wk^{len}_g{}", ctx_var.0)?,
            }
            for t in &self.terms {
                write!(f, "; {t:?}")?;
            }
            f.write_str("}")
        })
    }
}

impl fmt::Debug for Motives {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            write!(f, "M⃗(Typ {:?}; Trm {:?})", self.ty_motive, self.tm_motive)
        })
    }
}

impl fmt::Debug for Branches {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            write!(
                f,
                "b⃗(Nat {:?}; Π {:?}; Ty {:?}; El {:?}; Id {:?} | x {:?}; «Nat» {:?}; «Π» {:?}; «Ty» {:?}; 0 {:?}; S {:?}; elimN {:?}; λ {:?}; app {:?}; «Id» {:?}; refl {:?}; J {:?})",
                self.ty_nat,
                self.ty_pi,
                self.ty_ty,
                self.ty_el,
                self.ty_id,
                self.tm_var,
                self.tm_nat,
                self.tm_pi,
                self.tm_ty,
                self.tm_zero,
                self.tm_succ,
                self.tm_elim_nat,
                self.tm_lam,
                self.tm_app,
                self.tm_id,
                self.tm_refl,
                self.tm_j,
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::level::Level;
    use crate::term::{Term, Type};

    /// A DAG whose tree-expansion is 2^64 nodes: formatting must stay
    /// bounded in both output size and time.
    #[test]
    fn debug_of_exponential_dag_is_bounded() {
        let mut t = Rc::new(Term::Zero);
        for _ in 0..64 {
            t = Rc::new(Term::App {
                fun: Rc::clone(&t),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Nat),
                arg: Rc::clone(&t),
            });
        }
        let s = format!("{t:?}");
        assert!(s.len() < 128 * 1024, "unbounded debug output: {} bytes", s.len());
        assert!(s.contains('…'), "expected elision marker in bounded output");
    }

    /// The budget re-arms per outermost call: repeated formats of the same
    /// value agree (no leakage of a half-spent budget).
    #[test]
    fn budget_rearms_between_calls() {
        let mut t = Rc::new(Term::Zero);
        for _ in 0..2000 {
            t = Rc::new(Term::Succ(t));
        }
        let a = format!("{t:?}");
        let b = format!("{t:?}");
        assert_eq!(a, b);
        assert!(a.contains('…'));
    }

    #[test]
    fn small_terms_print_fully_and_readably() {
        let id = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Var(crate::term::LocalVar(0))),
        };
        assert_eq!(format!("{id:?}"), "λ[0,0](Nat). x0");
    }
}
