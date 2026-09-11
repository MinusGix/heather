//! The emission walker (`docs/annotation-component-respell-design.md` §2.5,
//! `issues/emission-spelling-chokepoint.md`).
//!
//! One pass over a checked declaration's statement and term that asks, at
//! every **emitted** annotation slot, whether [`Elaborator::emit_ty`] would
//! still change what is written there. A `Some` is a site that spells a type
//! its siblings spell differently — the failure every row of
//! `issues/emission-site-respell-audit.md` turned out to be — and the walker
//! is what finds the next one before a conversion sampler has to attribute
//! it.
//!
//! Scope is deliberately **exactly the chokepoint's**, so that "the walker
//! would change this" and "routing this site through `emit_ty` changes this"
//! are the same statement:
//!
//! - a slot is checked whole and never descended into: `emit_ty` is already
//!   component-wise, so a slot it declines has no component left to report;
//! - terms inside types are not walked (`Id` endpoints, `Vec` lengths, `El`
//!   codes), matching `respell_ty_deep`'s own walk;
//! - code payloads are not walked (`BoxTy`/`BoxTm` contents, a `CodeTm`'s
//!   type, the code recursors' motives and branches): the quote is syntax and
//!   the reflection boundary owns it (§6.4).
//!
//! The traversal is exhaustive with no `_` arm, borrowing `fmt.rs`'s shape:
//! a new kernel variant fails to compile here, which is the point — a new
//! annotation slot cannot be added without an answer about its spelling.
//! Binder depths are the ones each variant's doc comment in
//! `crates/kernel/src/term.rs` states.

use heather_kernel::term::{Motives, Term, Type};

use crate::{Cx, Elaborator};

/// One emitted slot whose content [`Elaborator::emit_ty`] would rewrite.
#[derive(Clone, Debug)]
pub struct EmissionFinding {
    /// The declaration the slot was found in.
    pub decl: String,
    /// The variant and field, e.g. `"Refl.ty"`, `"Pair.snd_ty"`, `"App.dom"`.
    pub slot: &'static str,
    /// Binders the slot sits under, past the declaration's (empty) context.
    pub depth: u32,
    /// The slot as written, through the kernel's node-budgeted `Debug`.
    pub found: String,
    /// What the chokepoint would write instead, same budget.
    pub emitted: String,
}

/// Walk one checked declaration. `stmt` and `term` are the pair the kernel is
/// handed, after `apply_global`.
pub(crate) fn walk_decl(
    el: &Elaborator,
    decl: &str,
    stmt: &Type,
    term: Option<&Term>,
) -> Vec<EmissionFinding> {
    let mut w = Walk {
        el,
        cx: Cx::empty(),
        decl,
        out: Vec::new(),
    };
    // The statement is emitted component-wise by `elab_decl_inner`'s closing
    // loop, and `emit_ty` on the whole `Π` visits binder `i` at depth `i` and
    // the result at depth `n` — the cascade's own fixpoint, in one call.
    w.slot("stmt", stmt, 0);
    if let Some(term) = term {
        w.term(term, 0);
    }
    w.out
}

struct Walk<'a> {
    el: &'a Elaborator,
    cx: Cx,
    decl: &'a str,
    out: Vec<EmissionFinding>,
}

impl Walk<'_> {
    /// One emitted annotation slot, at `d` binders past the empty context.
    fn slot(&mut self, name: &'static str, ty: &Type, d: u32) {
        if let Some(emitted) = self.el.emit_ty(&self.cx, ty, d) {
            self.out.push(EmissionFinding {
                decl: self.decl.to_string(),
                slot: name,
                depth: d,
                found: format!("{ty:?}"),
                emitted: format!("{emitted:?}"),
            });
        }
    }

    /// The `Wf` slot **pair**: `respell_ty_deep`'s `Wf` arm respells shape and
    /// arity together or neither, so the two are checked as the former they
    /// reconstitute — exactly as `build_ctor` writes them.
    fn wf_slots(
        &mut self,
        name: &'static str,
        level: &heather_kernel::level::Level,
        shape: &std::sync::Arc<Type>,
        arity: &std::sync::Arc<Term>,
        d: u32,
    ) {
        // The question a slot asks is the *component* respell
        // (`Elaborator::emit_wf_slots`), not `emit_ty` of the former the two
        // reconstitute: since
        // `docs/per-instantiation-type-codes-design.md` a monomorphized `Wf`
        // has a name for the whole, and that name may not stand in a slot
        // that holds the component (§8).
        let _ = level;
        if let Some((s, a)) = self.el.emit_wf_slots(&self.cx, shape, arity, d) {
            self.out.push(EmissionFinding {
                decl: self.decl.to_string(),
                slot: name,
                depth: d,
                found: format!("{shape:?} / {arity:?}"),
                emitted: format!("{s:?} / {a:?}"),
            });
        }
    }

    fn terms(&mut self, ts: &[std::sync::Arc<Term>], d: u32) {
        for t in ts {
            self.term(t, d);
        }
    }

    fn term(&mut self, t: &Term, d: u32) {
        match t {
            Term::Var(_) | Term::TmNat | Term::TmTy(_) | Term::Zero | Term::NatLit(_) => {}
            Term::Succ(t) => self.term(t, d),

            // -- encodings of types. No `Type` slot lives inside a code, but
            // the walk stays exhaustive so a future one cannot be missed.
            Term::TmPi { dom, cod, .. } => {
                self.term(dom, d);
                self.term(cod, d + 1);
            }
            Term::TmId { ty, lhs, rhs, .. } | Term::TmSEq { ty, lhs, rhs, .. } => {
                self.term(ty, d);
                self.term(lhs, d);
                self.term(rhs, d);
            }
            Term::TmSEmpty { .. } | Term::TmUnit { .. } | Term::TmEmpty { .. } => {}
            Term::TmSquash { ty, .. } => self.term(ty, d),
            Term::TmSigma { fst, snd, .. } => {
                self.term(fst, d);
                self.term(snd, d + 1);
            }
            Term::TmSum { lhs, rhs, .. } => {
                self.term(lhs, d);
                self.term(rhs, d);
            }
            Term::TmW { shape, pos, .. } => {
                self.term(shape, d);
                self.term(pos, d + 1);
            }
            Term::TmVec { elem, len, .. } => {
                self.term(elem, d);
                self.term(len, d);
            }
            Term::TmFin { len } => self.term(len, d),
            Term::TmWf { shape, arity, .. } => {
                self.term(shape, d);
                self.term(arity, d + 1);
            }

            Term::ElimNat {
                motive,
                base,
                step,
                scrut,
                ..
            } => {
                self.slot("ElimNat.motive", motive, d + 1);
                self.term(base, d);
                self.term(step, d + 2);
                self.term(scrut, d);
            }

            Term::Refl { ty, tm, .. } => {
                self.slot("Refl.ty", ty, d);
                self.term(tm, d);
            }
            Term::J {
                ty,
                lhs,
                motive,
                case,
                rhs,
                proof,
                ..
            } => {
                self.slot("J.ty", ty, d);
                self.slot("J.motive", motive, d + 2);
                self.term(lhs, d);
                self.term(case, d);
                self.term(rhs, d);
                self.term(proof, d);
            }
            Term::SRefl { ty, tm, .. } => {
                self.slot("SRefl.ty", ty, d);
                self.term(tm, d);
            }
            Term::Squash { ty, tm, .. } => {
                self.slot("Squash.ty", ty, d);
                self.term(tm, d);
            }
            Term::Transp {
                ty,
                motive,
                lhs,
                rhs,
                proof,
                tm,
                ..
            } => {
                self.slot("Transp.ty", ty, d);
                self.slot("Transp.motive", motive, d + 1);
                self.term(lhs, d);
                self.term(rhs, d);
                self.term(proof, d);
                self.term(tm, d);
            }
            Term::ElimSEmpty { motive, scrut, .. } => {
                self.slot("ElimSEmpty.motive", motive, d + 1);
                self.term(scrut, d);
            }
            Term::ElimSquash {
                src_ty,
                motive,
                case,
                scrut,
                ..
            } => {
                self.slot("ElimSquash.src_ty", src_ty, d);
                self.slot("ElimSquash.motive", motive, d + 1);
                self.term(case, d + 1);
                self.term(scrut, d);
            }

            Term::Pair {
                fst_ty,
                snd_ty,
                fst,
                snd,
                ..
            } => {
                self.slot("Pair.fst_ty", fst_ty, d);
                self.slot("Pair.snd_ty", snd_ty, d + 1);
                self.term(fst, d);
                self.term(snd, d);
            }
            Term::Fst {
                fst_ty,
                snd_ty,
                pair,
                ..
            } => {
                self.slot("Fst.fst_ty", fst_ty, d);
                self.slot("Fst.snd_ty", snd_ty, d + 1);
                self.term(pair, d);
            }
            Term::Snd {
                fst_ty,
                snd_ty,
                pair,
                ..
            } => {
                self.slot("Snd.fst_ty", fst_ty, d);
                self.slot("Snd.snd_ty", snd_ty, d + 1);
                self.term(pair, d);
            }

            Term::Triv { .. } => {}
            Term::ElimEmpty { motive, scrut, .. } => {
                self.slot("ElimEmpty.motive", motive, d + 1);
                self.term(scrut, d);
            }

            Term::Inl { lhs, rhs, val, .. } => {
                self.slot("Inl.lhs", lhs, d);
                self.slot("Inl.rhs", rhs, d);
                self.term(val, d);
            }
            Term::Inr { lhs, rhs, val, .. } => {
                self.slot("Inr.lhs", lhs, d);
                self.slot("Inr.rhs", rhs, d);
                self.term(val, d);
            }
            Term::Case {
                lhs,
                rhs,
                motive,
                case_l,
                case_r,
                scrut,
                ..
            } => {
                self.slot("Case.lhs", lhs, d);
                self.slot("Case.rhs", rhs, d);
                self.slot("Case.motive", motive, d + 1);
                self.term(case_l, d + 1);
                self.term(case_r, d + 1);
                self.term(scrut, d);
            }

            Term::Sup {
                shape_ty,
                pos_ty,
                label,
                children,
                ..
            } => {
                self.slot("Sup.shape_ty", shape_ty, d);
                self.slot("Sup.pos_ty", pos_ty, d + 1);
                self.term(label, d);
                self.term(children, d);
            }
            Term::ElimW {
                shape,
                pos,
                motive,
                step,
                scrut,
                ..
            } => {
                self.slot("ElimW.shape", shape, d);
                self.slot("ElimW.pos", pos, d + 1);
                self.slot("ElimW.motive", motive, d + 1);
                self.term(step, d + 3);
                self.term(scrut, d);
            }

            Term::Supf {
                level,
                shape,
                arity,
                label,
                children,
            } => {
                self.wf_slots("Supf.shape/arity", level, shape, arity, d);
                self.term(label, d);
                self.term(children, d);
            }
            Term::ElimWf {
                level,
                shape,
                arity,
                motive,
                step,
                scrut,
                ..
            } => {
                self.wf_slots("ElimWf.shape/arity", level, shape, arity, d);
                self.slot("ElimWf.motive", motive, d + 1);
                self.term(step, d + 3);
                self.term(scrut, d);
            }

            Term::Lam { dom, body, .. } => {
                self.slot("Lam.dom", dom, d);
                self.term(body, d + 1);
            }
            Term::App {
                fun,
                dom,
                cod,
                arg,
                ..
            } => {
                self.slot("App.dom", dom, d);
                self.slot("App.cod", cod, d + 1);
                self.term(fun, d);
                self.term(arg, d);
            }

            // Universe binders extend L, never Γ.
            Term::ULam { body, .. } => self.term(body, d),
            Term::UApp { fun, .. } => self.term(fun, d),

            // A global's substitution carries ordinary terms of this scope.
            Term::GlobalTm { subst, .. } => self.terms(&subst.terms, d),

            // Meta binders extend Ψ, never Γ, so the local depth is unchanged.
            Term::CtxLam { body, .. } => self.term(body, d),
            Term::CtxApp { fun, .. } => self.term(fun, d),
            Term::TyLam { body, .. } => self.term(body, d),
            Term::TyApp { fun, arg } => {
                self.slot("TyApp.arg", arg, d);
                self.term(fun, d);
            }

            // Code payloads: the quote is syntax scoped to its own `Δ`, and
            // the reflection boundary owns its spelling (§6.4).
            Term::BoxTy(_) | Term::BoxTm(_) => {}

            Term::LetBoxTy {
                motive,
                body,
                scrut,
                ..
            } => {
                self.slot("LetBoxTy.motive", motive, d + 1);
                self.term(body, d);
                self.term(scrut, d);
            }
            // `ty` is the contextual type's payload, scoped to `Δ` rather than
            // to Γ — a code payload, not an annotation of this scope.
            Term::LetBoxTm {
                motive,
                body,
                scrut,
                ..
            } => {
                self.slot("LetBoxTm.motive", motive, d + 1);
                self.term(body, d);
                self.term(scrut, d);
            }

            // The code recursors' motives and branches live under the ch. 04
            // branch telescopes (universe, global and local binders per
            // branch), and every type in them is a code payload's. Nothing in
            // the elaborator writes a registry-known lowering into one; the
            // scrutinee is an ordinary term of this scope.
            Term::ElimCodeTy { motives, scrut, .. } => {
                let _: &Motives = motives;
                self.term(scrut, d);
            }
            Term::ElimCodeTm { motives, scrut, .. } => {
                let _: &Motives = motives;
                self.term(scrut, d);
            }
        }
    }
}
