//! Induction-hypothesis generalization (issues/ih-generalization.md,
//! docs/ih-generalization-design.md).
//!
//! A structurally recursive `match` whose self-calls pass some *non-decreasing*
//! parameter at something other than the parameter itself needs a motive that
//! quantifies that parameter: `M(z) = Π(m : B). T[z]`. This module computes
//! that motive from the checking goal, wraps the arms in the matching lambdas
//! (under the parameters' own names, so an arm body reads exactly as written),
//! and applies the finished recursor back to the parameters. A self-call in an
//! arm then applies the induction hypothesis to the varied arguments
//! (`recursion::elab_self_call`).
//!
//! Two invariants carry over from the rest of the recursion machinery:
//!
//! - **The scan is a sizing decision only.** [`Elaborator::varying_params`]
//!   works on names, so shadowing can mislead it in either direction — and
//!   neither direction produces a wrong term. A missed parameter meets the
//!   by-binder refusal that stood before this existed; a parameter generalized
//!   needlessly costs a Π nothing reads. What a call lowers to is decided by
//!   comparing binder positions and by the ordinary application engine
//!   checking each varied argument against the ih's Π domain.
//! - **The kernel is the judge.** Nothing here is trusted: the recursor is
//!   checked like any other term.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type};
use heather_syntax::{Arm, Expr, ExprKind, LamBinder, Pat, Span};

use crate::surface::walk_expr;
use crate::{Cx, Elaborator};

/// One `match`'s generalization, handed to the route that builds its arms'
/// guards through `Cx::generalized`.
pub(crate) struct Generalization {
    /// The parameter the `match` descends on.
    pub(crate) dec: usize,
    /// The generalized parameters, in ascending declaration order — which is
    /// the order of the motive's Π binders and of the ih's applications.
    pub(crate) positions: Rc<Vec<usize>>,
    /// The `match` this belongs to. A route consumes it only for the `match`
    /// at this span, so a nested `match` on the same parameter — whose arms
    /// were *not* wrapped — never inherits a generalization it cannot honor.
    pub(crate) span: Span,
}

/// The generalization the guard of a `match` at `span` descending on `dec`
/// should carry, if the checking entry planned one.
///
/// Routes that know their `match`'s span pass it; the indexed routes, whose
/// arm environments carry none, match on the parameter alone.
pub(crate) fn guard_gen(cx: &Cx, dec: usize, span: Option<Span>) -> Option<Rc<Vec<usize>>> {
    cx.generalized
        .as_ref()
        .filter(|g| g.dec == dec && span.is_none_or(|s| g.span == s))
        .map(|g| Rc::clone(&g.positions))
}

impl Elaborator {
    /// Which of the declaration's parameters a self-call inside `arms` passes
    /// at something other than the parameter itself, closed under dependency
    /// (a later parameter whose type mentions a generalized one is generalized
    /// too, since its type is only right at the generalized value). Ascending.
    ///
    /// Name-based, and therefore a sizing decision only (module docs).
    pub(crate) fn varying_params(&self, cx: &Cx, arms: &[Arm], dec: usize) -> Vec<usize> {
        let Some(s) = cx.selfref.as_ref() else {
            return Vec::new();
        };
        // A parameter the *scrutinee's* type depends on is an index
        // (`fn append(n: Nat, xs: Vec(n), …)`), and an indexed `match` rebinds
        // it at each arm's own pattern variable
        // (`docs/inductive-indexed-lowering.md` §6, `Guard::rebind`). That is
        // the route's business: never a generalization candidate here, and
        // where the family is not indexed the by-binder refusal stands.
        let fixed: Vec<usize> = (0..dec)
            .filter(|&q| {
                cx.gamma.entries.get(dec).is_some_and(|entry| {
                    entry
                        .ty
                        .abstract_local(&Term::Var(LocalVar((dec - 1 - q) as u32)))
                        .is_some()
                })
            })
            .collect();
        let mut varying: Vec<usize> = Vec::new();
        for arm in arms {
            walk_expr(&arm.body, &mut |e| {
                let Some((args, explicit)) = crate::recursion::surface_self_call(s, e) else {
                    return;
                };
                let positions = (s.n_tyvars..s.params.len())
                    .filter(|&j| explicit || !s.params[j].1);
                for (slot, position) in positions.enumerate() {
                    if position == dec || fixed.contains(&position) {
                        continue;
                    }
                    let Some(arg) = args.get(slot) else { break };
                    let unchanged =
                        matches!(&arg.kind, ExprKind::Var(n) if *n == s.params[position].0);
                    if !unchanged && !varying.contains(&position) {
                        varying.push(position);
                    }
                }
            });
        }
        if varying.is_empty() {
            return varying;
        }
        varying.sort_unstable();
        // Dependency closure, in declaration order so it is transitive: a
        // parameter's type is scoped in the prefix before it, where a
        // generalized parameter `q < p` is `Var(p - 1 - q)`.
        let first = varying[0];
        for p in first + 1..s.params.len() {
            if varying.contains(&p) {
                continue;
            }
            let Some(entry) = cx.gamma.entries.get(p) else { break };
            let depends = varying
                .iter()
                .filter(|&&q| q < p)
                .any(|&q| entry.ty.abstract_local(&Term::Var(LocalVar((p - 1 - q) as u32))).is_some());
            // `p == dec` cannot happen: the scrutinee's dependencies were
            // excluded above, so nothing it depends on is in `varying`.
            if !depends || p == dec {
                continue;
            }
            varying.push(p);
        }
        varying.sort_unstable();
        varying
    }

    /// The locals a `match` on the local `scrutinee` refines: every binder
    /// after it whose type mentions it (directly or through another) and that
    /// an arm names or the goal mentions, with the binders their types need
    /// (issues/elab-match-refines-hypothesis-kernel-rejects.md). Generalized
    /// into the motive like a varied parameter, so in the `Zero` arm of
    /// `match n` a hypothesis `h: ¬(n = 0)` *is* `¬(0 = 0)` — in the kernel's
    /// term, not only in what the arm's author was told. Ascending.
    ///
    /// Two kinds of binder stay where they are. A hidden `#` binder or a
    /// reserved `__` one is the machinery's (an enclosing ih, a convoy
    /// window, a measure recursion's `__dec_h`), and its reader states what
    /// it needs about the binder as it was: the measure rewrite derives each
    /// call's obligation from the unrefined `__dec_h` itself. And a structural
    /// recursion's own `match` keeps its motive the recursion's: a self-call
    /// can pass only declared parameters, and those it varies are
    /// [`Self::varying_params`]'s already.
    pub(crate) fn refined_hypotheses(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrutinee: &Term,
        dec: Option<usize>,
        expected: &Type,
    ) -> Vec<usize> {
        let Term::Var(LocalVar(index)) = scrutinee else {
            return Vec::new();
        };
        let m = cx.gamma.entries.len();
        let x = m - 1 - *index as usize;
        if let (Some(_), Some(s)) = (dec, cx.selfref.as_ref()) {
            let mut calls = false;
            for arm in arms {
                walk_expr(&arm.body, &mut |e| {
                    calls |= crate::recursion::surface_self_call(s, e).is_some();
                });
            }
            if calls {
                return Vec::new();
            }
        }
        // Every binder whose type is about the scrutinee, directly or through
        // an earlier one: what the match *could* refine.
        let mut about: Vec<usize> = Vec::new();
        let mentions = |q: usize, p: usize| {
            cx.gamma.entries.get(q).is_some_and(|entry| {
                entry.ty.abstract_local(&Term::Var(LocalVar((q - 1 - p) as u32))).is_some()
            })
        };
        for q in x + 1..m {
            if mentions(q, x) || about.iter().any(|&p| mentions(q, p)) {
                about.push(q);
            }
        }
        // Of those, what an arm names or the goal mentions. A `match` is also
        // a computation: one in a function body or a motive must stay the
        // term it always was, so that it still converts with the `match` it
        // restates, and a hypothesis nothing reads would change that term
        // while refining nothing. One the goal mentions must go with the
        // goal, whose motive abstracts the scrutinee under it.
        let mut named: Vec<String> = Vec::new();
        for arm in arms {
            walk_expr(&arm.body, &mut |e| {
                if let ExprKind::Var(name) = &e.kind {
                    named.push(name.clone());
                }
            });
        }
        let machinery = |q: usize| cx.names[q].starts_with('#') || cx.names[q].starts_with("__");
        let mut refined: Vec<usize> = about
            .iter()
            .copied()
            .filter(|&q| {
                !machinery(q)
                    && (named.contains(&cx.names[q])
                        || expected.abstract_local(&Term::Var(LocalVar((m - 1 - q) as u32))).is_some())
            })
            .collect();
        // A refined binder's type is only right over the refined binders it
        // mentions, so those go too; one that needs the machinery's stays.
        let mut i = refined.len();
        while i > 0 {
            i -= 1;
            let q = refined[i];
            let needs: Vec<usize> =
                about.iter().copied().filter(|&p| p < q && mentions(q, p) && !refined.contains(&p)).collect();
            if needs.iter().any(|&p| machinery(p)) {
                refined.remove(i);
                continue;
            }
            if !needs.is_empty() {
                refined.extend(needs);
                refined.sort_unstable();
                i = refined.len();
            }
        }
        refined
    }

    /// `Π(y₁ : T_{j₁}) … Π(y_g : T_{j_g}). expected`, with every reference to a
    /// generalized parameter inside the domains and the goal pointing at the
    /// new binder. Scoped in `cx`, like `expected`; its level is the join.
    pub(crate) fn generalize_expected(
        &self,
        cx: &Cx,
        positions: &[usize],
        expected: &Type,
        level: &Level,
    ) -> (Type, Level) {
        let m = cx.gamma.entries.len();
        let g = positions.len();
        let mut ty = expected.apply_local(&rename(&cx.gamma, positions, g));
        let mut level = level.clone();
        for i in (0..g).rev() {
            let p = positions[i];
            let entry = cx.gamma.entries.get(p).expect("a parameter position");
            let dom = entry
                .ty
                .shift_local((m - p) as u32)
                .apply_local(&rename(&cx.gamma, positions, i));
            let dom_level = entry.level.clone();
            ty = Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: level.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(ty),
            };
            level = Level::max(dom_level, level);
        }
        (ty, level)
    }

    /// Each arm's body under `λ y₁ … y_g =>`, the binders carrying the
    /// parameters' own names so that the body's `m` is the generalized one.
    /// The lambdas are unannotated: the domain comes from the arm's expected
    /// Π, which is the one place it is already right.
    pub(crate) fn wrap_arms(&self, cx: &Cx, arms: &[Arm], positions: &[usize]) -> Vec<Arm> {
        arms.iter()
            .map(|arm| {
                let span = arm.body.span;
                // A pattern variable of the same name shadowed the local in
                // the arm as written, so it still does: the generalized
                // binder takes a name the body cannot spell.
                let mut bound = Vec::new();
                arm.binders.iter().for_each(|pat| pattern_names(pat, &mut bound));
                let binders = positions
                    .iter()
                    .map(|&p| LamBinder {
                        name: if bound.contains(&cx.names[p].as_str()) {
                            format!("#{}", cx.names[p])
                        } else {
                            cx.names[p].clone()
                        },
                        ty: None,
                        implicit: false,
                        span,
                    })
                    .collect();
                Arm {
                    ctor: arm.ctor.clone(),
                    default: arm.default,
                    binders: arm.binders.clone(),
                    body: Expr {
                        kind: ExprKind::Lam {
                            binders,
                            body: Box::new(arm.body.clone()),
                        },
                        span,
                    },
                    span: arm.span,
                }
            })
            .collect()
    }

    /// The finished recursor, of type `gen_ty`, applied back to the parameters
    /// it generalized — which lands it at the original goal.
    pub(crate) fn instantiate_generalized(
        &self,
        cx: &Cx,
        term: Term,
        gen_ty: Type,
        positions: &[usize],
    ) -> Term {
        let m = cx.gamma.entries.len();
        let mut term = term;
        let mut ty = gen_ty;
        for &p in positions {
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = ty
            else {
                unreachable!("generalize_expected built one Π per position");
            };
            let arg = Rc::new(Term::Var(LocalVar((m - 1 - p) as u32)));
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
            term = crate::spelling::checked_app(Rc::new(term), dom_level, cod_level, dom, cod, arg);
        }
        term
    }
}

/// Every variable a pattern binds, however deep.
fn pattern_names<'a>(pat: &'a Pat, out: &mut Vec<&'a str>) {
    match pat {
        Pat::Var { name, .. } => out.push(name),
        Pat::Ctor { args, .. } => args.iter().for_each(|arg| pattern_names(arg, out)),
        Pat::Named { pat, .. } => pattern_names(pat, out),
    }
}

/// The substitution `Γ → Γ, y₁ … y_i` that sends the generalized parameter
/// `positions[l]` (for `l < i`) to `y_{l+1}` and every other binder to itself,
/// weakened past the new ones. `i = 0` is the identity.
fn rename(gamma: &LocalCtx, positions: &[usize], i: usize) -> LocalSubst {
    let m = gamma.entries.len();
    let extra = i as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty {
            len: m as u32 + extra,
            base: CtxBase::Nil,
        },
        CtxBase::Var(g) => SubstTail::Wk {
            len: m as u32 + extra,
            ctx_var: g,
        },
    };
    let terms = (0..m)
        .map(|p| {
            let index = match positions[..i].iter().position(|&q| q == p) {
                Some(l) => (i - 1 - l) as u32,
                None => (m - 1 - p) as u32 + extra,
            };
            Rc::new(Term::Var(LocalVar(index)))
        })
        .collect();
    LocalSubst { tail, terms }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rename_sends_generalized_binders_to_the_new_ones() {
        // Γ = a, b, c (positions 0, 1, 2); generalize b then c.
        let mut cx = Cx::empty();
        for n in ["a", "b", "c"] {
            cx.push(n.into(), Type::Nat, Level::Zero);
        }
        let positions = [1usize, 2];
        // Under two new binders y₁ (for b), y₂ (for c): c ↦ Var 0, b ↦ Var 1,
        // a ↦ Var 4 (weakened past y₁ y₂ and its own two successors).
        let sigma = rename(&cx.gamma, &positions, 2);
        let at = |p: usize| Term::Var(LocalVar((2 - p) as u32)).apply_local(&sigma);
        assert_eq!(at(2), Term::Var(LocalVar(0)));
        assert_eq!(at(1), Term::Var(LocalVar(1)));
        assert_eq!(at(0), Term::Var(LocalVar(4)));
        // Under one new binder (for b only): b ↦ Var 0, c ↦ Var 1, a ↦ Var 3.
        let sigma = rename(&cx.gamma, &positions, 1);
        let at = |p: usize| Term::Var(LocalVar((2 - p) as u32)).apply_local(&sigma);
        assert_eq!(at(1), Term::Var(LocalVar(0)));
        assert_eq!(at(2), Term::Var(LocalVar(1)));
        assert_eq!(at(0), Term::Var(LocalVar(3)));
    }

    #[test]
    fn generalized_goal_is_a_pi_over_the_parameters_and_instantiates_back() {
        // Γ = n, m : Nat; goal `Id(Nat; m; n)`; generalize m.
        let mut cx = Cx::empty();
        cx.push("n".into(), Type::Nat, Level::Zero);
        cx.push("m".into(), Type::Nat, Level::Zero);
        let goal = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(Term::Var(LocalVar(0))),
            rhs: Rc::new(Term::Var(LocalVar(1))),
        };
        let e = Elaborator::with_prelude().expect("prelude");
        let (generalized, lvl) = e.generalize_expected(&cx, &[1], &goal, &Level::Zero);
        assert_eq!(lvl, Level::max(Level::Zero, Level::Zero));
        let Type::Pi { dom, cod, .. } = &generalized else {
            panic!("a Π, got {generalized:?}");
        };
        assert_eq!(**dom, Type::Nat);
        // Inside: y is Var 0, n is Var 2 (past y and m).
        assert_eq!(
            **cod,
            Type::Id {
                level: Level::Zero,
                ty: Rc::new(Type::Nat),
                lhs: Rc::new(Term::Var(LocalVar(0))),
                rhs: Rc::new(Term::Var(LocalVar(2))),
            }
        );
        // Applying to m gives the goal back, syntactically.
        let Type::Pi { cod, .. } = &generalized else { unreachable!() };
        let back =
            cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Var(LocalVar(0)))));
        assert_eq!(back, goal);
    }
}
