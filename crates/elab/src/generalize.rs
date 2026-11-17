//! Induction-hypothesis generalization (issues/ih-generalization.md,
//! docs/tactics/ih-generalization-design.md).
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
//! - **The scan is a sizing decision only.** [`Generalize::varying_params`]
//!   works on names, so shadowing can mislead it in either direction — and
//!   neither direction produces a wrong term. A missed parameter meets the
//!   by-binder refusal that stood before this existed; a parameter generalized
//!   needlessly costs a Π nothing reads. What a call lowers to is decided by
//!   comparing binder positions and by the ordinary application engine
//!   checking each varied argument against the ih's Π domain.
//! - **The kernel is the judge.** Nothing here is trusted: the recursor is
//!   checked like any other term.

use heather_kernel::rc::Rc;

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

/// Generalization's part of the elaborator.
pub(crate) struct Generalize<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Generalize<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Generalize<'_> {
    /// Which of the declaration's parameters a self-call inside `arms` passes
    /// at something other than the parameter itself, closed under dependency
    /// (a later parameter whose type mentions a generalized one is generalized
    /// too, since its type is only right at the generalized value; and an
    /// earlier value implicit a generalized one's type mentions, which the
    /// self-call infers). Ascending.
    ///
    /// Name-based, and therefore a sizing decision only (module docs).
    pub(crate) fn varying_params(&self, cx: &Cx, arms: &[Arm], dec: usize) -> Vec<usize> {
        let Some(s) = cx.selfref.as_ref() else {
            return Vec::new();
        };
        // A parameter the *scrutinee's* type depends on is an index
        // (`fn append(n: Nat, xs: Vec(n), …)`), and an indexed `match` rebinds
        // it at each arm's own pattern variable
        // (`docs/inductives/inductive-indexed-lowering.md` §6, `Guard::rebind`). That is
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
        // Dependency closure, to a fixpoint (a parameter's type is scoped in
        // the prefix before it, where parameter `q < p` is `Var(p - 1 - q)`):
        //
        // - forward: a later parameter whose type mentions a generalized one
        //   is generalized too, since its type is only right at the
        //   generalized value;
        // - backward, for a value implicit: an earlier `{q}` that a
        //   generalized parameter's type mentions is determined by the
        //   varied arguments (`g(k, x + 10, refl)` at `h: e = x` means
        //   `e := x + 10`), so it is generalized and the self-call infers it
        //   (issues/recursion-implicit-inferred-at-self-call.md). Kept
        //   unchanged, the ih would see the top call's `e`.
        let mentions = |p: usize, q: usize| {
            q < p
                && cx.gamma.entries.get(p).is_some_and(|entry| {
                    entry.ty.abstract_local(&Term::Var(LocalVar((p - 1 - q) as u32))).is_some()
                })
        };
        loop {
            let before = varying.len();
            for p in s.n_tyvars..s.params.len() {
                if varying.contains(&p) || p == dec {
                    continue;
                }
                let forward = varying.iter().any(|&q| mentions(p, q));
                // An index the scrutinee's type mentions is rebound by the
                // indexed route, never generalized (above).
                let backward = s.params[p].1
                    && !fixed.contains(&p)
                    && varying.iter().any(|&q| mentions(q, p));
                if forward || backward {
                    varying.push(p);
                }
            }
            if varying.len() == before {
                break;
            }
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
        scrutinee: (&Term, &Type, &Level),
        dec: Option<usize>,
        expected: &Type,
        eqbind: Option<&str>,
        span: Span,
    ) -> Refined {
        let (scrutinee, scrutinee_type, scrutinee_level) = scrutinee;
        let m = cx.gamma.entries.len();
        // A computed scrutinee is abstracted the same way, by syntactic
        // occurrence (docs/language/matching/dependent-match-compiler-design.md §5): a binder
        // whose type contains the term is about it. Only binders after every
        // local the term mentions can be, since the motive abstracts the term
        // as it stands in `cx`.
        let Term::Var(LocalVar(index)) = scrutinee else {
            return self.refined_by_occurrence(cx, arms, (scrutinee, scrutinee_type, scrutinee_level), expected, eqbind, span);
        };
        let x = m - 1 - *index as usize;
        if let (Some(_), Some(s)) = (dec, cx.selfref.as_ref()) {
            let mut calls = false;
            for arm in arms {
                walk_expr(&arm.body, &mut |e| {
                    calls |= crate::recursion::surface_self_call(s, e).is_some();
                });
            }
            if calls {
                return Refined::default();
            }
        }
        // Every binder whose type is about the scrutinee, directly or through
        // an earlier one: what the match *could* refine.
        let mut about: Vec<usize> = Vec::new();
        for q in x + 1..m {
            if mentions_binder(cx, q, x) || about.iter().any(|&p| mentions_binder(cx, q, p)) {
                about.push(q);
            }
        }
        Refined {
            positions: self.select_refined(cx, arms, expected, about, eqbind.map(|h| (scrutinee, Some(h)))),
            retyped: Vec::new(),
        }
    }

    /// [`Self::refined_hypotheses`] at a computed scrutinee. A binder an arm
    /// names whose type does not contain the term is still about it when the
    /// type, reduced, is stuck on it through a call
    /// (issues/case-split-refines-hypotheses-under-calls.md): it is refined
    /// at that reading, which `retyped` carries.
    fn refined_by_occurrence(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrutinee: (&Term, &Type, &Level),
        expected: &Type,
        eqbind: Option<&str>,
        span: Span,
    ) -> Refined {
        let (scrutinee, scrutinee_type, scrutinee_level) = scrutinee;
        let m = cx.gamma.entries.len();
        let wrapped = Type::El { level: Level::Zero, tm: Rc::new(scrutinee.clone()) };
        let first = (0..m)
            .rev()
            .find(|&p| wrapped.abstract_local(&Term::Var(LocalVar((m - 1 - p) as u32))).is_some())
            .map_or(0, |p| p + 1);
        let contains = |q: usize| {
            cx.gamma.entries.get(q).is_some_and(|entry| {
                entry.ty.shift_local((m - q) as u32).abstract_local(scrutinee).is_some()
            })
        };
        let named = arm_names(arms);
        let mut about: Vec<usize> = Vec::new();
        let mut retyped: Vec<(usize, Type)> = Vec::new();
        for q in first..m {
            if contains(q) || about.iter().any(|&p| mentions_binder(cx, q, p)) {
                about.push(q);
                continue;
            }
            // Only what an arm names is read reduced: it is all the
            // selection below could keep, and the reading costs a reduction
            // and a conversion per stuck position.
            if machinery(cx, q) || !named.iter().any(|n| n == &cx.names[q]) {
                continue;
            }
            let entry = cx.gamma.entries.get(q).expect("a binder of the context");
            let ty = entry.ty.shift_local((m - q) as u32);
            if let Some(read) = crate::matching::hypothesis_through_calls(
                self.0, cx, &ty, scrutinee, scrutinee_type, scrutinee_level, span,
            ) {
                about.push(q);
                retyped.push((q, read));
            }
        }
        if about.is_empty() {
            return Refined::default();
        }
        let positions = self.select_refined(cx, arms, expected, about, eqbind.map(|h| (scrutinee, Some(h))));
        retyped.retain(|(q, _)| positions.contains(q));
        Refined { positions, retyped }
    }

    /// Of the binders `about` the scrutinee, what an arm names or the goal
    /// mentions, closed under what their types need. Under `match h:`
    /// (`convoy`, the scrutinee scoped in `cx`), a binder an arm names that
    /// takes an equation about the scrutinee is left as written: it is what
    /// the arm passes `h` to, and `h` is about the scrutinee as written. At a
    /// computed scrutinee (`convoy`'s name of `h`), so is one an arm passes
    /// beside `h` in one call, `InSlot => t.goes_slot(…, slot, within, …)`:
    /// the callee states the two about the test as written, which is what
    /// passing the evidence along is for
    /// (issues/case-split-refines-hypotheses-under-calls.md).
    fn select_refined(
        &self,
        cx: &Cx,
        arms: &[Arm],
        expected: &Type,
        about: Vec<usize>,
        convoy: Option<(&Term, Option<&str>)>,
    ) -> Vec<usize> {
        let m = cx.gamma.entries.len();
        let mentions = |q: usize, p: usize| mentions_binder(cx, q, p);
        // Of those, what an arm names or the goal mentions. A `match` is also
        // a computation: one in a function body or a motive must stay the
        // term it always was, so that it still converts with the `match` it
        // restates, and a hypothesis nothing reads would change that term
        // while refining nothing. One the goal mentions must go with the
        // goal, whose motive abstracts the scrutinee under it.
        let named = arm_names(arms);
        // Nothing is left as written for what the arm's source passes it
        // to or with: the arm has both readings, and each use takes the one
        // its position asks for (docs/language/matching/arm-readings-design.md).
        // A hypothesis called what the equation is called is shadowed by it
        // in every arm: the name an arm writes is the equation.
        let equation = convoy.and_then(|(_, h)| h);
        let takes_h = |q: usize| equation.is_some_and(|h| h == &cx.names[q]);
        let machinery = |q: usize| machinery(cx, q);
        let mut refined: Vec<usize> = about
            .iter()
            .copied()
            .filter(|&q| {
                !machinery(q)
                    && ((named.iter().any(|n| n == &cx.names[q]) && !takes_h(q))
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
        self.generalize_retyped(cx, positions, &[], expected, level)
    }

    /// [`Self::generalize_expected`], with the binders in `retyped` given
    /// the type beside them (scoped in `cx`, and converting to their own)
    /// in place of the one they were bound at.
    pub(crate) fn generalize_retyped(
        &self,
        cx: &Cx,
        positions: &[usize],
        retyped: &[(usize, Type)],
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
            let dom = match retyped.iter().find(|(q, _)| *q == p) {
                Some((_, ty)) => ty.clone(),
                None => entry.ty.shift_local((m - p) as u32),
            }
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
                        name: if bound.contains(&&cx.names[p]) {
                            format!("#{}", &cx.names[p])
                        } else {
                            cx.names[p].to_string()
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

/// Whether an arm calls the declaration being elaborated.
pub(crate) fn arms_call_self(cx: &Cx, arms: &[Arm]) -> bool {
    let Some(s) = cx.selfref.as_ref() else { return false };
    let mut calls = false;
    for arm in arms {
        walk_expr(&arm.body, &mut |e| {
            calls |= crate::recursion::surface_self_call(s, e).is_some();
        });
    }
    calls
}

/// What a `match` refines: the binders it generalizes, ascending, and those
/// of them it reads at another spelling of their type
/// ([`Generalize::refined_hypotheses`]).
#[derive(Default)]
pub(crate) struct Refined {
    pub(crate) positions: Vec<usize>,
    pub(crate) retyped: Vec<(usize, Type)>,
}

/// Every name an arm's body mentions as a variable.
fn arm_names(arms: &[Arm]) -> Vec<String> {
    let mut named: Vec<String> = Vec::new();
    for arm in arms {
        walk_expr(&arm.body, &mut |e| {
            if let ExprKind::Var(name) = &e.kind {
                named.push(name.clone());
            }
        });
    }
    named
}

/// The names an arm passes as arguments of one call beside `h`, the
/// equation of a `match h:` (a method call's receiver is not one of them).
fn passed_beside(arms: &[Arm], h: &str) -> Vec<String> {
    let mut beside: Vec<String> = Vec::new();
    for arm in arms {
        walk_expr(&arm.body, &mut |e| {
            let (args, named) = match &e.kind {
                ExprKind::App { args, named, .. } => (args, named),
                ExprKind::Dot { args: Some(args), named, .. } => (args, named),
                _ => return,
            };
            let names: Vec<&str> = args
                .iter()
                .chain(named.iter().map(|arg| &arg.expr))
                .filter_map(|arg| match &arg.kind {
                    ExprKind::Var(name) => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            if names.contains(&h) {
                beside.extend(names.into_iter().filter(|&n| n != h).map(str::to_string));
            }
        });
    }
    beside
}

/// A hidden `#` binder or a reserved `__` one: the machinery's, never refined.
fn machinery(cx: &Cx, q: usize) -> bool {
    cx.names[q].starts_with('#') || cx.names[q].starts_with("__")
}

/// Every variable a pattern binds, however deep.
pub(crate) fn pattern_names<'a>(pat: &'a Pat, out: &mut Vec<&'a str>) {
    match pat {
        Pat::Var { name, .. } => out.push(name),
        Pat::Ctor { args, .. } => args.iter().for_each(|arg| pattern_names(arg, out)),
        Pat::Named { pat, .. } => pattern_names(pat, out),
    }
}

/// The substitution `Γ → Γ, y₁ … y_i` that sends the generalized parameter
/// `positions[l]` (for `l < i`) to `y_{l+1}` and every other binder to itself,
/// weakened past the new ones. `i = 0` is the identity.
pub(crate) fn rename(gamma: &LocalCtx, positions: &[usize], i: usize) -> LocalSubst {
    let m = gamma.entries.len();
    let extra = i as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty,
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
        let (generalized, lvl) = Generalize(&e).generalize_expected(&cx, &[1], &goal, &Level::Zero);
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

/// Does `ty` take an equation about `scrutinee` — is one of its Π
/// telescope's domains `scrutinee = c` or `c = scrutinee`? Both scoped in
/// the same context; the scrutinee is weakened past each Π it crosses.
fn takes_equation_about(ty: &Type, scrutinee: &Term) -> bool {
    let mut ty = ty;
    let mut s = scrutinee.clone();
    loop {
        let Type::Pi { dom, cod, .. } = ty else { return false };
        let sides = match &**dom {
            Type::Id { lhs, rhs, .. } => Some((lhs, rhs)),
            Type::El { tm, .. } => match &**tm {
                Term::TmId { lhs, rhs, .. } => Some((lhs, rhs)),
                _ => None,
            },
            _ => None,
        };
        if sides.is_some_and(|(l, r)| **l == s || **r == s) {
            return true;
        }
        s = s.shift_local(1);
        ty = cod;
    }
}

/// Whether binder `q`'s type mentions the earlier binder `p`.
pub(crate) fn mentions_binder(cx: &Cx, q: usize, p: usize) -> bool {
    cx.gamma.entries.get(q).is_some_and(|entry| {
        entry.ty.abstract_local(&Term::Var(LocalVar((q - 1 - p) as u32))).is_some()
    })
}

/// An alias whose type mentions a `match`'s scrutinee, carried through the
/// match as a convoy (docs/language/matching/dependent-match-compiler-design.md §7.2).
pub(crate) struct DependentAlias {
    pub(crate) name: String,
    pub(crate) ty: Type,
    pub(crate) level: Level,
    /// The alias by name: resolved, and so spliced, only once the match is
    /// built and applied back to it.
    pub(crate) alias: Rc<crate::Alias>,
}

impl Generalize<'_> {
    /// The aliases visible here whose type contains `scrutinee` and that some
    /// arm names. An alias is a term, not a binder, so nothing else would
    /// refine it: in the arm for `C`, its type would still speak of the
    /// scrutinee, while the arm is checked as if it spoke of `C`. That is a
    /// later field of a constructor whose type depends on the matched field,
    /// the shape a deep pattern compiles to
    /// (issues/deep-pattern-dependent-later-field.md).
    pub(crate) fn dependent_aliases(&self, cx: &Cx, arms: &[Arm], scrutinee: &Term) -> Vec<DependentAlias> {
        let mut named: Vec<String> = Vec::new();
        for arm in arms {
            walk_expr(&arm.body, &mut |e| {
                if let ExprKind::Var(name) = &e.kind {
                    named.push(name.clone());
                }
            });
        }
        // An arm that names the scrutinee speaks of it unrefined — it is not
        // rebound to the arm's constructor — so whatever it pairs the
        // scrutinee with must stay unrefined too: `g(c, k)` with `k : Resp(c) →
        // Nat` checks only at `c`'s own type. The convoy is for an arm that
        // cannot name the scrutinee, a deep pattern's column above all.
        let names_scrutinee = cx.aliases.iter().any(|alias| {
            named.iter().any(|n| *n == alias.name)
                && alias.at((cx.names.len() - alias.depth) as u32).0 == *scrutinee
        }) || matches!(scrutinee, Term::Var(LocalVar(i))
            if named.iter().any(|n| *n == cx.names[cx.names.len() - 1 - *i as usize]));
        if names_scrutinee {
            return Vec::new();
        }
        let wrapped = Type::El { level: Level::Zero, tm: Rc::new(scrutinee.clone()) };
        let mut seen: Vec<&str> = Vec::new();
        let mut out = Vec::new();
        for alias in cx.aliases.iter().rev() {
            let name = alias.name.as_str();
            if seen.contains(&name) {
                continue;
            }
            seen.push(name);
            if !named.iter().any(|n| n == name) || cx.names.iter().rposition(|n| n == name).is_some_and(|p| alias.depth <= p) {
                continue;
            }
            let by = (cx.names.len() - alias.depth) as u32;
            let (term, ty) = alias.at(by);
            // The scrutinee itself, or an alias the scrutinee is built from,
            // is not convoyed: abstracting it is the motive's job.
            if term == *scrutinee || wrapped.abstract_local(&term).is_some() {
                continue;
            }
            if ty.abstract_local(scrutinee).is_some() {
                out.push(DependentAlias { name: alias.name.clone(), ty, level: alias.level.clone(), alias: Rc::clone(alias) });
            }
        }
        out.reverse();
        out
    }

    /// `Π(a₁ : T₁) … (aₙ : Tₙ). expected`, each domain weakened past the
    /// binders before it.
    pub(crate) fn alias_generalized(&self, dependents: &[DependentAlias], expected: &Type, level: &Level) -> (Type, Level) {
        let n = dependents.len() as u32;
        let mut ty = expected.shift_local(n);
        let mut level = level.clone();
        for (i, a) in dependents.iter().enumerate().rev() {
            ty = Type::Pi {
                dom_level: a.level.clone(),
                cod_level: level.clone(),
                dom: Rc::new(a.ty.shift_local(i as u32)),
                cod: Rc::new(ty),
            };
            level = Level::max(a.level.clone(), level);
        }
        (ty, level)
    }

    /// Each arm under `λ a₁ … aₙ =>`, so that the body's names are the
    /// convoyed binders; a pattern variable of the same name keeps the arm's
    /// own meaning, as in [`Self::wrap_arms`].
    pub(crate) fn wrap_alias_arms(&self, arms: &[Arm], dependents: &[DependentAlias]) -> Vec<Arm> {
        arms.iter()
            .map(|arm| {
                let span = arm.body.span;
                let mut bound = Vec::new();
                arm.binders.iter().for_each(|pat| pattern_names(pat, &mut bound));
                let binders = dependents
                    .iter()
                    .map(|a| LamBinder {
                        name: if bound.contains(&a.name.as_str()) { format!("#{}", a.name) } else { a.name.clone() },
                        ty: None,
                        implicit: false,
                        span,
                    })
                    .collect();
                Arm {
                    ctor: arm.ctor.clone(),
                    default: arm.default,
                    binders: arm.binders.clone(),
                    body: Expr { kind: ExprKind::Lam { binders, body: Box::new(arm.body.clone()) }, span },
                    span: arm.span,
                }
            })
            .collect()
    }

    /// The match, of type `gen_ty`, applied back to the aliases it convoyed.
    pub(crate) fn instantiate_aliases(&self, cx: &Cx, term: Term, gen_ty: Type, dependents: &[DependentAlias]) -> Term {
        let mut term = term;
        let mut ty = gen_ty;
        for a in dependents {
            let Type::Pi { dom_level, cod_level, dom, cod } = ty else {
                unreachable!("alias_generalized built one Π per alias");
            };
            let by = (cx.names.len() - a.alias.depth) as u32;
            let arg = Rc::new(a.alias.splice(by).0);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
            term = crate::spelling::checked_app(Rc::new(term), dom_level, cod_level, dom, cod, arg);
        }
        term
    }
}
