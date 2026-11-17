//! `cases h;` — take an equation about a call apart along the tests the call
//! is stuck on (issues/cases-on-hypothesis-tactic.md).
//!
//! `emitted: p.call(…) = Some(c)` reads, reduced, as a case on a test of the
//! callee's (`layout.words_fit(…)`). One step of `cases emitted` is what a
//! proof writes by hand at that point:
//!
//! - `absurd(emitted)` when `emitted` now equates two different
//!   constructors (`None = Some(c)`);
//! - `subst(emitted, rest)` when it equates one constructor's applications
//!   with a local in a field (`Some(Out(w, n)) = Some(c)`), which replaces
//!   `c` and ends the inversion;
//! - otherwise `match e: test { C(x̄) => <next step>, … }` on the test it is
//!   stuck on, found as `split_all` finds the test a goal is stuck on
//!   (`goal_combinators::split_stuck`), with `emitted` refined in every arm
//!   by the case split's own reading of hypotheses through calls
//!   (`docs/elaborator/goal-motive-synthesis-design.md` §4.7);
//! - the rest of the block, once `emitted` is stuck on nothing, or once
//!   the splits `cases h as e1, e2` names have all been taken.
//!
//! So the proof built is the hand proof, nested motive-less matches, and the
//! kernel checks it as it checks that. Each step is an unspellable call
//! (`heather_syntax::CASES_HYPOTHESIS`) checked in its arm, where the arm's
//! refinement has already happened, as `split_all`'s steps are.

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::Type;
use heather_syntax::{Arm, CasesName, Expr, ExprKind, MatchForm, Pat, Span};

use crate::inductive::Inductives;
use crate::subst_local::LocalSubsts;
use crate::{Cx, Elaborator, R, err};

/// How many tests one `cases` takes apart along one path before it decides
/// it is looping rather than inverting.
const MAX_SPLITS: usize = 64;

/// The expression one step of `cases h` checks at `expected`: see the
/// module doc. `head` is the step's own head (the names still to give and
/// the last split's fingerprint), `args` the hypothesis and the rest of the
/// block.
pub(crate) fn step(elab: &Elaborator, cx: &Cx, head: &str, args: &[Expr], expected: &Type, span: Span) -> R<Expr> {
    let Some((names, bounded, last)) = heather_syntax::cases_of_head(head) else {
        return err("internal `cases` form has a malformed head", span);
    };
    let [hypothesis, body] = args else {
        return err("internal `cases` form has the wrong arity", span);
    };
    let ExprKind::Var(name) = &hypothesis.kind else {
        return err("`cases` takes apart a hypothesis named by a local", hypothesis.span);
    };
    let var = |name: &str| Expr { kind: ExprKind::Var(name.into()), span };
    let app = |head: &str, args: Vec<Expr>| Expr {
        kind: ExprKind::App { head: Box::new(var(head)), args, named: vec![], explicit: false, goal_oriented: false },
        span,
    };
    let (term, ty, level) = elab.resolve_reading(cx, name, hypothesis.span)?;
    if !matches!(elab.whnf(cx, &ty, span), Ok(Type::Id { .. })) {
        return err(
            format!("`cases {name}` takes apart an equation, and `{name}` is not one"),
            hypothesis.span,
        );
    }
    // A case the split refutes: `emitted` now equates two constructors.
    if Inductives(elab).refuted_by_computation(cx, &var(name)) {
        return Ok(app("absurd", vec![var(name)]));
    }
    // The case that survives: the call's value against the local it names.
    if LocalSubsts(elab).injected(cx, term, &ty, span, true, 0).is_some() {
        return Ok(app("subst", vec![var(name), (*body).clone()]));
    }
    // `cases h as e1, e2` takes the two splits it names, and then only
    // closes or substitutes: what `h` is still stuck on past them is the
    // rest of the block's (`region.code(…) = Some(c)` after `scopes()`).
    if bounded && names.is_empty() && last.is_some() {
        return Ok((*body).clone());
    }
    let premise = Type::Pi {
        dom_level: level,
        cod_level: Level::Zero,
        dom: Rc::new(ty),
        cod: Rc::new(expected.shift_local(1)),
    };
    let Some(split) = crate::goal_combinators::split_stuck(elab, cx, &premise, body, span, false) else {
        if last.is_none() {
            return err(
                format!(
                    "`cases {name}`: `{name}` is not stuck on any test of the call it states, \
                     so there is nothing to take apart"
                ),
                hypothesis.span,
            );
        }
        return Ok((*body).clone());
    };
    // The same test found again in a case of its own split: the split did
    // not refine `h`, and taking it again would not either.
    let fingerprint = format!("{:x}", fingerprint(&split.scrut));
    let taken = last.as_deref().map_or(0, |last| last.split('.').count());
    if last.as_deref().is_some_and(|last| last.rsplit('.').next() == Some(&fingerprint)) {
        return err(
            format!(
                "`cases {name}`: the split on the test `{name}` is stuck on did not refine `{name}` \
                 (a hypothesis passed beside the split's equation in one call is kept as written)"
            ),
            hypothesis.span,
        );
    }
    if taken >= MAX_SPLITS {
        return err(format!("`cases {name}` took apart {MAX_SPLITS} tests on one path and stopped"), hypothesis.span);
    }
    let path = match &last {
        Some(last) => format!("{last}.{fingerprint}"),
        None => fingerprint,
    };
    let (given, later) = match names.split_first() {
        Some((first, rest)) => (Some(first.clone()), rest.to_vec()),
        None => (None, Vec::new()),
    };
    let equation = match &given {
        Some(CasesName { equation, .. }) => equation.clone(),
        None => crate::goal_combinators::fresh(elab, cx, format!("__cases_{}", cx.names.len())),
    };
    let next = heather_syntax::cases_head(&later, bounded, Some(&path));
    let depth = cx.names.len();
    let arms = split
        .arms
        .iter()
        .enumerate()
        .map(|(index, arm)| {
            let arity = arm.binders.len();
            let binders = match &given {
                Some(CasesName { fields, .. }) if fields.len() == arity && arity > 0 => {
                    fields.iter().map(|field| Pat::Var { name: field.clone(), span }).collect()
                }
                _ => (0..arity).map(|field| Pat::Var { name: format!("__cases_{depth}_{index}_{field}"), span }).collect(),
            };
            Arm {
                ctor: arm.ctor.clone(),
                default: false,
                binders,
                body: app(&next, vec![var(name), shielded(body)]),
                span,
            }
        })
        .collect();
    Ok(Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: true,
            scrut: Box::new(split.scrut),
            eqbind: Some(equation),
            motive: None,
            arms,
        },
        span,
    })
}

/// The rest of the block, as an argument of a step beside `h` that is not
/// itself a name: a bare `fa` there would read as `h` passed beside the
/// split's equation `fa`, which keeps `h` as written
/// (`generalize::passed_beside`).
fn shielded(body: &Expr) -> Expr {
    match &body.kind {
        ExprKind::Var(_) => Expr {
            kind: ExprKind::Block(Box::new(heather_syntax::Block {
                stmts: vec![],
                result: Box::new(body.clone()),
                ons: vec![],
                span: body.span,
            })),
            span: body.span,
        },
        _ => body.clone(),
    }
}

/// A fingerprint of a test's spelling, to recognise the same test met again.
fn fingerprint(scrut: &Expr) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    format!("{:?}", scrut.kind).hash(&mut hasher);
    hasher.finish()
}
