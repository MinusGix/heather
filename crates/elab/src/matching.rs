//! Shared motive mechanics for surface eliminators.
//!
//! Route-specific lowering remains with the Nat, inductive, indexed, forded,
//! and `Wf` owners.  This module owns what all of them consume: reading a
//! written motive, synthesizing a motive from a checking goal, and the pure
//! syntax/core transformation used by convoy matching.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::{Arm, Expr, ExprKind, LamBinder, Span, Ty, TyKind};

use crate::diagnostics::STUCK_CANDIDATES;
use crate::{Cx, R, err};

/// Semantic reads required by the motive-synthesis ladder.
pub(crate) trait MotiveSynthesisElab {
    fn read_motive_type(&self, cx: &Cx, ty: &Type, span: Span) -> Option<Type>;
    fn read_motive_term(&self, cx: &Cx, term: &Term, span: Span) -> Option<Rc<Term>>;
    fn motive_candidate_converts(
        &self,
        cx: &Cx,
        candidate: &Term,
        scrutinee: &Term,
        scrutinee_type: &Type,
        scrutinee_level: &Level,
    ) -> bool;
}

/// The mechanically convoyed motive and arms, ready for ordinary lowering.
pub(crate) struct ConvoyPlan {
    pub(crate) motive: Type,
    pub(crate) level: Level,
    pub(crate) arms: Vec<Arm>,
}

/// Decorate an ordinary motive and its arms with `scrutinee = pattern`.
pub(crate) fn plan_convoy(
    binder: &str,
    arms: &[Arm],
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    motive: &Type,
    motive_level: &Level,
) -> ConvoyPlan {
    let equation = Type::Id {
        level: scrutinee_level.clone(),
        ty: Rc::new(scrutinee_type.shift_local(1)),
        lhs: Rc::new(scrutinee.shift_local(1)),
        rhs: Rc::new(Term::Var(LocalVar(0))),
    };
    let convoyed_motive = Type::Pi {
        dom_level: scrutinee_level.clone(),
        cod_level: motive_level.clone(),
        dom: Rc::new(equation),
        cod: Rc::new(motive.shift_local(1)),
    };
    let arms = arms
        .iter()
        .map(|arm| Arm {
            ctor: arm.ctor.clone(),
            default: arm.default,
            binders: arm.binders.clone(),
            body: Expr {
                kind: ExprKind::Lam {
                    binders: vec![LamBinder {
                        name: binder.to_string(),
                        ty: None,
                        implicit: false,
                        span: arm.body.span,
                    }],
                    body: Box::new(arm.body.clone()),
                },
                span: arm.body.span,
            },
            span: arm.span,
        })
        .collect();
    ConvoyPlan {
        motive: convoyed_motive,
        level: Level::max(scrutinee_level.clone(), motive_level.clone()),
        arms,
    }
}

/// Apply a convoyed eliminator to reflexivity, recovering the original type.
pub(crate) fn finish_convoy(
    eliminator: Term,
    scrutinee: Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    motive_level: &Level,
    result: &Type,
) -> Term {
    let scrutinee = Rc::new(scrutinee);
    let scrutinee_type = Rc::new(scrutinee_type.clone());
    Term::App {
        fun: Rc::new(eliminator),
        dom_level: scrutinee_level.clone(),
        cod_level: motive_level.clone(),
        dom: Rc::new(Type::Id {
            level: scrutinee_level.clone(),
            ty: Rc::clone(&scrutinee_type),
            lhs: Rc::clone(&scrutinee),
            rhs: Rc::clone(&scrutinee),
        }),
        // The Π is non-dependent, so the result is weakened past its equation
        // binder.
        cod: Rc::new(result.shift_local(1)),
        arg: Rc::new(Term::Refl {
            level: scrutinee_level.clone(),
            ty: scrutinee_type,
            tm: scrutinee,
        }),
    }
}

/// Take apart a written motive lambda into its binders and type body.
pub(crate) fn motive_lam(expression: &Expr, arity: usize, advice: &str) -> R<(Vec<String>, Ty)> {
    let ExprKind::Lam { binders, body } = &expression.kind else {
        return err(format!("a motive is a lambda: {advice}"), expression.span);
    };
    if binders.len() != arity {
        return err(
            format!(
                "this motive binds {} name(s), but {arity} are needed: {advice}",
                binders.len()
            ),
            expression.span,
        );
    }
    if let Some(binder) = binders.iter().find(|binder| binder.ty.is_some()) {
        return err(
            format!(
                "a motive binder takes no annotation: `{}`'s type is fixed by what the \
                 motive is a motive for",
                binder.name
            ),
            expression.span,
        );
    }
    let names = binders.iter().map(|binder| binder.name.clone()).collect();
    let ty = crate::surface::expression_as_type(body)
        .unwrap_or_else(|| Ty { kind: TyKind::OfExpr(body.clone()), span: body.span });
    Ok((names, ty))
}

/// Synthesize a dependent motive for a motive-less match in checking mode.
pub(crate) fn synthesize_motive(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    expected: &Type,
    span: Span,
) -> Type {
    let rewrap = field_rewrap(scrutinee);
    if let Some(motive) = abstract_scrut(expected, scrutinee, &rewrap) {
        return motive;
    }
    let Some(exposed) = expose(elab, cx, expected, span) else {
        return expected.shift_local(1);
    };
    if let Some(motive) = abstract_stuck(
        elab,
        cx,
        &exposed,
        scrutinee,
        scrutinee_type,
        scrutinee_level,
    ) {
        return motive;
    }
    if let Some(motive) = abstract_scrut(&exposed, scrutinee, &rewrap) {
        return motive;
    }
    expected.shift_local(1)
}

fn abstract_stuck(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    exposed: &Type,
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
) -> Option<Type> {
    let mut candidates = Vec::new();
    let mut budget = STUCK_CANDIDATES;
    stuck_in_type(exposed, &mut candidates, &mut budget);
    candidates.dedup();
    let hits: Vec<Term> = candidates
        .into_iter()
        .filter(|candidate| {
            candidate == scrutinee
                || elab.motive_candidate_converts(
                    cx,
                    candidate,
                    scrutinee,
                    scrutinee_type,
                    scrutinee_level,
                )
        })
        .collect();
    exposed.abstract_local_any(&hits)
}

fn expose(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    ty: &Type,
    span: Span,
) -> Option<Type> {
    match elab.read_motive_type(cx, ty, span)? {
        Type::Id { level, ty, lhs, rhs } => Some(Type::Id {
            level,
            ty,
            lhs: elab.read_motive_term(cx, &lhs, span)?,
            rhs: elab.read_motive_term(cx, &rhs, span)?,
        }),
        Type::El { level, tm } => Some(Type::El {
            level,
            tm: elab.read_motive_term(cx, &tm, span)?,
        }),
        Type::Pi { dom_level, cod_level, dom, cod } => Some(Type::Pi {
            dom_level,
            cod_level,
            dom: Rc::new(expose(elab, cx, &dom, span)?),
            cod,
        }),
        head => Some(head),
    }
}

fn stuck_in_type(ty: &Type, out: &mut Vec<Term>, budget: &mut u32) {
    match ty {
        Type::Id { lhs, rhs, .. } => {
            stuck_scrutinees(lhs, out, budget);
            stuck_scrutinees(rhs, out, budget);
        }
        Type::El { tm, .. } => stuck_scrutinees(tm, out, budget),
        Type::Pi { dom, .. } => stuck_in_type(dom, out, budget),
        _ => {}
    }
}

fn stuck_scrutinees(term: &Term, out: &mut Vec<Term>, budget: &mut u32) {
    if *budget == 0 {
        return;
    }
    *budget -= 1;
    let scrutinee = match term {
        Term::ElimNat { scrut, .. }
        | Term::ElimEmpty { scrut, .. }
        | Term::ElimSEmpty { scrut, .. }
        | Term::Case { scrut, .. }
        | Term::ElimW { scrut, .. }
        | Term::ElimWf { scrut, .. } => Some(scrut),
        Term::Fst { pair, .. } | Term::Snd { pair, .. } => Some(pair),
        Term::J { proof, .. } | Term::Transp { proof, .. } => Some(proof),
        _ => None,
    };
    if let Some(scrutinee) = scrutinee {
        out.push((**scrutinee).clone());
        stuck_scrutinees(scrutinee, out, budget);
        return;
    }
    match term {
        Term::Succ(term) => stuck_scrutinees(term, out, budget),
        Term::Inl { val, .. } | Term::Inr { val, .. } => {
            stuck_scrutinees(val, out, budget);
        }
        Term::Pair { fst, snd, .. } => {
            stuck_scrutinees(fst, out, budget);
            stuck_scrutinees(snd, out, budget);
        }
        Term::Sup { label, children, .. } | Term::Supf { label, children, .. } => {
            stuck_scrutinees(label, out, budget);
            stuck_scrutinees(children, out, budget);
        }
        Term::App { fun, arg, .. } => {
            stuck_scrutinees(fun, out, budget);
            stuck_scrutinees(arg, out, budget);
        }
        _ => {}
    }
}

fn abstract_scrut(
    goal: &Type,
    scrutinee: &Term,
    rewrap: &Option<(Term, Term)>,
) -> Option<Type> {
    goal.abstract_local(scrutinee).or_else(|| {
        let (base, replacement) = rewrap.as_ref()?;
        goal.abstract_local_with(base, replacement)
    })
}

fn field_rewrap(scrutinee: &Term) -> Option<(Term, Term)> {
    let Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } = scrutinee else {
        return None;
    };
    let mut base = Rc::clone(pair);
    let mut replacement = Term::Pair {
        fst_level: fst_level.clone(),
        snd_level: snd_level.clone(),
        fst_ty: Rc::new(fst_ty.shift_local(1)),
        snd_ty: Rc::new(snd_ty.shift_local(1)),
        fst: Rc::new(Term::Var(LocalVar(0))),
        snd: Rc::new(Term::Snd {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::new(fst_ty.shift_local(1)),
            snd_ty: Rc::new(snd_ty.shift_local(1)),
            pair: Rc::new(pair.shift_local(1)),
        }),
    };
    while let Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } = &*base {
        let (fst_ty, snd_ty) = (
            Rc::new(fst_ty.shift_local(1)),
            Rc::new(snd_ty.shift_local(1)),
        );
        replacement = Term::Pair {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::clone(&fst_ty),
            snd_ty: Rc::clone(&snd_ty),
            fst: Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty,
                snd_ty,
                pair: Rc::new(pair.shift_local(1)),
            }),
            snd: Rc::new(replacement),
        };
        base = Rc::clone(pair);
    }
    Some(((*base).clone(), replacement))
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPAN: Span = Span { start: 0, end: 1 };

    struct Fake;

    impl MotiveSynthesisElab for Fake {
        fn read_motive_type(&self, _cx: &Cx, ty: &Type, _span: Span) -> Option<Type> {
            Some(ty.clone())
        }

        fn read_motive_term(&self, _cx: &Cx, term: &Term, _span: Span) -> Option<Rc<Term>> {
            Some(Rc::new(term.clone()))
        }

        fn motive_candidate_converts(
            &self,
            _cx: &Cx,
            candidate: &Term,
            scrutinee: &Term,
            _scrutinee_type: &Type,
            _scrutinee_level: &Level,
        ) -> bool {
            candidate == scrutinee
        }
    }

    #[test]
    fn motive_synthesis_abstracts_or_weakens_without_an_elaborator() {
        let scrutinee = Term::Var(LocalVar(0));
        let expected = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(scrutinee.clone()),
            rhs: Rc::new(Term::Zero),
        };
        let motive = synthesize_motive(
            &Fake,
            &Cx::empty(),
            &scrutinee,
            &Type::Nat,
            &Level::Zero,
            &expected,
            SPAN,
        );
        assert_ne!(motive, expected.shift_local(1));

        let constant = Type::Nat;
        assert_eq!(
            synthesize_motive(
                &Fake,
                &Cx::empty(),
                &scrutinee,
                &Type::Nat,
                &Level::Zero,
                &constant,
                SPAN,
            ),
            constant.shift_local(1)
        );
    }

    #[test]
    fn convoy_planning_is_a_pure_match_transformation() {
        let arm = Arm {
            ctor: "Zero".into(),
            default: false,
            binders: Vec::new(),
            body: Expr { kind: ExprKind::Num(0), span: SPAN },
            span: SPAN,
        };
        let plan = plan_convoy(
            "equation",
            &[arm],
            &Term::Zero,
            &Type::Nat,
            &Level::Zero,
            &Type::Nat,
            &Level::Zero,
        );
        assert!(matches!(plan.motive, Type::Pi { dom, .. } if matches!(&*dom, Type::Id { .. })));
        assert!(matches!(
            &plan.arms[0].body.kind,
            ExprKind::Lam { binders, .. } if binders[0].name == "equation"
        ));

        let finished = finish_convoy(
            Term::Zero,
            Term::Zero,
            &Type::Nat,
            &Level::Zero,
            &Level::Zero,
            &Type::Nat,
        );
        assert!(matches!(finished, Term::App { arg, .. } if matches!(&*arg, Term::Refl { .. })));
    }
}
