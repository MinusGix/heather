//! Checking-only goal-tree combinators.
//!
//! `split_all; all_goals { body }` is elaborator sugar for an ordinary nested
//! match whose leaves are copies of `body`. The generated proof remains an
//! ordinary term and crosses the declaration's normal kernel gate.

use heather_syntax::{Arm, Expr, ExprKind, MatchForm, Pat, Span};

use crate::{Cx, Elaborator};

struct FiniteLocal {
    name: String,
    constructors: Vec<(String, usize)>,
}

fn finite_locals(elab: &Elaborator, cx: &Cx) -> Vec<FiniteLocal> {
    cx.names
        .iter()
        .zip(cx.gamma.entries.iter())
        .filter_map(|(name, entry)| {
            let inductive = elab.tag_of(&entry.ty)?;
            // Recursive and indexed families are not finite case domains.
            // Non-recursive constructors may carry payloads; splitting still
            // creates finitely many goals and binds those payloads normally.
            if inductive.recursive || inductive.index.is_some() {
                return None;
            }
            Some(FiniteLocal {
                name: name.clone(),
                constructors: inductive
                    .ctors
                    .iter()
                    .map(|ctor| (ctor.name.clone(), ctor.fields.len()))
                    .collect(),
            })
        })
        .collect()
}

fn tree(locals: &[FiniteLocal], leaf: &Expr, span: Span, depth: usize) -> Expr {
    let Some((local, rest)) = locals.split_first() else {
        return leaf.clone();
    };
    let branch = tree(rest, leaf, span, depth + 1);
    Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: true,
            scrut: Box::new(Expr {
                kind: ExprKind::Var(local.name.clone()),
                span,
            }),
            eqbind: None,
            motive: None,
            arms: local
                .constructors
                .iter()
                .enumerate()
                .map(|(ctor_index, (ctor, arity))| Arm {
                    ctor: ctor.clone(),
                    default: false,
                    binders: (0..*arity)
                        .map(|field| Pat::Var {
                            name: format!("__split_all_{depth}_{ctor_index}_{field}"),
                            span,
                        })
                        .collect(),
                    body: branch.clone(),
                    span,
                })
                .collect(),
        },
        span,
    }
}

pub(crate) fn split_all(elab: &Elaborator, cx: &Cx, leaf: &Expr, span: Span) -> Expr {
    tree(&finite_locals(elab, cx), leaf, span, 0)
}
