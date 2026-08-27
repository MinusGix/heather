//! Ordinary block statements and block-expression sequencing.
//!
//! A surface `let` is an elaborator alias, not a kernel binder.  This module
//! owns the consequences of that decision: statements extend a cloned [`Cx`],
//! record destructuring installs projections in declaration order, and a block
//! contributes only the term synthesized or checked for its result.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Block, Expr, ExprKind, LamBinder, Pat, Span, Stmt, Ty};

use crate::inductive::Inductive;
use crate::{Alias, Cx, DictBinder, R, Skel, err, skel_of_lam_binders, skel_of_ty};

/// Recursive expression and registry services required by ordinary statements.
pub(crate) trait StatementElab {
    fn lower_let_annotation(&self, cx: &Cx, annotation: &Ty) -> R<(Type, Level)>;

    fn check_let_value(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
        skeleton: Option<&Skel>,
    ) -> R<Term>;

    fn infer_statement_expression(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)>;

    fn infer_let_lambda(
        &self,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
    ) -> R<(Term, Type, Level)>;

    fn dictionary_alias(&self, name: &str, annotation: &Ty) -> Option<DictBinder>;

    fn record_for_destructuring(
        &self,
        cx: &Cx,
        record_type: &Type,
        span: Span,
    ) -> Option<Rc<Inductive>>;

    fn project_destructured_field(
        &self,
        cx: &Cx,
        record: &Inductive,
        record_type: &Type,
        value: Rc<Term>,
        index: usize,
        span: Span,
    ) -> R<(Term, Type, Level)>;
}

/// Checking-mode recursion for a block result.
pub(crate) trait BlockCheckingElab: StatementElab {
    #[allow(clippy::too_many_arguments)]
    fn check_block_result(
        &self,
        cx: &Cx,
        result: &Expr,
        expected: &Type,
        level: &Level,
        hint: Option<(&str, &str)>,
        skeleton: Option<&Skel>,
        capture_slots: bool,
    ) -> R<Term>;
}

/// Extend a clone of `cx` with the aliases introduced by `statements`.
pub(crate) fn elaborate(elab: &impl StatementElab, cx: &Cx, statements: &[Stmt]) -> R<Cx> {
    let mut cx = cx.clone();
    for statement in statements {
        match statement {
            Stmt::Let { name, ty, expr, .. } => {
                elaborate_let(elab, &mut cx, name, ty.as_ref(), expr)?;
            }
            Stmt::LetRecord { fields, expr, span } => {
                elaborate_record_let(elab, &mut cx, fields, expr, *span)?;
            }
            Stmt::LetCode { span, .. } => {
                return err(
                    "`let code` is meta-layer syntax: it binds code inside a \
                     `meta fn` body (docs/in-language-map-design.md §3)",
                    *span,
                );
            }
        }
    }
    Ok(cx)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn check_block(
    elab: &impl BlockCheckingElab,
    cx: &Cx,
    block: &Block,
    expected: &Type,
    level: &Level,
    hint: Option<(&str, &str)>,
    skeleton: Option<&Skel>,
    capture_slots: bool,
) -> R<Term> {
    let cx = elaborate(elab, cx, &block.stmts)?;
    elab.check_block_result(
        &cx,
        &block.result,
        expected,
        level,
        hint,
        skeleton,
        capture_slots,
    )
}

pub(crate) fn infer_block(
    elab: &impl StatementElab,
    cx: &Cx,
    block: &Block,
) -> R<(Term, Type, Level)> {
    let cx = elaborate(elab, cx, &block.stmts)?;
    elab.infer_statement_expression(&cx, &block.result)
}

fn elaborate_let(
    elab: &impl StatementElab,
    cx: &mut Cx,
    name: &str,
    annotation: Option<&Ty>,
    expression: &Expr,
) -> R<()> {
    let (term, ty, level, skeleton) = match annotation {
        Some(annotation) => {
            let (ty, level) = elab.lower_let_annotation(cx, annotation)?;
            let skeleton = skel_of_ty(annotation);
            let term = elab.check_let_value(cx, expression, &ty, &level, skeleton.as_deref())?;
            (term, ty, level, skeleton)
        }
        None => {
            let (term, ty, level, skeleton) = match &expression.kind {
                ExprKind::Lam { binders, body } => {
                    let inferred = elab.infer_let_lambda(cx, binders, body)?;
                    (
                        inferred.0,
                        inferred.1,
                        inferred.2,
                        skel_of_lam_binders(binders),
                    )
                }
                _ => {
                    let inferred = elab.infer_statement_expression(cx, expression)?;
                    (inferred.0, inferred.1, inferred.2, None)
                }
            };
            (term, ty, level, skeleton)
        }
    };

    if let Some(annotation) = annotation
        && let Some(dictionary) = elab.dictionary_alias(name, annotation)
    {
        cx.dicts.push(Rc::new(dictionary));
    }
    cx.aliases.push(Rc::new(Alias {
        skel: skeleton,
        name: name.to_string(),
        depth: cx.names.len(),
        term: Rc::new(term),
        ty,
        level,
    }));
    Ok(())
}

fn elaborate_record_let(
    elab: &impl StatementElab,
    cx: &mut Cx,
    fields: &[heather_syntax::RecordPatField],
    expression: &Expr,
    span: Span,
) -> R<()> {
    let (term, record_type, _) = elab.infer_statement_expression(cx, expression)?;
    let Some(record) = elab.record_for_destructuring(cx, &record_type, span) else {
        return err("a `let { … }` pattern needs a record on the right", span);
    };
    let value = Rc::new(term);
    let mut selected = vec![None; record.ctors[0].fields.len()];
    for field in fields {
        let Some(index) = record.field_index(&field.name) else {
            return err(
                format!("`{}` has no field `{}`", record.name, field.name),
                field.span,
            );
        };
        if selected[index].replace(field).is_some() {
            return err(
                format!(
                    "field `{}` appears twice in this record pattern",
                    field.name
                ),
                field.span,
            );
        }
    }

    // A dependent record's declaration order is semantic; written pattern
    // order is presentation only.
    for (index, field) in selected.into_iter().enumerate() {
        let Some(field) = field else { continue };
        let Pat::Var {
            name,
            span: pattern_span,
        } = &field.pat
        else {
            return err(
                "a record `let` field is irrefutable: its right side must be a \
                 name or `_`; use `match` or `if let` for a constructor pattern",
                field.pat.span(),
            );
        };
        if name == "_" {
            continue;
        }
        let (term, ty, level) = elab.project_destructured_field(
            cx,
            &record,
            &record_type,
            Rc::clone(&value),
            index,
            *pattern_span,
        )?;
        cx.aliases.push(Rc::new(Alias {
            skel: skel_of_ty(&record.ctors[0].fields[index].1),
            name: name.clone(),
            depth: cx.names.len(),
            term: Rc::new(term),
            ty,
            level,
        }));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;
    use heather_syntax::TyKind;

    const SPAN: Span = Span { start: 0, end: 1 };

    #[derive(Default)]
    struct Fake {
        lowered: Cell<usize>,
        checked: Cell<usize>,
        harvested: Cell<usize>,
    }

    impl StatementElab for Fake {
        fn lower_let_annotation(&self, _cx: &Cx, annotation: &Ty) -> R<(Type, Level)> {
            assert!(matches!(annotation.kind, TyKind::Nat));
            self.lowered.set(self.lowered.get() + 1);
            Ok((Type::Nat, Level::Zero))
        }

        fn check_let_value(
            &self,
            cx: &Cx,
            expression: &Expr,
            expected: &Type,
            level: &Level,
            _skeleton: Option<&Skel>,
        ) -> R<Term> {
            assert_eq!((expected, level), (&Type::Nat, &Level::Zero));
            let ExprKind::Var(name) = &expression.kind else {
                panic!("the fixture checks an alias reference");
            };
            assert!(cx.aliases.iter().any(|alias| alias.name == *name));
            self.checked.set(self.checked.get() + 1);
            Ok(Term::Zero)
        }

        fn infer_statement_expression(
            &self,
            _cx: &Cx,
            expression: &Expr,
        ) -> R<(Term, Type, Level)> {
            assert!(matches!(expression.kind, ExprKind::Num(_)));
            Ok((Term::Zero, Type::Nat, Level::Zero))
        }

        fn infer_let_lambda(
            &self,
            _cx: &Cx,
            _binders: &[LamBinder],
            _body: &Expr,
        ) -> R<(Term, Type, Level)> {
            self.harvested.set(self.harvested.get() + 1);
            Ok((Term::Zero, Type::Nat, Level::Zero))
        }

        fn dictionary_alias(&self, _name: &str, _annotation: &Ty) -> Option<DictBinder> {
            None
        }

        fn record_for_destructuring(
            &self,
            _cx: &Cx,
            _record_type: &Type,
            _span: Span,
        ) -> Option<Rc<Inductive>> {
            None
        }

        fn project_destructured_field(
            &self,
            _cx: &Cx,
            _record: &Inductive,
            _record_type: &Type,
            _value: Rc<Term>,
            _index: usize,
            _span: Span,
        ) -> R<(Term, Type, Level)> {
            unreachable!("the fixture has no records")
        }
    }

    #[test]
    fn statement_sequencing_and_lambda_harvest_need_no_elaborator() {
        let fake = Fake::default();
        let statements = vec![
            Stmt::Let {
                name: "x".into(),
                ty: None,
                expr: Expr {
                    kind: ExprKind::Num(1),
                    span: SPAN,
                },
                span: SPAN,
            },
            Stmt::Let {
                name: "y".into(),
                ty: Some(Ty {
                    kind: TyKind::Nat,
                    span: SPAN,
                }),
                expr: Expr {
                    kind: ExprKind::Var("x".into()),
                    span: SPAN,
                },
                span: SPAN,
            },
            Stmt::Let {
                name: "f".into(),
                ty: None,
                expr: Expr {
                    kind: ExprKind::Lam {
                        binders: vec![LamBinder {
                            name: "A".into(),
                            ty: Some(Ty {
                                kind: TyKind::Nat,
                                span: SPAN,
                            }),
                            implicit: true,
                            span: SPAN,
                        }],
                        body: Box::new(Expr {
                            kind: ExprKind::Num(0),
                            span: SPAN,
                        }),
                    },
                    span: SPAN,
                },
                span: SPAN,
            },
        ];

        let cx = elaborate(&fake, &Cx::empty(), &statements).unwrap();
        assert_eq!(
            cx.aliases
                .iter()
                .map(|alias| alias.name.as_str())
                .collect::<Vec<_>>(),
            ["x", "y", "f"]
        );
        assert!(cx.aliases[2].skel.is_some());
        assert_eq!(
            (fake.lowered.get(), fake.checked.get(), fake.harvested.get()),
            (1, 1, 1)
        );
    }

    #[test]
    fn program_statements_refuse_meta_let_code_locally() {
        let statement = Stmt::LetCode {
            name: "code".into(),
            expr: Expr {
                kind: ExprKind::Num(0),
                span: SPAN,
            },
            span: SPAN,
        };
        assert!(elaborate(&Fake::default(), &Cx::empty(), &[statement]).is_err());
    }
}
