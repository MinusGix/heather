//! Ordinary block statements and block-expression sequencing.
//!
//! A surface `let` is an elaborator alias, not a kernel binder.  This module
//! owns the consequences of that decision: statements extend a cloned [`Cx`],
//! record destructuring installs projections in declaration order, and a block
//! contributes only the term synthesized or checked for its result.
//!
//! A `have` is the one statement that *is* a kernel binder
//! (docs/have-design.md): the rest of its block elaborates under `x : T` and
//! the block becomes the redex `(λ x: T. rest)(v)`, so the kernel checks `v`
//! once however often `x` is used.
//!
//! **Every written value reaches the kernel.** An alias's value is in the
//! kernel's input only where a use spliced it, and the elaborator does not
//! decide well-typedness itself: it leaves conversions — a `refl`'s two
//! sides, a constructor's field types — to the gate. So a `let` no use
//! spliced (`let p = P(2, refl); 0`) would be accepted however wrong its
//! value. A block therefore ends by wrapping such a value around its result
//! as a redex that discards it, `(λ _: T. λ b: B. b)(v)(rest)`
//! ([`LetValue::discard_around`]); a value some use spliced is already
//! checked there.

use std::sync::Arc as Rc;
use std::sync::atomic::{AtomicBool, Ordering};

use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
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

    /// A local or alias in scope, by name, read without recording a splice
    /// (`Elaborator::resolve_reading`): the right side of a renaming `let`.
    fn read_local(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)>;

    /// `ty` as an emitted annotation slot in `cx` (`Elaborator::annotation_type`,
    /// the one emission chokepoint): the domain of a discarding redex.
    fn annotation(&self, cx: &Cx, ty: &Type) -> Type;

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

/// Extend a clone of `cx` with the aliases introduced by `statements`, up to
/// the first `have`. Returns the extended context, the values those aliases
/// were bound to, and the statements from that `have` on, which are empty
/// when there is none: a `have` scopes over the rest of its block, so only a
/// caller that holds the block's result can elaborate it ([`check_block`],
/// [`infer_block`]). That caller also owns the values: once the result is
/// built, it discards the ones no use spliced around it
/// ([`LetValue::discard_around`]).
pub(crate) fn elaborate<'s>(
    elab: &impl StatementElab,
    cx: &Cx,
    statements: &'s [Stmt],
) -> R<(Cx, Vec<LetValue>, &'s [Stmt])> {
    let mut cx = cx.clone();
    let mut values = Vec::new();
    for (index, statement) in statements.iter().enumerate() {
        match statement {
            Stmt::Let { opaque: true, .. } => return Ok((cx, values, &statements[index..])),
            Stmt::Let { name, ty, expr, .. } => {
                values.extend(elaborate_let(elab, &mut cx, name, ty.as_ref(), expr)?);
            }
            Stmt::LetRecord { fields, expr, span } => {
                values.push(elaborate_record_let(elab, &mut cx, fields, expr, *span)?);
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
    Ok((cx, values, &[]))
}

/// A written `let`'s value (a record `let`'s whole right side), kept until
/// its block is built. Every alias it bound shares `spliced`.
pub(crate) struct LetValue {
    term: Rc<Term>,
    ty: Rc<Type>,
    level: Level,
    spliced: Rc<AtomicBool>,
}

impl LetValue {
    pub(crate) fn new(term: Rc<Term>, ty: Type, level: Level) -> Self {
        LetValue {
            term,
            ty: Rc::new(ty),
            level,
            spliced: Rc::new(AtomicBool::new(false)),
        }
    }

    /// The alias a written `let x = v;` binds at `depth`, sharing this
    /// value's record of being spliced.
    pub(crate) fn alias(&self, name: String, depth: usize, skel: Option<Rc<Skel>>) -> Alias {
        Alias {
            name,
            depth,
            term: Rc::clone(&self.term),
            ty: (*self.ty).clone(),
            level: self.level.clone(),
            skel,
            spliced: Some(Rc::clone(&self.spliced)),
            shifted: Default::default(),
        }
    }

    /// `body`, of `body_type` at `body_level` in `cx`, the context the values
    /// were bound in, with every value no use spliced discarded around it as
    /// `(λ _: T. λ b: B. b)(v)(body)` — outermost first, so the redexes read
    /// in the order the `let`s were written. The block's type is unchanged:
    /// the discarding function is the identity on `B` once `v` is given.
    ///
    /// Each value, its type and `body` stay at the block's own depth: only
    /// `B` goes under the discarding binder, once for the whole block
    /// ([`Discard`]). Wrapping as `(λ _: T. body)(v)` instead put the rest
    /// of the block one binder deeper per value, so `k` unused proofs about
    /// a shared chain shifted the body `k` times and handed the gate the
    /// chain at `k` depths (`issues/discarded-let-values-nest-binders.md`).
    pub(crate) fn discard_around(
        elab: &impl StatementElab,
        cx: &Cx,
        values: Vec<LetValue>,
        body: Term,
        body_type: &Type,
        body_level: &Level,
    ) -> Term {
        let unused: Vec<LetValue> = values
            .into_iter()
            .filter(|value| !value.spliced.load(Ordering::Relaxed))
            .collect();
        if unused.is_empty() {
            return body;
        }
        let discard = Discard::new(elab, cx, body_type, body_level);
        unused.into_iter().rev().fold(body, |body, value| discard.around(elab, cx, value, body))
    }
}

/// What every discarding redex of one block shares: the block's type `B`
/// and the identity on it under the discarded value's binder, built once so
/// that each redex holds the same nodes.
struct Discard {
    level: Level,
    /// `B`, as an annotation slot.
    ty: Rc<Type>,
    /// `B` under one binder: the codomain of `app(…; b: B. B↑)`.
    ty_under: Rc<Type>,
    /// `λ b: B↑. b`, under the discarded value's binder.
    identity: Rc<Term>,
    /// Its type there, `Π(b: B↑). B↑↑`.
    identity_ty: Rc<Type>,
}

impl Discard {
    fn new(elab: &impl StatementElab, cx: &Cx, body_type: &Type, body_level: &Level) -> Self {
        let ty = elab.annotation(cx, body_type);
        let ty_under = Rc::new(ty.shift_local(1));
        let identity_ty = Rc::new(Type::Pi {
            dom_level: body_level.clone(),
            cod_level: body_level.clone(),
            dom: Rc::clone(&ty_under),
            cod: Rc::new(ty.shift_local(2)),
        });
        let identity = Rc::new(Term::Lam {
            dom_level: body_level.clone(),
            cod_level: body_level.clone(),
            dom: Rc::clone(&ty_under),
            body: Rc::new(Term::Var(LocalVar(0))),
        });
        Discard { level: body_level.clone(), ty: Rc::new(ty), ty_under, identity, identity_ty }
    }

    /// `app(app(λ(_: T). λ(b: B↑). b; v); body)`, both applications in the
    /// kernel's annotated form ([`HaveValue::redex`]). `Π(b: B↑). B↑↑` has
    /// level `l_B ⊔ l_B`, which is `l_B`.
    fn around(&self, elab: &impl StatementElab, cx: &Cx, value: LetValue, body: Term) -> Term {
        let keep = HaveValue {
            term: value.term,
            ty: Rc::new(elab.annotation(cx, &value.ty)),
            level: value.level,
        }
        .redex_shared(Rc::clone(&self.identity), Rc::clone(&self.identity_ty), self.level.clone());
        Term::App {
            fun: Rc::new(keep),
            dom_level: self.level.clone(),
            cod_level: self.level.clone(),
            dom: Rc::clone(&self.ty),
            cod: Rc::clone(&self.ty_under),
            arg: Rc::new(body),
        }
    }
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
    check_statements(
        elab,
        cx,
        &block.stmts,
        &block.result,
        expected,
        level,
        hint,
        skeleton,
        capture_slots,
    )
}

/// [`check_block`] over a suffix of a block's statements. At a `have` the
/// rest is checked under the new binder against the expected type weakened
/// past it, which keeps the block checking-transparent
/// (docs/have-design.md §4).
#[allow(clippy::too_many_arguments)]
fn check_statements(
    elab: &impl BlockCheckingElab,
    cx: &Cx,
    statements: &[Stmt],
    result: &Expr,
    expected: &Type,
    level: &Level,
    hint: Option<(&str, &str)>,
    skeleton: Option<&Skel>,
    capture_slots: bool,
) -> R<Term> {
    let (cx, values, rest) = elaborate(elab, cx, statements)?;
    let body = match rest.split_first() {
        None => elab.check_block_result(
            &cx,
            result,
            expected,
            level,
            hint,
            skeleton,
            capture_slots,
        )?,
        Some((have, rest)) => {
            let (inner, value) = elaborate_have(elab, &cx, have)?;
            let body_type = expected.shift_local(1);
            let body = check_statements(
                elab,
                &inner,
                rest,
                result,
                &body_type,
                level,
                hint,
                skeleton,
                capture_slots,
            )?;
            value.redex(body, body_type, level.clone())
        }
    };
    Ok(LetValue::discard_around(elab, &cx, values, body, expected, level))
}

pub(crate) fn infer_block(
    elab: &impl StatementElab,
    cx: &Cx,
    block: &Block,
) -> R<(Term, Type, Level)> {
    infer_statements(elab, cx, &block.stmts, &block.result)
}

/// [`infer_block`] over a suffix of a block's statements. At a `have` the
/// rest is inferred under the new binder, and the block's type is the rest's
/// with the value substituted back in (docs/have-design.md §4).
fn infer_statements(
    elab: &impl StatementElab,
    cx: &Cx,
    statements: &[Stmt],
    result: &Expr,
) -> R<(Term, Type, Level)> {
    let (cx, values, rest) = elaborate(elab, cx, statements)?;
    let (body, ty, level) = match rest.split_first() {
        None => elab.infer_statement_expression(&cx, result)?,
        Some((have, rest)) => {
            let (inner, value) = elaborate_have(elab, &cx, have)?;
            let (body, body_type, body_level) = infer_statements(elab, &inner, rest, result)?;
            let ty = body_type
                .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&value.term)));
            (value.redex(body, body_type, body_level.clone()), ty, body_level)
        }
    };
    Ok((LetValue::discard_around(elab, &cx, values, body, &ty, &level), ty, level))
}

/// A `have`'s elaborated value, ready to be applied to the rest of its block.
struct HaveValue {
    term: Rc<Term>,
    ty: Rc<Type>,
    level: Level,
}

impl HaveValue {
    /// `app(λ(x: T). body; l_T, l_B; x: T. B; v)` — the kernel's annotated
    /// application, not `AppAt`: the unannotated form infers its function,
    /// and a λ whose body only checks does not infer.
    fn redex(self, body: Term, body_type: Type, body_level: Level) -> Term {
        self.redex_shared(Rc::new(body), Rc::new(body_type), body_level)
    }

    /// [`Self::redex`] over a body and type already shared.
    fn redex_shared(self, body: Rc<Term>, body_type: Rc<Type>, body_level: Level) -> Term {
        Term::App {
            fun: Rc::new(Term::Lam {
                dom_level: self.level.clone(),
                cod_level: body_level.clone(),
                dom: Rc::clone(&self.ty),
                body,
            }),
            dom_level: self.level,
            cod_level: body_level,
            dom: self.ty,
            cod: body_type,
            arg: self.term,
        }
    }
}

/// Elaborate `have x = e;` in `cx`: its value exactly as a `let`'s, and the
/// context the rest of the block sees, where `x` is a binder and not an
/// alias.
fn elaborate_have(elab: &impl StatementElab, cx: &Cx, have: &Stmt) -> R<(Cx, HaveValue)> {
    let Stmt::Let { name, ty: annotation, expr, opaque: true, .. } = have else {
        unreachable!("`elaborate` stops only at a `have`")
    };
    let (term, ty, level, skeleton) = let_value(elab, cx, annotation.as_ref(), expr)?;
    let mut inner = cx.clone();
    if let Some(annotation) = annotation
        && let Some(dictionary) = elab.dictionary_alias(name, annotation)
    {
        inner.dicts.push(Rc::new(dictionary));
    }
    inner.push_skel(name.clone(), ty.clone(), level.clone(), skeleton);
    Ok((
        inner,
        HaveValue {
            term: Rc::new(term),
            ty: Rc::new(ty),
            level,
        },
    ))
}

fn elaborate_let(
    elab: &impl StatementElab,
    cx: &mut Cx,
    name: &str,
    annotation: Option<&Ty>,
    expression: &Expr,
) -> R<Option<LetValue>> {
    if annotation.is_none()
        && let Some(splice) = renamed(cx, expression)
    {
        // `let y = x;`, which `match` desugaring writes for every pattern
        // variable: a local is well-typed by construction and an alias's
        // value is its own `let`'s, so there is nothing of `y`'s to check.
        // A use of `y` is a use of `x`'s value, so it records `x`'s splice.
        let ExprKind::Var(name_read) = &expression.kind else { unreachable!() };
        let (term, ty, level) = elab.read_local(cx, name_read, expression.span)?;
        cx.aliases.push(Rc::new(Alias {
            skel: None,
            name: name.to_string(),
            depth: cx.names.len(),
            term: Rc::new(term),
            ty,
            level,
            spliced: splice,
            shifted: Default::default(),
        }));
        return Ok(None);
    }
    let (term, ty, level, skeleton) = let_value(elab, cx, annotation, expression)?;
    if let Some(annotation) = annotation
        && let Some(dictionary) = elab.dictionary_alias(name, annotation)
    {
        cx.dicts.push(Rc::new(dictionary));
    }
    let value = LetValue::new(Rc::new(term), ty, level);
    cx.aliases.push(Rc::new(value.alias(name.to_string(), cx.names.len(), skeleton)));
    Ok(Some(value))
}

/// When `expression` is a bare name of a local or an alias in scope, the
/// splice record a use of it should set: the alias's own, or none for a
/// local. Shadowing as `resolve` decides it: an alias bound after a local of
/// the same name hides it.
fn renamed(cx: &Cx, expression: &Expr) -> Option<Option<Rc<AtomicBool>>> {
    let ExprKind::Var(name) = &expression.kind else { return None };
    let local = cx.names.lookup(name);
    let alias = cx.aliases.iter_inner().find(|a| a.name == *name);
    match (local, alias) {
        (Some(pos), Some(a)) if a.depth <= pos => Some(None),
        (_, Some(a)) => Some(a.spliced.clone()),
        (Some(_), None) => Some(None),
        (None, None) => None,
    }
}

/// A `let` or `have` right-hand side: checked against its annotation, or
/// inferred, with a λ's written marks harvested into the skeleton.
fn let_value(
    elab: &impl StatementElab,
    cx: &Cx,
    annotation: Option<&Ty>,
    expression: &Expr,
) -> R<(Term, Type, Level, Option<Rc<Skel>>)> {
    Ok(match annotation {
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
    })
}

fn elaborate_record_let(
    elab: &impl StatementElab,
    cx: &mut Cx,
    fields: &[heather_syntax::RecordPatField],
    expression: &Expr,
    span: Span,
) -> R<LetValue> {
    let (term, record_type, record_level) = elab.infer_statement_expression(cx, expression)?;
    let Some(record) = elab.record_for_destructuring(cx, &record_type, span) else {
        return err("a `let { … }` pattern needs a record on the right", span);
    };
    let whole = LetValue::new(Rc::new(term), record_type.clone(), record_level);
    let value = Rc::clone(&whole.term);
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
        // A use of any field splices a projection of the whole value.
        cx.aliases.push(Rc::new(Alias {
            spliced: Some(Rc::clone(&whole.spliced)),
            skel: skel_of_ty(&record.ctors[0].fields[index].1),
            name: name.clone(),
            depth: cx.names.len(),
            term: Rc::new(term),
            ty,
            level,
            shifted: Default::default(),
        }));
    }
    Ok(whole)
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
            assert!(cx.aliases.iter_inner().any(|alias| alias.name == *name));
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

        fn read_local(&self, _cx: &Cx, _name: &str, _span: Span) -> R<(Term, Type, Level)> {
            Ok((Term::Zero, Type::Nat, Level::Zero))
        }

        fn annotation(&self, _cx: &Cx, ty: &Type) -> Type {
            ty.clone()
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
                    kind: ExprKind::Num(1u64.into()),
                    span: SPAN,
                },
                span: SPAN,
                opaque: false,
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
                opaque: false,
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
                            kind: ExprKind::Num(0u64.into()),
                            span: SPAN,
                        }),
                    },
                    span: SPAN,
                },
                span: SPAN,
                opaque: false,
            },
        ];

        let (cx, _, rest) = elaborate(&fake, &Cx::empty(), &statements).unwrap();
        assert!(rest.is_empty());
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

    /// The alias pass stops at a `have` and hands back the statements from it
    /// on, since only the caller holding the block's result can scope the
    /// binder over the rest (docs/have-design.md §5).
    #[test]
    fn the_alias_pass_stops_at_the_first_have() {
        let number = |name: &str, opaque| Stmt::Let {
            name: name.into(),
            ty: None,
            expr: Expr {
                kind: ExprKind::Num(1u64.into()),
                span: SPAN,
            },
            span: SPAN,
            opaque,
        };
        let statements = vec![number("a", false), number("h", true), number("b", false)];
        let (cx, _, rest) = elaborate(&Fake::default(), &Cx::empty(), &statements).unwrap();
        assert_eq!(cx.aliases.len(), 1);
        assert_eq!(rest.len(), 2);
        assert!(matches!(&rest[0], Stmt::Let { name, opaque: true, .. } if name == "h"));
    }

    #[test]
    fn program_statements_refuse_meta_let_code_locally() {
        let statement = Stmt::LetCode {
            name: "code".into(),
            expr: Expr {
                kind: ExprKind::Num(0u64.into()),
                span: SPAN,
            },
            span: SPAN,
        };
        assert!(elaborate(&Fake::default(), &Cx::empty(), &[statement]).is_err());
    }
}
