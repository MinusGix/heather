//! Scoped proof worlds (`within W { … }` and `within W for x { … }`):
//! lowering from an inside representation into an outside Heather proof
//! (docs/language/proof-worlds-design.md).
//!
//! No new kernel form and no new AST variant:
//! - Monadic form `within W { body }` wraps tail leaves of `body` in
//!   `Pointed::ret`, runs [`crate::try_lower::binds_in_block`], and emits
//!   `__within(W, lowered)`.
//! - Pointwise form `within W for x { body }` partitions outer vs inner
//!   bindings, lowers `let u <- e;` statements into `W::use(e, … W::always(…))`,
//!   and emits `__within_for(W, lowered)` inside any outer `let`s.

use std::collections::BTreeSet;

use crate::ast::*;
use crate::parser::ParseError;
use crate::try_lower::{BIND_SEQ, POINTED_RET, has_bind_marker, unwrap_bind_marker};

type R<T> = Result<T, ParseError>;

/// Sentinel call head for `within W { … }`.
pub const WITHIN: &str = "__within";

/// Sentinel call head for `within W for x { … }`.
pub const WITHIN_FOR: &str = "__within_for";

fn fail<T>(span: Span, msg: impl Into<String>) -> R<T> {
    Err(ParseError { span, msg: msg.into() })
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

fn call(name: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(var(name, span)),
            args,
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

/// Lower `within world [for binder] { block }` into an ordinary AST expression.
pub(crate) fn lower(
    world: Expr,
    binder: Option<LamBinder>,
    block: Block,
    start: Span,
    next: &mut usize,
) -> R<Expr> {
    if !block.ons.is_empty() {
        return fail(
            block.ons[0].span,
            "a `within` block cannot contain declaration-scoped `on` discharges",
        );
    }
    match binder {
        None => lower_monadic(world, block, start, next),
        Some(index_binder) => lower_pointwise(world, index_binder, block, start, next),
    }
}

/// Wrap tail leaves of a monadic `within` block in `Pointed::ret`, descending
/// through blocks, `match`/`if` arms, and inner blocks that have already
/// lowered their own `let <-` statements into `Bind::seq`.
fn wrap_tail_leaves(e: Expr) -> Expr {
    let span = e.span;
    // A bare `(<- m)` in tail position is already in `M(G)`: unwrap directly.
    if let Some(inner) = unwrap_bind_marker(&e) {
        return inner.clone();
    }
    match e.kind {
        ExprKind::Block(mut b) => {
            b.result = Box::new(wrap_tail_leaves(*b.result));
            Expr { kind: ExprKind::Block(b), span }
        }
        ExprKind::Match { form, generated, scrut, eqbind, motive, mut arms } => {
            for arm in &mut arms {
                let arm_span = arm.body.span;
                let body = std::mem::replace(
                    &mut arm.body,
                    Expr { kind: ExprKind::AutoRefl, span: arm_span },
                );
                arm.body = wrap_tail_leaves(body);
            }
            Expr { kind: ExprKind::Match { form, generated, scrut, eqbind, motive, arms }, span }
        }
        ExprKind::App { head, mut args, named, explicit, goal_oriented } => {
            // Already wrapped in `Pointed::ret`: keep as-is.
            if named.is_empty()
                && !explicit
                && !goal_oriented
                && args.len() == 1
                && matches!(&head.kind, ExprKind::Var(n) if n == POINTED_RET)
            {
                return Expr {
                    kind: ExprKind::App { head, args, named, explicit, goal_oriented },
                    span,
                };
            }
            // Inner block lowered to `Bind::seq(m, λ x => body)`: wrap continuation leaves.
            if named.is_empty()
                && !explicit
                && !goal_oriented
                && args.len() == 2
                && matches!(&head.kind, ExprKind::Var(n) if n == BIND_SEQ)
                && matches!(&args[1].kind, ExprKind::Lam { .. })
            {
                let lam = std::mem::replace(
                    &mut args[1].kind,
                    ExprKind::AutoRefl,
                );
                if let ExprKind::Lam { binders, body } = lam {
                    let wrapped = wrap_tail_leaves(*body);
                    args[1].kind = ExprKind::Lam { binders, body: Box::new(wrapped) };
                }
                return Expr {
                    kind: ExprKind::App { head, args, named, explicit, goal_oriented },
                    span,
                };
            }
            let inner = Expr {
                kind: ExprKind::App { head, args, named, explicit, goal_oriented },
                span,
            };
            call(POINTED_RET, vec![inner], span)
        }
        other => call(POINTED_RET, vec![Expr { kind: other, span }], span),
    }
}

fn lower_monadic(world: Expr, mut block: Block, start: Span, next: &mut usize) -> R<Expr> {
    let block_span = block.span;
    let wrapped_result = wrap_tail_leaves(*block.result);
    block.result = Box::new(wrapped_result);
    let lowered = crate::try_lower::binds_in_block(block, next)?;
    let span = start.join(block_span);
    Ok(call(
        WITHIN,
        vec![world, Expr { kind: ExprKind::Block(Box::new(lowered)), span: block_span }],
        span,
    ))
}

enum BindTarget {
    Name { name: String, ty: Option<Ty>, span: Span },
    Record { fields: Vec<RecordPatField>, span: Span },
}

fn collect_pat_names(pat: &Pat, out: &mut Vec<String>) {
    match pat {
        Pat::Var { name, .. } => {
            if name != "_" {
                out.push(name.clone());
            }
        }
        Pat::Ctor { args, .. } => {
            for a in args {
                collect_pat_names(a, out);
            }
        }
        Pat::Named { pat, .. } => collect_pat_names(pat, out),
    }
}

fn ty_mentions_any(t: &Ty, vars: &BTreeSet<String>) -> bool {
    if vars.is_empty() {
        return false;
    }
    match &t.kind {
        TyKind::Named { name, args } => {
            vars.contains(name) || args.iter().any(|a| ty_mentions_any(a, vars))
        }
        TyKind::Fn { binder, dom, cod, .. } => {
            if ty_mentions_any(dom, vars) {
                return true;
            }
            if let Some(b) = binder
                && vars.contains(b)
            {
                let mut narrowed = vars.clone();
                narrowed.remove(b);
                ty_mentions_any(cod, &narrowed)
            } else {
                ty_mentions_any(cod, vars)
            }
        }
        TyKind::Eq(a, b) => mentions_any(a, vars) || mentions_any(b, vars),
        TyKind::OfExpr(e) | TyKind::Fin(e) | TyKind::TypeOf(e) => mentions_any(e, vars),
        TyKind::Vec { elem, len } => ty_mentions_any(elem, vars) || mentions_any(len, vars),
        TyKind::Squash(inner) | TyKind::Code { ty: inner, .. } => ty_mentions_any(inner, vars),
        _ => false,
    }
}

fn mentions_any(e: &Expr, vars: &BTreeSet<String>) -> bool {
    if vars.is_empty() {
        return false;
    }
    match &e.kind {
        ExprKind::Var(name) => vars.contains(name),
        ExprKind::App { head, args, named, .. } => {
            mentions_any(head, vars)
                || args.iter().any(|a| mentions_any(a, vars))
                || named.iter().any(|a| mentions_any(&a.expr, vars))
        }
        ExprKind::TyApp { head, args } => {
            mentions_any(head, vars) || args.iter().any(|t| ty_mentions_any(t, vars))
        }
        ExprKind::Lam { binders, body } => {
            let mut active = vars.clone();
            for b in binders {
                if let Some(t) = &b.ty
                    && ty_mentions_any(t, &active)
                {
                    return true;
                }
                active.remove(&b.name);
            }
            mentions_any(body, &active)
        }
        ExprKind::CollectionLit(xs) => xs.iter().any(|x| mentions_any(x, vars)),
        ExprKind::Eq(a, b) | ExprKind::Index { recv: a, idx: b } => {
            mentions_any(a, vars) || mentions_any(b, vars)
        }
        ExprKind::TyLit(t) => ty_mentions_any(t, vars),
        ExprKind::Match { scrut, motive, arms, eqbind, .. } => {
            if mentions_any(scrut, vars)
                || motive.as_ref().is_some_and(|m| mentions_any(m, vars))
            {
                return true;
            }
            for arm in arms {
                let mut active = vars.clone();
                if let Some(eq) = eqbind {
                    active.remove(eq);
                }
                let mut bound = Vec::new();
                for p in &arm.binders {
                    collect_pat_names(p, &mut bound);
                }
                for n in bound {
                    active.remove(&n);
                }
                if mentions_any(&arm.body, &active) {
                    return true;
                }
            }
            false
        }
        ExprKind::MatchCode { scrut, motive, arms } => {
            if mentions_any(scrut, vars) || ty_mentions_any(motive, vars) {
                return true;
            }
            for arm in arms {
                let mut active = vars.clone();
                let mut bound = Vec::new();
                for p in &arm.binders {
                    collect_pat_names(p, &mut bound);
                }
                for n in bound {
                    active.remove(&n);
                }
                if mentions_any(&arm.body, &active) {
                    return true;
                }
            }
            false
        }
        ExprKind::Dot { recv, tyargs, args, named, .. } => {
            mentions_any(recv, vars)
                || tyargs.iter().any(|t| ty_mentions_any(t, vars))
                || args.iter().flatten().any(|a| mentions_any(a, vars))
                || named.iter().any(|a| mentions_any(&a.expr, vars))
        }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            tyargs.iter().any(|t| ty_mentions_any(t, vars))
                || fields.iter().any(|f| mentions_any(&f.expr, vars))
        }
        ExprKind::Block(b) => {
            let mut active = vars.clone();
            for s in &b.stmts {
                match s {
                    Stmt::Let { name, ty, expr, .. } => {
                        if ty.as_ref().is_some_and(|t| ty_mentions_any(t, &active))
                            || mentions_any(expr, &active)
                        {
                            return true;
                        }
                        active.remove(name);
                    }
                    Stmt::LetRecord { fields, expr, .. } => {
                        if mentions_any(expr, &active) {
                            return true;
                        }
                        let mut bound = Vec::new();
                        for f in fields {
                            collect_pat_names(&f.pat, &mut bound);
                        }
                        for n in bound {
                            active.remove(&n);
                        }
                    }
                    Stmt::LetCode { name, expr, .. } => {
                        if mentions_any(expr, &active) {
                            return true;
                        }
                        active.remove(name);
                    }
                }
            }
            if mentions_any(&b.result, &active) {
                return true;
            }
            b.ons.iter().any(|o| {
                mentions_any(&o.expr, &active)
                    || matches!(&o.target, OnTarget::Stmt(t) if ty_mentions_any(t, &active))
            })
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => mentions_any(x, vars),
        ExprKind::J { proof, motive, case } => {
            mentions_any(proof, vars) || mentions_any(motive, vars) || mentions_any(case, vars)
        }
        _ => false,
    }
}

fn dot_field(recv: Expr, field: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Dot {
            recv: Box::new(recv),
            name: field.to_string(),
            tyargs: Vec::new(),
            args: None,
            named: Vec::new(),
        },
        span,
    }
}

/// Projection of the `i`-th element out of a left-nested `And` pair of `k`
/// elements (`k >= 2`): `((e_0 ∧ e_1) ∧ …) ∧ e_{k-1}`.
fn pair_proj(root: &str, i: usize, k: usize, span: Span) -> Expr {
    let mut e = var(root, span);
    let lefts = if i == 0 { k - 1 } else { k - 1 - i };
    for _ in 0..lefts {
        e = dot_field(e, "left", span);
    }
    if i > 0 {
        e = dot_field(e, "right", span);
    }
    e
}

fn lower_pointwise(
    world: Expr,
    index_binder: LamBinder,
    block: Block,
    start: Span,
    next: &mut usize,
) -> R<Expr> {
    let ExprKind::Var(world_name) = &world.kind else {
        return fail(
            world.span,
            "a pointwise `within W for x { … }` needs a world name `W` (such as `Eventually`)",
        );
    };
    let world_name = world_name.clone();
    let block_span = block.span;
    let span = start.join(block_span);

    let mut inner_vars: BTreeSet<String> = BTreeSet::new();
    if index_binder.name != "_" {
        inner_vars.insert(index_binder.name.clone());
    }

    let mut outer_stmts: Vec<Stmt> = Vec::new();
    let mut inner_stmts: Vec<Stmt> = Vec::new();
    let mut binds: Vec<(BindTarget, Expr)> = Vec::new();

    for stmt in block.stmts {
        match stmt {
            Stmt::Let { name, ty, expr, span: sspan, opaque } => {
                if !opaque
                    && let Some(rhs) = unwrap_bind_marker(&expr)
                {
                    if has_bind_marker(rhs) {
                        return fail(
                            rhs.span,
                            "nested `(<- …)` is not supported inside a pointwise `within … for` block; bind each fact with `let h <- e;`",
                        );
                    }
                    if mentions_any(rhs, &inner_vars) {
                        return fail(
                            rhs.span,
                            format!(
                                "a bound fact in `within {world_name} for {}` cannot depend on `{}` or on an earlier bound fact",
                                index_binder.name, index_binder.name
                            ),
                        );
                    }
                    if name != "_" {
                        inner_vars.insert(name.clone());
                    }
                    binds.push((BindTarget::Name { name, ty, span: sspan }, rhs.clone()));
                } else {
                    if has_bind_marker(&expr) {
                        return fail(
                            expr.span,
                            "nested `(<- …)` is not supported inside a pointwise `within … for` block; bind it with `let h <- e;`",
                        );
                    }
                    let is_inner = inner_vars.contains(&name)
                        || mentions_any(&expr, &inner_vars)
                        || ty.as_ref().is_some_and(|t| ty_mentions_any(t, &inner_vars));
                    if is_inner {
                        if name != "_" {
                            inner_vars.insert(name.clone());
                        }
                        inner_stmts.push(Stmt::Let { name, ty, expr, span: sspan, opaque });
                    } else {
                        outer_stmts.push(Stmt::Let { name, ty, expr, span: sspan, opaque });
                    }
                }
            }
            Stmt::LetRecord { fields, expr, span: sspan } => {
                let mut bound = Vec::new();
                for f in &fields {
                    collect_pat_names(&f.pat, &mut bound);
                }
                if let Some(rhs) = unwrap_bind_marker(&expr) {
                    if has_bind_marker(rhs) {
                        return fail(
                            rhs.span,
                            "nested `(<- …)` is not supported inside a pointwise `within … for` block; bind each fact with `let h <- e;`",
                        );
                    }
                    if mentions_any(rhs, &inner_vars) {
                        return fail(
                            rhs.span,
                            format!(
                                "a bound fact in `within {world_name} for {}` cannot depend on `{}` or on an earlier bound fact",
                                index_binder.name, index_binder.name
                            ),
                        );
                    }
                    for n in bound {
                        inner_vars.insert(n);
                    }
                    binds.push((BindTarget::Record { fields, span: sspan }, rhs.clone()));
                } else {
                    if has_bind_marker(&expr) {
                        return fail(
                            expr.span,
                            "nested `(<- …)` is not supported inside a pointwise `within … for` block; bind it with `let h <- e;`",
                        );
                    }
                    let is_inner = mentions_any(&expr, &inner_vars)
                        || bound.iter().any(|n| inner_vars.contains(n));
                    if is_inner {
                        for n in bound {
                            inner_vars.insert(n);
                        }
                        inner_stmts.push(Stmt::LetRecord { fields, expr, span: sspan });
                    } else {
                        outer_stmts.push(Stmt::LetRecord { fields, expr, span: sspan });
                    }
                }
            }
            Stmt::LetCode { name, expr, span: sspan } => {
                if has_bind_marker(&expr) {
                    return fail(
                        expr.span,
                        "nested `(<- …)` is not supported inside a pointwise `within … for` block",
                    );
                }
                if inner_vars.contains(&name) || mentions_any(&expr, &inner_vars) {
                    if name != "_" {
                        inner_vars.insert(name.clone());
                    }
                    inner_stmts.push(Stmt::LetCode { name, expr, span: sspan });
                } else {
                    outer_stmts.push(Stmt::LetCode { name, expr, span: sspan });
                }
            }
        }
    }

    if has_bind_marker(&block.result) {
        return fail(
            block.result.span,
            "nested `(<- …)` is not supported inside a pointwise `within … for` block; bind it with `let h <- e;`",
        );
    }

    let k = binds.len();
    let wrapped = if k == 0 {
        let inner_body = if inner_stmts.is_empty() {
            *block.result
        } else {
            Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts: inner_stmts,
                    result: block.result,
                    ons: Vec::new(),
                    span: block_span,
                })),
                span: block_span,
            }
        };
        let lam = Expr {
            kind: ExprKind::Lam { binders: vec![index_binder], body: Box::new(inner_body) },
            span: block_span,
        };
        call(WITHIN_FOR, vec![world, lam], span)
    } else if k == 1 {
        let (target, rhs) = binds.into_iter().next().expect("k == 1");
        let mut lam_binders = vec![index_binder];
        let mut prelude_inner_stmts = Vec::new();
        match target {
            BindTarget::Name { name, ty, span: bspan } => {
                lam_binders.push(LamBinder { name, ty, implicit: false, span: bspan });
            }
            BindTarget::Record { fields, span: bspan } => {
                let n = *next;
                *next += 1;
                let slot = format!("#wrec{n}");
                lam_binders.push(LamBinder {
                    name: slot.clone(),
                    ty: None,
                    implicit: false,
                    span: bspan,
                });
                prelude_inner_stmts.push(Stmt::LetRecord {
                    fields,
                    expr: var(&slot, bspan),
                    span: bspan,
                });
            }
        }
        prelude_inner_stmts.append(&mut inner_stmts);
        let inner_body = if prelude_inner_stmts.is_empty() {
            *block.result
        } else {
            Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts: prelude_inner_stmts,
                    result: block.result,
                    ons: Vec::new(),
                    span: block_span,
                })),
                span: block_span,
            }
        };
        let lam = Expr {
            kind: ExprKind::Lam { binders: lam_binders, body: Box::new(inner_body) },
            span: block_span,
        };
        call(WITHIN_FOR, vec![world, rhs, lam], span)
    } else {
        // Combine all `k >= 2` bound facts bottom-up with `W::both` so `I`, `le`
        // and the combined predicate infer completely before the body lambda is
        // checked (docs/language/proof-worlds-design.md §3).
        let n = *next;
        *next += 1;
        let tuple_slot = format!("#wboth{n}");
        let mut prelude_inner_stmts = Vec::new();
        let mut rhs_iter = binds.into_iter().enumerate();
        let (first_i, (first_target, first_rhs)) = rhs_iter.next().expect("k >= 2");
        let mut combined = first_rhs;
        let mut targets = vec![(first_i, first_target)];
        let both_name = format!("{world_name}::both");
        for (i, (target, rhs)) in rhs_iter {
            let cspan = combined.span.join(rhs.span);
            combined = call(&both_name, vec![combined, rhs], cspan);
            targets.push((i, target));
        }
        for (i, target) in targets {
            match target {
                BindTarget::Name { name, ty, span: bspan } => {
                    prelude_inner_stmts.push(Stmt::Let {
                        name,
                        ty,
                        expr: pair_proj(&tuple_slot, i, k, bspan),
                        span: bspan,
                        opaque: false,
                    });
                }
                BindTarget::Record { fields, span: bspan } => {
                    prelude_inner_stmts.push(Stmt::LetRecord {
                        fields,
                        expr: pair_proj(&tuple_slot, i, k, bspan),
                        span: bspan,
                    });
                }
            }
        }
        prelude_inner_stmts.append(&mut inner_stmts);
        let inner_body = Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts: prelude_inner_stmts,
                result: block.result,
                ons: Vec::new(),
                span: block_span,
            })),
            span: block_span,
        };
        let lam = Expr {
            kind: ExprKind::Lam {
                binders: vec![
                    index_binder,
                    LamBinder { name: tuple_slot, ty: None, implicit: false, span: block_span },
                ],
                body: Box::new(inner_body),
            },
            span: block_span,
        };
        call(WITHIN_FOR, vec![world, combined, lam], span)
    };

    if outer_stmts.is_empty() {
        Ok(wrapped)
    } else {
        Ok(Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts: outer_stmts,
                result: Box::new(wrapped),
                ons: Vec::new(),
                span,
            })),
            span,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::parse_file;

    #[test]
    fn parses_monadic_and_pointwise_within() {
        let src = r#"
theorem a(): Nat { within Dne { let x <- e; x } }
theorem b(): Nat { within Eventually for n { let u <- p; let v <- q; f(n, u, v) } }
fn keep(within: Nat) -> Nat { within + 1 }
"#;
        parse_file(src).expect("valid `within` forms should parse");
    }

    #[test]
    fn refuses_pointwise_bind_depending_on_index() {
        let src = r#"
theorem bad(): Nat {
    within Eventually for n {
        let h <- Eventually::at_least(n);
        h
    }
}
"#;
        let err = parse_file(src).expect_err("bind depending on index should fail");
        assert!(err.msg.contains("cannot depend on `n`"), "got: {}", err.msg);
    }

    #[test]
    fn refuses_pointwise_bind_depending_on_earlier_bind() {
        let src = r#"
theorem bad(): Nat {
    within Eventually for n {
        let u <- p;
        let v <- f(u);
        v
    }
}
"#;
        let err = parse_file(src).expect_err("bind depending on earlier bound fact should fail");
        assert!(err.msg.contains("cannot depend on `n`"), "got: {}", err.msg);
    }
}
