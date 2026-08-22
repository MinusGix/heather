//! Registered source lints.
//!
//! A lint is identified here, run over the written AST after its owning item
//! has elaborated successfully, and emitted through the ordinary warning
//! channel. Keeping the registry separate from elaboration is what lets a
//! source-style rule be added without burying another condition in a typing
//! path. Semantic lints may still be raised where their analysis lives, but
//! use the same [`Lint`] identity.

use heather_syntax::{Block, Decl, Expr, ExprKind, Item, Stmt, Ty, TyKind};

/// Stable identity of a non-fatal lint diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Lint {
    /// A written pattern arm has no constructor cases left to reach it.
    UnreachableMatchArm,
    /// `λ x h => (match x as … { … })(h)` can usually put the match in
    /// checking position by moving `h` into its result.
    MatchFunctionApplication,
}

impl Lint {
    /// Stable kebab-case name for diagnostics, tests, and future allow/deny
    /// configuration. Adding configuration does not have to parse messages.
    pub fn name(self) -> &'static str {
        match self {
            Self::UnreachableMatchArm => "unreachable-match-arm",
            Self::MatchFunctionApplication => "match-function-application",
        }
    }
}

pub(crate) struct Finding {
    pub lint: Lint,
    pub msg: String,
    pub span: heather_syntax::Span,
}

type ExprLint = fn(&Expr, &mut Vec<Finding>);

/// The registry. A source-expression lint is one function and one row; the
/// shared total walker supplies nesting, item ownership, and deterministic
/// source order.
const EXPR_LINTS: &[ExprLint] = &[match_function_application];

pub(crate) fn check_item(item: &Item) -> Vec<Finding> {
    let mut out = Vec::new();
    match item {
        Item::Decl(d) => decl(d, &mut out),
        // The first source-lint customer is a declaration-body style rule.
        // The walker is deliberately item-scoped so the other item forms can
        // add their surface-bearing fields when a lint has a customer there.
        Item::Inductive(_)
        | Item::Class(_)
        | Item::Instance(_)
        | Item::Designation(_)
        | Item::Datarepr(_)
        | Item::Impl(_)
        | Item::Import(_) => {}
    }
    out
}

fn decl(d: &Decl, out: &mut Vec<Finding>) {
    d.params.iter().for_each(|p| ty(&p.ty, out));
    ty(&d.result, out);
    block(&d.body, out);
}

fn block(b: &Block, out: &mut Vec<Finding>) {
    for s in &b.stmts {
        match s {
            Stmt::Let { ty: ann, expr: value, .. } => {
                if let Some(t) = ann {
                    ty(t, out);
                }
                expr(value, out);
            }
            Stmt::LetRecord { expr: value, .. } | Stmt::LetCode { expr: value, .. } => {
                expr(value, out)
            }
        }
    }
    expr(&b.result, out);
    for on in &b.ons {
        if let heather_syntax::OnTarget::Stmt(t) = &on.target {
            ty(t, out);
        }
        expr(&on.expr, out);
    }
}

fn ty(t: &Ty, out: &mut Vec<Finding>) {
    match &t.kind {
        TyKind::Nat
        | TyKind::Univ { .. }
        | TyKind::Ctx
        | TyKind::TyCode { .. }
        | TyKind::Splice { .. } => {}
        TyKind::Eq(a, b) => {
            expr(a, out);
            expr(b, out);
        }
        TyKind::OfExpr(e) | TyKind::Fin(e) => expr(e, out),
        TyKind::Named { args, .. } => args.iter().for_each(|a| ty(a, out)),
        TyKind::Vec { elem, len } => {
            ty(elem, out);
            expr(len, out);
        }
        TyKind::Fn { dom, cod, .. } => {
            ty(dom, out);
            ty(cod, out);
        }
        TyKind::Code { ty: body, .. } => ty(body, out),
    }
}

fn expr(e: &Expr, out: &mut Vec<Finding>) {
    for lint in EXPR_LINTS {
        lint(e, out);
    }
    match &e.kind {
        ExprKind::Var(_)
        | ExprKind::OpSymbol { .. }
        | ExprKind::Univ { .. }
        | ExprKind::Num(_)
        | ExprKind::ArgSlot(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_) => {}
        ExprKind::TyLit(t) => ty(t, out),
        ExprKind::App { head, args, named, .. } => {
            expr(head, out);
            args.iter().for_each(|a| expr(a, out));
            named.iter().for_each(|a| expr(&a.expr, out));
        }
        ExprKind::TyApp { head, args } => {
            expr(head, out);
            args.iter().for_each(|a| ty(a, out));
        }
        ExprKind::Lam { binders, body } => {
            binders.iter().filter_map(|b| b.ty.as_ref()).for_each(|t| ty(t, out));
            expr(body, out);
        }
        ExprKind::VecLit(xs) => xs.iter().for_each(|x| expr(x, out)),
        ExprKind::Eq(a, b) | ExprKind::Index { recv: a, idx: b } => {
            expr(a, out);
            expr(b, out);
        }
        ExprKind::Match { scrut, motive, arms, .. } => {
            expr(scrut, out);
            motive.iter().for_each(|m| expr(m, out));
            arms.iter().for_each(|a| expr(&a.body, out));
        }
        ExprKind::MatchCode { scrut, motive, arms } => {
            expr(scrut, out);
            ty(motive, out);
            arms.iter().for_each(|a| expr(&a.body, out));
        }
        ExprKind::Dot { recv, args, named, .. } => {
            expr(recv, out);
            args.iter().flatten().for_each(|a| expr(a, out));
            named.iter().for_each(|a| expr(&a.expr, out));
        }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            tyargs.iter().for_each(|t| ty(t, out));
            fields.iter().for_each(|f| expr(&f.expr, out));
        }
        ExprKind::Block(b) => block(b, out),
        ExprKind::Quote(x) | ExprKind::Splice(x) => expr(x, out),
        ExprKind::J { proof, motive, case } => {
            expr(proof, out);
            expr(motive, out);
            expr(case, out);
        }
    }
}

fn match_function_application(e: &Expr, out: &mut Vec<Finding>) {
    let ExprKind::Lam { binders, body } = &e.kind else { return };
    let ExprKind::App { head, args, named, explicit } = &body.kind else { return };
    if *explicit || !named.is_empty() || args.is_empty() || args.len() > binders.len() {
        return;
    }
    let ExprKind::Match { motive: Some(motive), generated: false, .. } = &head.kind else {
        return;
    };
    let ExprKind::Lam { body: motive_body, .. } = &motive.kind else { return };
    if !matches!(&motive_body.kind, ExprKind::TyLit(t) if matches!(t.kind, TyKind::Fn { .. })) {
        return;
    }
    let tail = &binders[binders.len() - args.len()..];
    if !tail.iter().zip(args).all(|(binder, arg)| {
        matches!(&arg.kind, ExprKind::Var(name) if name == &binder.name)
    }) {
        return;
    }
    let names = tail.iter().map(|b| format!("`{}`", b.name)).collect::<Vec<_>>().join(", ");
    out.push(Finding {
        lint: Lint::MatchFunctionApplication,
        msg: format!(
            "this `match` returns a function only to be immediately applied to {names}; \
             move the trailing lambda binder{} into the match result so the match is in \
             checking position, where its motive may be inferable",
            if tail.len() == 1 { "" } else { "s" },
        ),
        span: head.span,
    });
}
