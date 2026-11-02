//! Uniform renaming of a local in surface syntax: every occurrence of the
//! name, bound or free, in expressions, types, blocks and patterns. Renaming
//! all of them to a fresh name is alpha-equivalence, so no binder needs
//! tracking: an inner `let x` becomes `let x'` along with every `x` it
//! shadows. A field or member name (`.x`, `x := e` in a record literal, a
//! named argument's name) is not a local and is kept.
//!
//! Used to put a generated body in SSA form where a consumer reads names by
//! their last binding (`crate::loops`' `while`, whose `decreases` obligations
//! mention the parameters).

use heather_syntax::{Block, Expr, ExprKind, Pat, Stmt, Ty, TyKind};

pub(crate) fn rename_block(b: &mut Block, from: &str, to: &str) {
    for s in &mut b.stmts {
        rename_stmt(s, from, to);
    }
    rename_expr(&mut b.result, from, to);
    for on in &mut b.ons {
        rename_expr(&mut on.expr, from, to);
    }
}

pub(crate) fn rename_stmt(s: &mut Stmt, from: &str, to: &str) {
    match s {
        Stmt::Let { name, ty, expr, .. } => {
            if name == from { *name = to.to_string(); }
            if let Some(t) = ty { rename_ty(t, from, to); }
            rename_expr(expr, from, to);
        }
        Stmt::LetRecord { fields, expr, .. } => {
            for f in fields { rename_pat(&mut f.pat, from, to); }
            rename_expr(expr, from, to);
        }
        Stmt::LetCode { name, expr, .. } => {
            if name == from { *name = to.to_string(); }
            rename_expr(expr, from, to);
        }
    }
}

fn rename_pat(p: &mut Pat, from: &str, to: &str) {
    match p {
        Pat::Var { name, .. } => if name == from { *name = to.to_string(); },
        Pat::Ctor { args, .. } => for a in args { rename_pat(a, from, to); },
        Pat::Named { pat, .. } => rename_pat(pat, from, to),
    }
}

pub(crate) fn rename_ty(t: &mut Ty, from: &str, to: &str) {
    match &mut t.kind {
        TyKind::Eq(a, b) => { rename_expr(a, from, to); rename_expr(b, from, to); }
        TyKind::OfExpr(e) | TyKind::Fin(e) | TyKind::TypeOf(e) => rename_expr(e, from, to),
        // A bare name in type position may be a local (`A`, a value read as
        // a type); with arguments it is a type constructor.
        TyKind::Named { name, args } => {
            if args.is_empty() && name == from { *name = to.to_string(); }
            for a in args { rename_ty(a, from, to); }
        }
        TyKind::Vec { elem, len } => { rename_ty(elem, from, to); rename_expr(len, from, to); }
        TyKind::Squash(inner) => rename_ty(inner, from, to),
        TyKind::Fn { binder, dom, cod, .. } => {
            if binder.as_deref() == Some(from) { *binder = Some(to.to_string()); }
            rename_ty(dom, from, to);
            rename_ty(cod, from, to);
        }
        TyKind::Code { ty, .. } => rename_ty(ty, from, to),
        TyKind::Nat | TyKind::Univ { .. } | TyKind::Ctx | TyKind::TyCode { .. } | TyKind::Splice { .. } => {}
    }
}

pub(crate) fn rename_expr(e: &mut Expr, from: &str, to: &str) {
    match &mut e.kind {
        ExprKind::Var(n) => if n == from { *n = to.to_string(); },
        ExprKind::OpSymbol { .. }
        | ExprKind::Univ { .. }
        | ExprKind::Num(_)
        | ExprKind::Scaled(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::ArgSlot(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_) => {}
        ExprKind::App { head, args, named, .. } => {
            rename_expr(head, from, to);
            for a in args { rename_expr(a, from, to); }
            for n in named { rename_expr(&mut n.expr, from, to); }
        }
        ExprKind::TyApp { head, args } => {
            rename_expr(head, from, to);
            for a in args { rename_ty(a, from, to); }
        }
        ExprKind::Lam { binders, body } => {
            for b in binders {
                if b.name == from { b.name = to.to_string(); }
                if let Some(t) = &mut b.ty { rename_ty(t, from, to); }
            }
            rename_expr(body, from, to);
        }
        ExprKind::CollectionLit(xs) => for x in xs { rename_expr(x, from, to); },
        ExprKind::Eq(a, b) => { rename_expr(a, from, to); rename_expr(b, from, to); }
        ExprKind::TyLit(t) => rename_ty(t, from, to),
        ExprKind::Match { scrut, eqbind, motive, arms, .. } => {
            rename_expr(scrut, from, to);
            if eqbind.as_deref() == Some(from) { *eqbind = Some(to.to_string()); }
            if let Some(m) = motive { rename_expr(m, from, to); }
            for a in arms {
                for p in &mut a.binders { rename_pat(p, from, to); }
                rename_expr(&mut a.body, from, to);
            }
        }
        ExprKind::MatchCode { scrut, motive, arms } => {
            rename_expr(scrut, from, to);
            rename_ty(motive, from, to);
            for a in arms {
                for p in &mut a.binders { rename_pat(p, from, to); }
                rename_expr(&mut a.body, from, to);
            }
        }
        ExprKind::Dot { recv, tyargs, args, named, .. } => {
            rename_expr(recv, from, to);
            for t in tyargs { rename_ty(t, from, to); }
            if let Some(xs) = args { for x in xs { rename_expr(x, from, to); } }
            for n in named { rename_expr(&mut n.expr, from, to); }
        }
        ExprKind::Index { recv, idx } => { rename_expr(recv, from, to); rename_expr(idx, from, to); }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            for t in tyargs { rename_ty(t, from, to); }
            for f in fields { rename_expr(&mut f.expr, from, to); }
        }
        ExprKind::RecordUpdate { base, fields } => {
            rename_expr(base, from, to);
            for f in fields { rename_expr(&mut f.expr, from, to); }
        }
        ExprKind::Block(b) => rename_block(b, from, to),
        ExprKind::Quote(x) | ExprKind::Splice(x) => rename_expr(x, from, to),
        ExprKind::J { proof, motive, case } => {
            rename_expr(proof, from, to);
            rename_expr(motive, from, to);
            rename_expr(case, from, to);
        }
    }
}

/// `b` with each top-level `let` that rebinds a name already bound (by
/// `bound`, or an earlier statement) renamed to a fresh `name__N`, and
/// every later occurrence with it: the block reads the same, and no
/// top-level binder shadows another.
pub(crate) fn ssa(b: &mut Block, bound: &[String]) {
    let mut seen: Vec<String> = bound.to_vec();
    let mut fresh = 0usize;
    for i in 0..b.stmts.len() {
        let name = match &b.stmts[i] {
            Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => name.clone(),
            Stmt::LetRecord { .. } => continue,
        };
        if !seen.contains(&name) {
            seen.push(name);
            continue;
        }
        let to = loop {
            fresh += 1;
            let candidate = format!("{name}__{fresh}");
            if !seen.contains(&candidate) && !mentions(b, &candidate) { break candidate; }
        };
        match &mut b.stmts[i] {
            Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => *name = to.clone(),
            Stmt::LetRecord { .. } => unreachable!(),
        }
        for s in &mut b.stmts[i + 1..] {
            rename_stmt(s, &name, &to);
        }
        rename_expr(&mut b.result, &name, &to);
        for on in &mut b.ons {
            rename_expr(&mut on.expr, &name, &to);
        }
        seen.push(to);
    }
}

fn mentions(b: &Block, name: &str) -> bool {
    let e = Expr { kind: ExprKind::Block(Box::new(b.clone())), span: b.span };
    crate::measure::mentions_context(&e, name)
}
