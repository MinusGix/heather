//! Uniform renaming of a local in surface syntax: every occurrence of the
//! name, bound or free, in expressions, types, blocks and patterns. Renaming
//! all of them to a fresh name is alpha-equivalence, so no binder needs
//! tracking: an inner `let x` becomes `let x'` along with every `x` it
//! shadows. A field or member name (`.x`, `x := e` in a record literal, a
//! named argument's name) is not a local and is kept.
//!
//! Used to put a generated body in SSA form (`crate::loops`' `while`, whose
//! condition is placed after the body's `let`s and reads the parameters),
//! and to deshadow a `decreases` body ([`deshadow`]), whose lowering reads
//! names by their last binding.

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
        | ExprKind::SuffixedNum { .. }
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

/// `body` with every binder that shadows a name already in scope — a
/// parameter in `bound`, or an enclosing or earlier binder — renamed to a
/// fresh `name__N` across its own scope: block `let`s, `let { … }`
/// patterns, `match` arm binders and equation binders, and λ binders, at
/// any depth. Siblings that reuse a name (two arms both binding `k`) do not
/// shadow each other and are kept. The result is alpha-equivalent to
/// `body`, and every name in it means one binder wherever it is read.
///
/// `decreases` reads names by their last binding: its measure is stated
/// over the parameters, and a lifted obligation's telescope is a list of
/// binders by name, so a `let m = m - 1` that shadowed the measured `m`
/// made the call's obligation `m < m` (issues/decreases-shadowed-let.md).
/// The lowering deshadows the body first, so neither has to track scopes.
pub(crate) fn deshadow(body: &mut Block, bound: &[String]) {
    let whole = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
    let mut taken: Vec<String> = bound.to_vec();
    collect_names(&whole, &mut taken);
    let mut d = Deshadow { env: bound.to_vec(), taken, whole, fresh: 0 };
    d.block(body);
}

/// Every local name `e` binds or reads, for [`deshadow`]'s fresh names.
pub(crate) fn collect_names(e: &Expr, out: &mut Vec<String>) {
    crate::surface::walk_expr(e, &mut |x| match &x.kind {
        ExprKind::Var(n) => out.push(n.clone()),
        ExprKind::Lam { binders, .. } => out.extend(binders.iter().map(|b| b.name.clone())),
        ExprKind::Block(b) => for s in &b.stmts {
            match s {
                Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => out.push(name.clone()),
                Stmt::LetRecord { fields, .. } => for f in fields { crate::measure::pat_names(&f.pat, out); },
            }
        },
        ExprKind::Match { eqbind, arms, .. } => {
            out.extend(eqbind.iter().cloned());
            for a in arms { for p in &a.binders { crate::measure::pat_names(p, out); } }
        }
        ExprKind::MatchCode { arms, .. } => {
            for a in arms { for p in &a.binders { crate::measure::pat_names(p, out); } }
        }
        _ => {}
    });
}

struct Deshadow {
    /// The names in scope at the walk's position, innermost last.
    env: Vec<String>,
    /// Every name the body mentions or binds, and each fresh one handed out.
    taken: Vec<String>,
    /// The body as given, for names in positions [`collect_names`] skips.
    whole: Expr,
    fresh: usize,
}

impl Deshadow {
    /// The name a binder `name` is bound under: itself, unless it shadows.
    fn binder(&mut self, name: &str) -> Option<String> {
        if name == "_" || !self.env.iter().any(|n| n == name) {
            return None;
        }
        let to = loop {
            self.fresh += 1;
            let candidate = format!("{name}__{}", self.fresh);
            if !self.taken.contains(&candidate) && !crate::measure::mentions_context(&self.whole, &candidate) {
                break candidate;
            }
        };
        self.taken.push(to.clone());
        Some(to)
    }

    fn block(&mut self, b: &mut Block) {
        let depth = self.env.len();
        for i in 0..b.stmts.len() {
            let (first, rest) = b.stmts.split_at_mut(i + 1);
            let s = &mut first[i];
            // The statement's own value and annotation are read in the scope
            // before its binders.
            let mut names: Vec<String> = Vec::new();
            match s {
                Stmt::Let { name, ty, expr, .. } => {
                    if let Some(t) = ty { self.ty(t); }
                    self.expr(expr);
                    names.push(name.clone());
                }
                Stmt::LetCode { name, expr, .. } => {
                    self.expr(expr);
                    names.push(name.clone());
                }
                Stmt::LetRecord { fields, expr, .. } => {
                    self.expr(expr);
                    for f in fields.iter() { crate::measure::pat_names(&f.pat, &mut names); }
                }
            }
            for name in names {
                if let Some(to) = self.binder(&name) {
                    match s {
                        Stmt::Let { name: n, .. } | Stmt::LetCode { name: n, .. } => *n = to.clone(),
                        Stmt::LetRecord { fields, .. } => for f in fields.iter_mut() { rename_pat(&mut f.pat, &name, &to); },
                    }
                    for later in rest.iter_mut() { rename_stmt(later, &name, &to); }
                    rename_expr(&mut b.result, &name, &to);
                    for on in &mut b.ons { rename_expr(&mut on.expr, &name, &to); }
                    self.env.push(to);
                } else {
                    self.env.push(name);
                }
            }
        }
        self.expr(&mut b.result);
        for on in &mut b.ons { self.expr(&mut on.expr); }
        self.env.truncate(depth);
    }

    /// Bind `names` (already renamed in place where they shadow) over `body`,
    /// renaming each shadowing one in it first.
    fn under(&mut self, pats: &mut [Pat], body: &mut Expr) {
        let depth = self.env.len();
        let mut names = Vec::new();
        for p in pats.iter() { crate::measure::pat_names(p, &mut names); }
        for name in names {
            if let Some(to) = self.binder(&name) {
                for p in pats.iter_mut() { rename_pat(p, &name, &to); }
                rename_expr(body, &name, &to);
                self.env.push(to);
            } else {
                self.env.push(name);
            }
        }
        self.expr(body);
        self.env.truncate(depth);
    }

    fn ty(&mut self, t: &mut Ty) {
        match &mut t.kind {
            TyKind::Eq(a, b) => { self.expr(a); self.expr(b); }
            TyKind::OfExpr(e) | TyKind::Fin(e) | TyKind::TypeOf(e) => self.expr(e),
            TyKind::Named { args, .. } => for a in args { self.ty(a); },
            TyKind::Vec { elem, len } => { self.ty(elem); self.expr(len); }
            TyKind::Squash(inner) | TyKind::Code { ty: inner, .. } => self.ty(inner),
            TyKind::Fn { binder, dom, cod, .. } => {
                self.ty(dom);
                let depth = self.env.len();
                if let Some(name) = binder.clone() {
                    if let Some(to) = self.binder(&name) {
                        *binder = Some(to.clone());
                        rename_ty(cod, &name, &to);
                        self.env.push(to);
                    } else {
                        self.env.push(name);
                    }
                }
                self.ty(cod);
                self.env.truncate(depth);
            }
            TyKind::Nat | TyKind::Univ { .. } | TyKind::Ctx | TyKind::TyCode { .. } | TyKind::Splice { .. } => {}
        }
    }

    fn expr(&mut self, e: &mut Expr) {
        match &mut e.kind {
            ExprKind::Var(_)
            | ExprKind::OpSymbol { .. }
            | ExprKind::Univ { .. }
            | ExprKind::Num(_)
            | ExprKind::SuffixedNum { .. }
            | ExprKind::Scaled(_)
            | ExprKind::Char(_)
            | ExprKind::Str(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl
            | ExprKind::Hole(_) => {}
            ExprKind::App { head, args, named, .. } => {
                self.expr(head);
                for a in args { self.expr(a); }
                for n in named { self.expr(&mut n.expr); }
            }
            ExprKind::TyApp { head, args } => {
                self.expr(head);
                for a in args { self.ty(a); }
            }
            ExprKind::Lam { binders, body } => {
                let depth = self.env.len();
                for i in 0..binders.len() {
                    if let Some(t) = &mut binders[i].ty { self.ty(t); }
                    let name = binders[i].name.clone();
                    if let Some(to) = self.binder(&name) {
                        binders[i].name = to.clone();
                        for later in &mut binders[i + 1..] {
                            if let Some(t) = &mut later.ty { rename_ty(t, &name, &to); }
                            // A later binder of the same name is renamed with
                            // the rest of its scope; it then shadows `to`.
                            if later.name == name { later.name = to.clone(); }
                        }
                        rename_expr(body, &name, &to);
                        self.env.push(to);
                    } else {
                        self.env.push(name);
                    }
                }
                self.expr(body);
                self.env.truncate(depth);
            }
            ExprKind::CollectionLit(xs) => for x in xs { self.expr(x); },
            ExprKind::Eq(a, b) => { self.expr(a); self.expr(b); }
            ExprKind::TyLit(t) => self.ty(t),
            ExprKind::Match { scrut, eqbind, motive, arms, .. } => {
                self.expr(scrut);
                if let Some(m) = motive { self.expr(m); }
                let depth = self.env.len();
                if let Some(name) = eqbind.clone() {
                    if let Some(to) = self.binder(&name) {
                        *eqbind = Some(to.clone());
                        for a in arms.iter_mut() {
                            for p in &mut a.binders { rename_pat(p, &name, &to); }
                            rename_expr(&mut a.body, &name, &to);
                        }
                        self.env.push(to);
                    } else {
                        self.env.push(name);
                    }
                }
                for a in arms { self.under(&mut a.binders, &mut a.body); }
                self.env.truncate(depth);
            }
            ExprKind::MatchCode { scrut, motive, arms } => {
                self.expr(scrut);
                self.ty(motive);
                for a in arms { self.under(&mut a.binders, &mut a.body); }
            }
            ExprKind::Dot { recv, tyargs, args, named, .. } => {
                self.expr(recv);
                for t in tyargs { self.ty(t); }
                if let Some(xs) = args { for x in xs { self.expr(x); } }
                for n in named { self.expr(&mut n.expr); }
            }
            ExprKind::Index { recv, idx } => { self.expr(recv); self.expr(idx); }
            ExprKind::RecordLit { tyargs, fields, .. } => {
                for t in tyargs { self.ty(t); }
                for f in fields { self.expr(&mut f.expr); }
            }
            ExprKind::RecordUpdate { base, fields } => {
                self.expr(base);
                for f in fields { self.expr(&mut f.expr); }
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::Quote(x) | ExprKind::Splice(x) => self.expr(x),
            ExprKind::J { proof, motive, case } => {
                self.expr(proof);
                self.expr(motive);
                self.expr(case);
            }
        }
    }
}

/// Every expression in `e`, outermost first, mutably: `f` returns whether
/// it replaced the node, and a replaced node's children are not visited.
/// Expressions inside types are not visited (a type is not rewritten here).
pub(crate) fn walk_expr_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Expr) -> bool) {
    if f(e) {
        return;
    }
    match &mut e.kind {
        ExprKind::Var(_)
        | ExprKind::OpSymbol { .. }
        | ExprKind::Univ { .. }
        | ExprKind::Num(_)
        | ExprKind::SuffixedNum { .. }
        | ExprKind::Scaled(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::ArgSlot(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_)
        | ExprKind::TyLit(_) => {}
        ExprKind::App { head, args, named, .. } => {
            walk_expr_mut(head, f);
            for a in args { walk_expr_mut(a, f); }
            for n in named { walk_expr_mut(&mut n.expr, f); }
        }
        ExprKind::TyApp { head, .. } => walk_expr_mut(head, f),
        ExprKind::Lam { body, .. } => walk_expr_mut(body, f),
        ExprKind::CollectionLit(xs) => for x in xs { walk_expr_mut(x, f); },
        ExprKind::Eq(a, b) => { walk_expr_mut(a, f); walk_expr_mut(b, f); }
        ExprKind::Match { scrut, motive, arms, .. } => {
            walk_expr_mut(scrut, f);
            if let Some(m) = motive { walk_expr_mut(m, f); }
            for a in arms { walk_expr_mut(&mut a.body, f); }
        }
        ExprKind::MatchCode { scrut, arms, .. } => {
            walk_expr_mut(scrut, f);
            for a in arms { walk_expr_mut(&mut a.body, f); }
        }
        ExprKind::Dot { recv, args, named, .. } => {
            walk_expr_mut(recv, f);
            if let Some(xs) = args { for x in xs { walk_expr_mut(x, f); } }
            for n in named { walk_expr_mut(&mut n.expr, f); }
        }
        ExprKind::Index { recv, idx } => { walk_expr_mut(recv, f); walk_expr_mut(idx, f); }
        ExprKind::RecordLit { fields, .. } => for x in fields { walk_expr_mut(&mut x.expr, f); },
        ExprKind::RecordUpdate { base, fields } => {
            walk_expr_mut(base, f);
            for x in fields { walk_expr_mut(&mut x.expr, f); }
        }
        ExprKind::Block(b) => {
            for s in &mut b.stmts {
                match s {
                    Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => walk_expr_mut(expr, f),
                }
            }
            walk_expr_mut(&mut b.result, f);
            for on in &mut b.ons { walk_expr_mut(&mut on.expr, f); }
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => walk_expr_mut(x, f),
        ExprKind::J { proof, motive, case } => {
            walk_expr_mut(proof, f);
            walk_expr_mut(motive, f);
            walk_expr_mut(case, f);
        }
    }
}
