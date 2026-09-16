//! Can the role of a `<` token be recovered from the AST?
//! (issues/heather-formatter.md — the premise the formatter's design rests on.)
//!
//! `TokKind::Lt` is emitted for *both* the comparison operator (`a < b`) and
//! the opener of a type-argument list (`Vec<T, A>`), so a purely lexical
//! formatter cannot know whether to pad it. `TokKind::Gt` is unambiguous — the
//! lexer's own comment says `>` is never an operator — so every `Gt` in a file
//! closes exactly one argument list.
//!
//! That gives a *completeness check* for free: walk the AST, derive one
//! `(open, close)` pair per argument list, and assert the derived closers are
//! exactly the file's `Gt` tokens. If the two sets agree over the whole corpus,
//! the derivation found every list and the remaining `Lt` tokens are operators.
//!
//! The census stays as a test, not just a spike: a new argument-list site added
//! to the grammar without a case here shows up as an unaccounted-for `>`.

use heather_syntax::lexer::{lex, Tok, TokKind};
use heather_syntax::*;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn hthr_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            hthr_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "hthr") {
            out.push(p);
        }
    }
}

/// One derived argument list: the byte offsets of its `<` and `>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Delims {
    open: usize,
    close: usize,
}

struct Walk<'a> {
    toks: &'a [Tok],
    /// Each derived argument list, labelled by the AST site that produced
    /// it so a disagreement names the case that is wrong.
    sites: Vec<(&'static str, Delims)>,
    /// Sites carrying arguments in the AST for which no `<` exists in the
    /// source. Not a failure: `P ∨ Q` and `¬P` are parser-desugared to
    /// `Named { name: "Or" | "Not", args }`, so the AST reports an argument
    /// list the author never wrote. A formatter must tolerate these rather
    /// than assume every argument-bearing node has delimiters.
    unlocated: Vec<(&'static str, Span)>,
}

impl<'a> Walk<'a> {
    /// The first `Lt` at or after `from` and strictly before `before`.
    fn lt_in(&self, from: usize, before: usize) -> Option<usize> {
        self.toks
            .iter()
            .find(|t| {
                matches!(t.kind, TokKind::Lt) && t.span.start >= from && t.span.start < before
            })
            .map(|t| t.span.start)
    }

    /// The **first** `Gt` at or after `from`. Every argument carries a span,
    /// so nothing but the closer can lie between the last argument's end and
    /// the next `>`: taking the last `Gt` in the node's region instead walks
    /// past the list into the declaration body.
    fn gt_after(&self, from: usize) -> Option<usize> {
        self.toks
            .iter()
            .find(|t| matches!(t.kind, TokKind::Gt) && t.span.start >= from)
            .map(|t| t.span.start)
    }

    /// An argument list whose arguments carry spans: `Name<A, B>` in any
    /// position. `region` is the whole node; `first`/`last` bound the args.
    fn list_spanned(&mut self, site: &'static str, region: Span, first: Span, last: Span) {
        match (self.lt_in(region.start, first.start), self.gt_after(last.end)) {
            (Some(open), Some(close)) => self.sites.push((site, Delims { open, close })),
            _ => self.unlocated.push((site, region)),
        }
    }

    /// A parameter list whose names are bare `String`s in the AST and so carry
    /// no spans — `class C<A>`, `inductive I<A>`. Located from the declared
    /// name instead; the names cannot nest, so the first `Gt` after the opener
    /// closes the list.
    fn list_bare(&mut self, site: &'static str, region: Span, name: &str) {
        let after_name = self
            .toks
            .iter()
            .find(|t| {
                t.span.start >= region.start
                    && matches!(&t.kind, TokKind::Ident(i) if i == name)
            })
            .map(|t| t.span.end);
        let Some(after_name) = after_name else {
            self.unlocated.push((site, region));
            return;
        };
        let open = self
            .toks
            .iter()
            .find(|t| matches!(t.kind, TokKind::Lt) && t.span.start >= after_name)
            .map(|t| t.span.start);
        let Some(open) = open else {
            self.unlocated.push((site, region));
            return;
        };
        match self
            .toks
            .iter()
            .find(|t| matches!(t.kind, TokKind::Gt) && t.span.start > open)
            .map(|t| t.span.start)
        {
            Some(close) => self.sites.push((site, Delims { open, close })),
            None => self.unlocated.push((site, region)),
        }
    }

    fn ty(&mut self, t: &Ty) {
        match &t.kind {
            TyKind::Named { args, .. } if !args.is_empty() => {
                self.list_spanned("ty-named", t.span, args[0].span, args[args.len() - 1].span);
                for a in args {
                    self.ty(a);
                }
            }
            TyKind::Named { .. } | TyKind::Nat | TyKind::Ctx | TyKind::Splice { .. } => {}
            TyKind::Univ { .. } => {
                // `Type<n>` writes a numeral; `Type` alone writes nothing.
                if let Some(open) = self.lt_in(t.span.start, t.span.end) {
                    if let Some(close) = self.gt_after(open) {
                        self.sites.push(("ty-univ", Delims { open, close }));
                    }
                }
            }
            TyKind::Eq(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            TyKind::OfExpr(e) | TyKind::Fin(e) => self.expr(e),
            TyKind::Vec { elem, len } => {
                self.ty(elem);
                self.expr(len);
            }
            TyKind::Squash(inner) => {
                // Two spellings: `∥A∥` has no angle brackets, `Squash<A>` does.
                if let Some(open) = self.lt_in(t.span.start, inner.span.start) {
                    if let Some(close) = self.gt_after(inner.span.end) {
                        self.sites.push(("ty-squash", Delims { open, close }));
                    }
                }
                self.ty(inner);
            }
            TyKind::Fn { dom, cod, .. } => {
                self.ty(dom);
                self.ty(cod);
            }
            TyKind::TyCode { .. } => {}
            TyKind::Code { ty, .. } => self.ty(ty),
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Var(_)
            | ExprKind::OpSymbol { .. }
            | ExprKind::Num(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl
            | ExprKind::Hole(_) => {}
            ExprKind::Univ { .. } => {
                if let Some(open) = self.lt_in(e.span.start, e.span.end) {
                    if let Some(close) = self.gt_after(open) {
                        self.sites.push(("expr-univ", Delims { open, close }));
                    }
                }
            }
            ExprKind::App { head, args, named, .. } => {
                self.expr(head);
                for a in args {
                    self.expr(a);
                }
                for n in named {
                    self.expr(&n.expr);
                }
            }
            ExprKind::TyApp { head, args } => {
                if !args.is_empty() {
                    self.list_spanned(
                        "expr-tyapp",
                        e.span,
                        args[0].span,
                        args[args.len() - 1].span,
                    );
                }
                self.expr(head);
                for a in args {
                    self.ty(a);
                }
            }
            ExprKind::Lam { binders, body } => {
                for b in binders {
                    if let Some(t) = &b.ty {
                        self.ty(t);
                    }
                }
                self.expr(body);
            }
            ExprKind::CollectionLit(xs) => {
                for x in xs {
                    self.expr(x);
                }
            }
            ExprKind::Eq(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::TyLit(t) => self.ty(t),
            ExprKind::Match { scrut, motive, arms, .. } => {
                self.expr(scrut);
                if let Some(m) = motive {
                    self.expr(m);
                }
                for a in arms {
                    self.expr(&a.body);
                }
            }
            ExprKind::MatchCode { scrut, motive, arms } => {
                self.expr(scrut);
                self.ty(motive);
                for a in arms {
                    self.expr(&a.body);
                }
            }
            ExprKind::Dot { recv, args, named, .. } => {
                self.expr(recv);
                for a in args.iter().flatten() {
                    self.expr(a);
                }
                for n in named {
                    self.expr(&n.expr);
                }
            }
            ExprKind::Index { recv, idx } => {
                self.expr(recv);
                self.expr(idx);
            }
            ExprKind::RecordLit { tyargs, fields, .. } => {
                if !tyargs.is_empty() {
                    self.list_spanned(
                        "expr-recordlit",
                        e.span,
                        tyargs[0].span,
                        tyargs[tyargs.len() - 1].span,
                    );
                }
                for t in tyargs {
                    self.ty(t);
                }
                for f in fields {
                    self.expr(&f.expr);
                }
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

    fn block(&mut self, b: &Block) {
        for s in &b.stmts {
            match s {
                Stmt::Let { ty, expr, .. } => {
                    if let Some(t) = ty {
                        self.ty(t);
                    }
                    self.expr(expr);
                }
                Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => self.expr(expr),
            }
        }
        self.expr(&b.result);
        for o in &b.ons {
            if let OnTarget::Stmt(t) = &o.target {
                self.ty(t);
            }
            self.expr(&o.expr);
        }
    }

    fn param(&mut self, p: &Param) {
        self.ty(&p.ty);
    }

    fn class_ref(&mut self, c: &ClassRef, region: Span) {
        if !c.args.is_empty() {
            self.list_spanned(
                "class-ref",
                region,
                c.args[0].span,
                c.args[c.args.len() - 1].span,
            );
        }
        for a in &c.args {
            self.ty(a);
        }
        for i in &c.index {
            self.expr(i);
        }
    }

    fn decl(&mut self, d: &Decl) {
        if !d.tyvars.is_empty() {
            self.list_spanned(
                "decl-tyvars",
                d.span,
                d.tyvars[0].span,
                d.tyvars[d.tyvars.len() - 1].span,
            );
        }
        for p in &d.params {
            self.param(p);
        }
        self.ty(&d.result);
        if let Some(e) = &d.decreases {
            self.expr(e);
        }
        self.block(&d.body);
    }

    fn item(&mut self, it: &Item) {
        match it {
            Item::Decl(d) => self.decl(d),
            Item::Inductive(i) => {
                if !i.params.is_empty() {
                    self.list_bare("inductive-params", i.span, &i.name);
                }
                for p in &i.valparams {
                    self.param(p);
                }
                if let Some(t) = &i.index {
                    self.ty(t);
                }
                for c in &i.ctors {
                    for f in &c.fields {
                        self.ty(&f.ty);
                    }
                    if let Some(r) = &c.result {
                        self.expr(r);
                    }
                }
            }
            Item::Class(c) => {
                if !c.params.is_empty() {
                    self.list_bare("class-params", c.span, &c.name);
                }
                for p in &c.valparams {
                    self.param(p);
                }
                for e in &c.extends {
                    self.class_ref(e, c.span);
                }
                for f in &c.fields {
                    self.ty(&f.ty);
                }
            }
            Item::Instance(i) => {
                if !i.tyvars.is_empty() {
                    self.list_spanned(
                        "instance-tyvars",
                        i.span,
                        i.tyvars[0].span,
                        i.tyvars[i.tyvars.len() - 1].span,
                    );
                }
                for p in &i.valparams {
                    self.param(p);
                }
                self.class_ref(&i.class, i.span);
                for r in &i.requires {
                    self.param(r);
                }
                match &i.body {
                    InstanceBody::Block(ds) => {
                        for d in ds {
                            self.decl(d);
                        }
                    }
                    InstanceBody::Literal(fs) => {
                        for f in fs {
                            self.expr(&f.expr);
                        }
                    }
                }
            }
            Item::Designation(d) => {
                if !d.tyvars.is_empty() {
                    // `designation<A> ++ at List<A> := append`: bare names, so
                    // the first `>` after the opener closes the list.
                    match self
                        .lt_in(d.span.start, d.carrier.span.start)
                        .and_then(|open| self.gt_after(open).map(|close| Delims { open, close }))
                    {
                        Some(delims) => self.sites.push(("designation-tyvars", delims)),
                        None => self.unlocated.push(("designation-tyvars", d.span)),
                    }
                }
                self.ty(&d.carrier);
                self.expr(&d.op);
            }
            Item::Datarepr(d) => {
                self.ty(&d.spec);
                self.datarepr_body(&d.body);
            }
            Item::Impl(i) => self.datarepr_body(&i.body),
            Item::Import(_) => {}
        }
    }

    fn datarepr_body(&mut self, b: &DatareprBody) {
        match b {
            DatareprBody::Fields(fs) => {
                for f in fs {
                    self.expr(&f.expr);
                }
            }
            DatareprBody::Mint(e) => self.expr(e),
        }
    }
}

#[test]
fn every_gt_is_accounted_for() {
    let root = repo_root();
    let mut files = Vec::new();
    hthr_files(&root.join("lib"), &mut files);
    hthr_files(&root.join("examples"), &mut files);
    hthr_files(&root.join("crates"), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no .hthr corpus found under {}", root.display());

    let mut checked = 0usize;
    let mut unparsed = 0usize;
    let mut total_gt = 0usize;
    let mut total_lt = 0usize;
    let mut opener_lt = 0usize;
    let mut desugared = 0usize;
    let mut report = String::new();

    for path in &files {
        let src = std::fs::read_to_string(path).unwrap();
        let Ok(file) = parse_file(&src) else {
            unparsed += 1;
            continue;
        };
        let toks = lex(&src).unwrap();
        let mut w = Walk { toks: &toks, sites: Vec::new(), unlocated: Vec::new() };
        for it in &file.items {
            w.item(it);
        }

        let mut gts: Vec<usize> = toks
            .iter()
            .filter(|t| matches!(t.kind, TokKind::Gt))
            .map(|t| t.span.start)
            .collect();
        gts.sort();
        total_gt += gts.len();

        // A grouped binder (`before, after: MachineState<Mem>`) gives every
        // name its own `Param` over one written `Ty`, so the same list is
        // reached twice. Identical delimiters are benign; two *different*
        // openers claiming one `>` would mean a real misderivation.
        let mut pairs: Vec<Delims> = w.sites.iter().map(|(_, d)| *d).collect();
        pairs.sort();
        pairs.dedup();
        for a in &pairs {
            let rival: Vec<&Delims> =
                pairs.iter().filter(|b| b.close == a.close && b.open != a.open).collect();
            assert!(
                rival.is_empty(),
                "{}: `>` at {} claimed by two different openers: {:?}",
                path.strip_prefix(&root).unwrap_or(path).display(),
                a.close,
                rival
            );
        }
        let mut closes: Vec<usize> = pairs.iter().map(|d| d.close).collect();
        closes.sort();

        let rel = path.strip_prefix(&root).unwrap_or(path).display().to_string();
        if closes != gts {
            let missed: Vec<_> = gts.iter().filter(|g| !closes.contains(g)).take(5).collect();
            let extra: Vec<_> = closes.iter().filter(|c| !gts.contains(c)).take(5).collect();
            report.push_str(&format!(
                "{rel}: {} derived vs {} Gt; missed@{:?} extra@{:?} unlocated={:?}\n",
                closes.len(),
                gts.len(),
                missed,
                extra,
                &w.unlocated[..w.unlocated.len().min(3)],
            ));
        }
        // Every derived opener must actually be an `Lt`.
        for d in &pairs {
            assert!(
                toks.iter().any(|t| matches!(t.kind, TokKind::Lt) && t.span.start == d.open),
                "{rel}: derived opener at {} is not an `Lt`",
                d.open
            );
        }
        total_lt += toks.iter().filter(|t| matches!(t.kind, TokKind::Lt)).count();
        opener_lt += pairs.len();
        desugared += w.unlocated.len();
        checked += 1;
    }

    eprintln!(
        "spike: {checked} files parsed ({unparsed} unparseable, skipped); \
         {total_gt} `>` all accounted for; \
         {total_lt} `<` = {opener_lt} openers + {} comparisons; \
         {desugared} argument lists exist only after desugaring",
        total_lt - opener_lt
    );
    assert!(report.is_empty(), "argument-list derivation disagrees with `>` census:\n{report}");
}
