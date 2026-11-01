//! Which `<` opens a type-argument list?
//!
//! [`TokKind::Lt`] is emitted for both the comparison operator (`a < b`) and
//! the opener of an argument list (`Vec<T, A>`), so the token stream alone
//! cannot say which spacing a `<` wants. [`TokKind::Gt`] is unambiguous — `>`
//! is never an operator — so every `>` closes exactly one list, which is what
//! makes the derivation here checkable: see
//! `tests/generic_delimiter_roles.rs`, which requires the derived closers to
//! be exactly the file's `Gt` tokens over the whole repository corpus.
//!
//! `<` is the first token whose role its kind does not determine, and not the
//! last: infix subtraction makes `a - b` vs `-b` the second
//! (issues/infix-subtraction-notation.md), read off the same walk. Hence
//! [`TokenRole`] rather than a `<`-shaped answer.

use crate::ast::*;
use crate::lexer::{Tok, TokKind};

/// What a token means where it stands, when its [`TokKind`] does not say.
///
/// Absence is the ordinary reading — a `<` is a comparison, a `-` is a prefix
/// negation — so only the exceptions are recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenRole {
    /// A `<` opening a type-argument list, or the `>` closing one.
    ArgumentDelimiter,
    /// An operator symbol being *declared* rather than applied, as the `-` of
    /// `designation prefix - at Int := neg`. It has no operands, so none of
    /// the spacing rules about operands apply to it.
    OperatorName,
    /// A `-` standing between two operands: subtraction, spaced like `+`,
    /// rather than a prefix negation hugging the operand after it.
    InfixMinus,
}

/// Every token in `file` whose role its [`TokKind`] does not determine, keyed
/// by byte offset.
pub fn token_roles(toks: &[Tok], file: &File) -> std::collections::HashMap<usize, TokenRole> {
    let mut map = std::collections::HashMap::new();
    let w = walk(toks, file);
    for (_, d) in w.sites {
        map.insert(d.open, TokenRole::ArgumentDelimiter);
        map.insert(d.close, TokenRole::ArgumentDelimiter);
    }
    for at in w.infix_minus {
        map.insert(at, TokenRole::InfixMinus);
    }
    for it in &file.items {
        let Item::Designation(d) = it else { continue };
        // `designation [<tyvars>] [fixity] SYMBOL at CARRIER := OP`: the symbol
        // is whatever sits immediately before the `at` keyword. Reading it off
        // the token stream avoids a span the AST does not carry.
        let at = toks.iter().position(|t| {
            t.span.start >= d.span.start
                && t.span.end <= d.span.end
                && matches!(&t.kind, TokKind::Ident(i) if i == "at")
        });
        if let Some(i) = at.filter(|i| *i > 0) {
            map.insert(toks[i - 1].span.start, TokenRole::OperatorName);
        }
    }
    map
}

/// Every argument list found in one parsed file.
#[derive(Debug, Default)]
pub struct ArgumentLists {
    /// Each list, labelled by the AST site that produced it so a disagreement
    /// names the case that is wrong.
    pub lists: Vec<(&'static str, Delims)>,
    /// Sites carrying arguments in the AST for which no `<` exists in the
    /// source. Not a failure: `P ∨ Q` and `¬P` are parser-desugared to
    /// `Named { name: "Or" | "Not", args }`, so the AST reports an argument
    /// list the author never wrote. Callers must tolerate these rather than
    /// assume every argument-bearing node has delimiters.
    pub undelimited: Vec<(&'static str, Span)>,
}

/// Derive every argument list in `file`, whose source lexed to `toks`.
pub fn argument_lists(toks: &[Tok], file: &File) -> ArgumentLists {
    let w = walk(toks, file);
    ArgumentLists { lists: w.sites, undelimited: w.unlocated }
}

fn walk<'a>(toks: &'a [Tok], file: &File) -> Walk<'a> {
    let mut w = Walk { toks, sites: Vec::new(), unlocated: Vec::new(), infix_minus: Vec::new() };
    for it in &file.items {
        w.item(it);
    }
    for &(head, first, last) in &file.section_typarams {
        w.list_spanned("section-tyvars", head, first, last);
    }
    w
}

/// One derived argument list: the byte offsets of its `<` and `>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Delims {
    /// Byte offset of the `<`.
    pub open: usize,
    /// Byte offset of the `>`.
    pub close: usize,
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
    /// Byte offset of each `-` that subtracts rather than negates.
    infix_minus: Vec<usize>,
}

impl<'a> Walk<'a> {
    /// The **last** `Lt` at or after `from` and strictly before `before`.
    ///
    /// Last, not first: a node's span often starts well left of its own
    /// argument list. `instance<P: Decide> Decide<¬P>` reaches `class_ref`
    /// with the whole instance as its region, and the first `Lt` there opens
    /// the *instance's* parameter list, not the class reference's. Since no
    /// type argument can begin with `<`, the opener is always the nearest `<`
    /// to the left of the first argument.
    fn lt_in(&self, from: usize, before: usize) -> Option<usize> {
        self.toks
            .iter()
            .rev()
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

    /// The operator of `l - r`. The head's span is the whole application, so
    /// the token is found between the operands: the **first** `Minus` after
    /// `l`, since only closing parentheses can precede it there, while a
    /// parenthesised `r` may open with a negation of its own (`a - (-b)`).
    fn minus_between(&mut self, l: Span, r: Span) {
        let at = self.toks.iter().find(|t| {
            matches!(t.kind, TokKind::Minus) && t.span.start >= l.end && t.span.start < r.start
        });
        if let Some(t) = at {
            self.infix_minus.push(t.span.start);
        }
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

    /// `Pos<A>` as a binder's type or a function's result is parser sugar
    /// (`parser::pos_carrier`): the AST keeps only the carrier `A`, so the
    /// list `Pos<…>` wrote around it is found from the tokens that hug it.
    fn pos_wrapper(&mut self, t: &Ty) {
        let Some(at) = self.toks.iter().position(|k| k.span.start == t.span.start) else { return };
        if at < 2
            || !matches!(self.toks[at - 1].kind, TokKind::Lt)
            || !matches!(&self.toks[at - 2].kind, TokKind::Ident(i) if i == "Pos")
        {
            return;
        }
        let after = self.toks.iter().find(|k| k.span.start >= t.span.end);
        if let Some(close) = after.filter(|k| matches!(k.kind, TokKind::Gt)) {
            self.sites.push(("ty-pos-sugar", Delims { open: self.toks[at - 1].span.start, close: close.span.start }));
        }
    }

    fn ty(&mut self, t: &Ty) {
        self.pos_wrapper(t);
        match &t.kind {
            TyKind::Named { args, .. } if !args.is_empty() => {
                self.list_spanned("ty-named", t.span, args[0].span, args[args.len() - 1].span);
                for a in args {
                    self.ty(a);
                }
            }
            // A `def`'s inferred type is its value, walked as its body.
            TyKind::Named { .. } | TyKind::Nat | TyKind::Ctx | TyKind::Splice { .. } | TyKind::TypeOf(_) => {}
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
            | ExprKind::Scaled(_)
            | ExprKind::Char(_)
            | ExprKind::Str(_)
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
                if let (ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix }, [l, r]) =
                    (&head.kind, args.as_slice())
                {
                    if symbol == "-" {
                        self.minus_between(l.span, r.span);
                    }
                }
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
            ExprKind::Dot { recv, tyargs, args, named, .. } => {
                if !tyargs.is_empty() {
                    self.list_spanned(
                        "expr-dot",
                        e.span,
                        tyargs[0].span,
                        tyargs[tyargs.len() - 1].span,
                    );
                }
                self.expr(recv);
                for t in tyargs {
                    self.ty(t);
                }
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
            ExprKind::RecordUpdate { base, fields } => {
                self.expr(base);
                for f in fields {
                    self.expr(&f.expr);
                }
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
        if let Some(e) = &p.default {
            self.expr(e);
        }
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
        // A section's type parameters lead a member's list but were written
        // in the section's head, before the member (`walk` locates that list).
        let own: Vec<&TyParam> = d.tyvars.iter().filter(|t| t.span.start >= d.span.start).collect();
        if let (Some(first), Some(last)) = (own.first(), own.last()) {
            self.list_spanned("decl-tyvars", d.span, first.span, last.span);
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
            Item::Generate(g) => self.expr(&g.generator),
            Item::Prefixed(p) => {
                self.expr(&p.generator);
                self.decl(&p.decl);
            }
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
                for k in c.kinds.iter().flatten() {
                    self.ty(k);
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
