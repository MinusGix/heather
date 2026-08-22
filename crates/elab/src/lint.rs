//! Registered source lints.
//!
//! A lint is identified here, run over the written AST after its owning item
//! has elaborated successfully, and emitted through the ordinary warning
//! channel. Keeping the registry separate from elaboration is what lets a
//! source-style rule be added without burying another condition in a typing
//! path. Semantic lints may still be raised where their analysis lives, but
//! use the same [`Lint`] identity.

use heather_syntax::lexer::{lex, Tok, TokKind};
use heather_syntax::{
    Block, ClassRef, DatareprBody, Decl, Expr, ExprKind, FieldDecl, InstanceBody, Item, Param,
    MatchForm, Span, Stmt, Ty, TyKind,
};

/// Which project-specific source conventions should accompany the general
/// correctness and readability lints. The default profile deliberately says
/// nothing about whether a downstream project prefers ASCII or Unicode.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum LintProfile {
    #[default]
    Default,
    Stdlib,
}

/// Stable identity of a non-fatal lint diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Lint {
    /// A written pattern arm has no constructor cases left to reach it.
    UnreachableMatchArm,
    /// `λ x h => (match x as … { … })(h)` can usually put the match in
    /// checking position by moving `h` into its result.
    MatchFunctionApplication,
    /// Whitespace after prefix negation makes it read unlike an operator.
    TightNegationSpacing,
    /// Heather's own library uses the canonical mathematical spellings.
    StdlibUnicodeSpelling,
    /// Consecutive calls of a directly named function can use one argument list.
    NestedCall,
    /// A constructor-pattern binder is named but not read by its arm.
    UnusedPatternBinder,
    /// Written notation selected a compatibility basename after missing a designation.
    OperatorFallback,
    /// An explicit match motive can be omitted in its checking position.
    RedundantMatchMotive,
}

impl Lint {
    /// Stable kebab-case name for diagnostics, tests, and future allow/deny
    /// configuration. Adding configuration does not have to parse messages.
    pub fn name(self) -> &'static str {
        match self {
            Self::UnreachableMatchArm => "unreachable-match-arm",
            Self::MatchFunctionApplication => "match-function-application",
            Self::TightNegationSpacing => "tight-negation-spacing",
            Self::StdlibUnicodeSpelling => "stdlib-unicode-spelling",
            Self::NestedCall => "nested-call",
            Self::UnusedPatternBinder => "unused-pattern-binder",
            Self::OperatorFallback => "operator-fallback",
            Self::RedundantMatchMotive => "redundant-match-motive",
        }
    }
}

pub(crate) struct Finding {
    pub lint: Lint,
    pub msg: String,
    pub span: heather_syntax::Span,
    pub fix: Option<crate::LintFix>,
}

/// Lexed once per file and shared by every lint and successfully elaborated
/// item in it. Source lints should not each invent a comment/string scanner.
pub(crate) struct Source<'a> {
    text: &'a str,
    toks: Vec<Tok>,
    profile: LintProfile,
}

impl<'a> Source<'a> {
    pub fn new(text: &'a str, profile: LintProfile) -> Self {
        // `Source` is built only after `parse_file` succeeded, so lexing the
        // exact same bytes cannot fail.
        let toks = lex(text).expect("parsed source must lex");
        Self { text, toks, profile }
    }

    fn written(&self, span: Span) -> &'a str {
        &self.text[span.start..span.end]
    }

    fn item_tokens(&self, item: &Item) -> impl Iterator<Item = &Tok> {
        let span = item_span(item);
        let first = self.toks.partition_point(|t| t.span.end <= span.start);
        self.toks[first..]
            .iter()
            .take_while(move |t| t.span.end <= span.end)
            .filter(move |t| t.span.start >= span.start)
    }

    pub fn complete_motive_fix(&self, item: &Item, partial: Span) -> Option<Span> {
        let item = item_span(item);
        if partial.start < item.start || partial.end > item.end {
            return None;
        }
        let brace = self
            .toks
            .iter()
            .find(|t| t.span.start >= partial.end && matches!(t.kind, TokKind::LBrace))?;
        Some(Span { start: partial.start, end: brace.span.start })
    }
}

#[derive(Clone, Copy)]
struct ExprContext {
    is_app_head: bool,
}

type ExprLint = fn(&Expr, ExprContext, &mut Vec<Finding>);
type SourceLint = fn(&Item, &Source<'_>, &mut Vec<Finding>);

/// The registry. A source-expression lint is one function and one row; the
/// shared total walker supplies nesting, item ownership, and deterministic
/// source order.
const EXPR_LINTS: &[ExprLint] =
    &[match_function_application, nested_call, unused_pattern_binders];
const SOURCE_LINTS: &[SourceLint] = &[tight_negation_spacing, stdlib_unicode_spelling];

pub(crate) fn check_item(item: &Item, source: &Source<'_>) -> Vec<Finding> {
    let mut out = Vec::new();
    for lint in SOURCE_LINTS {
        lint(item, source, &mut out);
    }
    match item {
        Item::Decl(d) => decl(d, &mut out),
        Item::Inductive(i) => {
            i.valparams.iter().for_each(|p| param(p, &mut out));
            i.ctors.iter().for_each(|c| {
                c.fields.iter().for_each(|f| field(f, &mut out));
                c.result.iter().for_each(|e| expr(e, &mut out));
            });
            i.index.iter().for_each(|t| ty(t, &mut out));
        }
        Item::Class(c) => {
            c.valparams.iter().for_each(|p| param(p, &mut out));
            c.extends.iter().for_each(|r| class_ref(r, &mut out));
            c.fields.iter().for_each(|f| field(f, &mut out));
        }
        Item::Instance(i) => {
            i.valparams.iter().for_each(|p| param(p, &mut out));
            class_ref(&i.class, &mut out);
            i.requires.iter().for_each(|p| param(p, &mut out));
            match &i.body {
                InstanceBody::Block(ds) => ds.iter().for_each(|d| decl(d, &mut out)),
                InstanceBody::Literal(fs) => fs.iter().for_each(|f| expr(&f.expr, &mut out)),
            }
        }
        Item::Designation(d) => {
            ty(&d.carrier, &mut out);
            expr(&d.op, &mut out);
        }
        Item::Datarepr(d) => {
            ty(&d.spec, &mut out);
            datarepr_body(&d.body, &mut out);
        }
        Item::Impl(i) => datarepr_body(&i.body, &mut out),
        Item::Import(_) => {}
    }
    out
}

fn decl(d: &Decl, out: &mut Vec<Finding>) {
    d.params.iter().for_each(|p| param(p, out));
    ty(&d.result, out);
    block(&d.body, out);
}

fn param(p: &Param, out: &mut Vec<Finding>) {
    ty(&p.ty, out);
}

fn field(f: &FieldDecl, out: &mut Vec<Finding>) {
    ty(&f.ty, out);
}

fn class_ref(r: &ClassRef, out: &mut Vec<Finding>) {
    r.args.iter().for_each(|t| ty(t, out));
    r.index.iter().for_each(|e| expr(e, out));
}

fn datarepr_body(body: &DatareprBody, out: &mut Vec<Finding>) {
    match body {
        DatareprBody::Fields(fs) => fs.iter().for_each(|f| expr(&f.expr, out)),
        DatareprBody::Mint(e) => expr(e, out),
    }
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
    expr_with_context(e, ExprContext { is_app_head: false }, out);
}

fn expr_with_context(e: &Expr, context: ExprContext, out: &mut Vec<Finding>) {
    for lint in EXPR_LINTS {
        lint(e, context, out);
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
            expr_with_context(head, ExprContext { is_app_head: true }, out);
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

fn match_function_application(e: &Expr, _context: ExprContext, out: &mut Vec<Finding>) {
    let ExprKind::Lam { binders, body } = &e.kind else { return };
    let ExprKind::App { head, args, named, explicit, .. } = &body.kind else { return };
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
        fix: None,
    });
}

fn nested_call(e: &Expr, context: ExprContext, out: &mut Vec<Finding>) {
    if context.is_app_head {
        return;
    }
    let ExprKind::App { head, args, named, explicit, .. } = &e.kind else { return };
    if *explicit || args.is_empty() || !named.is_empty() {
        return;
    }
    let ExprKind::App {
        head: inner_head,
        args: inner_args,
        named: inner_named,
        explicit: inner_explicit,
        ..
    } = &head.kind
    else {
        return;
    };
    if *inner_explicit || inner_args.is_empty() || !inner_named.is_empty() {
        return;
    }
    // Keep this a surface-equivalent rewrite, not advice to inline a computed
    // function value. Type applications still have a directly named callee.
    let mut callee = inner_head.as_ref();
    while let ExprKind::TyApp { head, .. } = &callee.kind {
        callee = head;
    }
    if !matches!(callee.kind, ExprKind::Var(_)) {
        return;
    }
    out.push(Finding {
        lint: Lint::NestedCall,
        msg: "consecutive calls to the same function can use one argument list; write `f(a, b)` instead of `f(a)(b)`".into(),
        span: e.span,
        fix: None,
    });
}

fn unused_pattern_binders(e: &Expr, _context: ExprContext, out: &mut Vec<Finding>) {
    let ExprKind::Match { form, generated: false, arms, eqbind, .. } = &e.kind else { return };
    if !matches!(form, MatchForm::Match | MatchForm::Split) {
        return;
    }
    for arm in arms {
        let mut uses = BinderUses::default();
        let mut written = Vec::new();
        for (field, pat) in arm.binders.iter().enumerate() {
            uses.bind_pattern(pat, &mut written, arm.ctor == "Succ" && field == 1);
        }
        if let Some(name) = eqbind {
            uses.bind_shadow(name);
        }
        uses.expr(&arm.body);
        for binder in written {
            // Before semantic pattern preparation, a bare nested constructor
            // is represented by the same node as a binder. Constructor names
            // are capitalized by Heather's declaration grammar/style; staying
            // silent on capitalized binders is the conservative side of that
            // erased distinction.
            if binder.name == "_"
                || binder.name.starts_with('#')
                || binder.name.chars().next().is_some_and(char::is_uppercase)
                || uses.used.contains(&binder.id)
            {
                continue;
            }
            out.push(Finding {
                lint: Lint::UnusedPatternBinder,
                msg: if binder.induction_hypothesis {
                    format!(
                        "induction hypothesis `{}` is not used; write `_` here, or consider whether this proof only needs case analysis",
                        binder.name,
                    )
                } else {
                    format!(
                        "constructor payload `{}` is not used in this arm; write `_` instead",
                        binder.name,
                    )
                },
                span: binder.span,
                fix: Some(crate::LintFix { span: binder.span, replacement: "_".into() }),
            });
        }
    }
}

struct WrittenBinder {
    id: usize,
    name: String,
    span: Span,
    induction_hypothesis: bool,
}

/// A small lexical resolver for linting binding identities. Each environment
/// entry is either a pattern binder's id or `None` for a shadowing binder from
/// a lambda, local declaration, or nested pattern. This is deliberately not a
/// text search: `λ x => x` inside an arm must not make the arm's `x` look used.
#[derive(Default)]
struct BinderUses {
    env: Vec<(String, Option<usize>)>,
    used: std::collections::HashSet<usize>,
    next_id: usize,
}

impl BinderUses {
    fn bind_pattern(
        &mut self,
        pat: &heather_syntax::Pat,
        written: &mut Vec<WrittenBinder>,
        induction_hypothesis: bool,
    ) {
        match pat {
            heather_syntax::Pat::Var { name, span } => {
                let id = self.next_id;
                self.next_id += 1;
                self.env.push((name.clone(), Some(id)));
                written.push(WrittenBinder {
                    id,
                    name: name.clone(),
                    span: *span,
                    induction_hypothesis,
                });
            }
            heather_syntax::Pat::Ctor { args, .. } => {
                for p in args {
                    self.bind_pattern(p, written, false);
                }
            }
            heather_syntax::Pat::Named { pat, .. } => {
                self.bind_pattern(pat, written, induction_hypothesis)
            }
        }
    }

    fn bind_shadow(&mut self, name: &str) {
        self.env.push((name.into(), None));
    }

    fn mark(&mut self, name: &str) {
        if let Some((_, Some(id))) = self.env.iter().rev().find(|(bound, _)| bound == name) {
            self.used.insert(*id);
        }
    }

    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let mark = self.env.len();
        f(self);
        self.env.truncate(mark);
    }

    fn ty(&mut self, t: &Ty) {
        match &t.kind {
            TyKind::Nat
            | TyKind::Univ { .. }
            | TyKind::Ctx
            | TyKind::TyCode { .. }
            | TyKind::Splice { .. } => {}
            TyKind::Eq(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            TyKind::OfExpr(e) | TyKind::Fin(e) => self.expr(e),
            TyKind::Named { args, .. } => args.iter().for_each(|a| self.ty(a)),
            TyKind::Vec { elem, len } => {
                self.ty(elem);
                self.expr(len);
            }
            TyKind::Fn { binder, dom, cod, .. } => {
                self.ty(dom);
                self.scoped(|this| {
                    if let Some(name) = binder {
                        this.bind_shadow(name);
                    }
                    this.ty(cod);
                });
            }
            TyKind::Code { ty, .. } => self.ty(ty),
        }
    }

    fn block(&mut self, b: &Block) {
        self.scoped(|this| {
            for stmt in &b.stmts {
                match stmt {
                    Stmt::Let { name, ty, expr, .. } => {
                        ty.iter().for_each(|t| this.ty(t));
                        this.expr(expr);
                        this.bind_shadow(name);
                    }
                    Stmt::LetRecord { fields, expr, .. } => {
                        this.expr(expr);
                        for f in fields {
                            for name in pattern_names(&f.pat) {
                                this.bind_shadow(name);
                            }
                        }
                    }
                    Stmt::LetCode { name, expr, .. } => {
                        this.expr(expr);
                        this.bind_shadow(name);
                    }
                }
            }
            this.expr(&b.result);
            for on in &b.ons {
                if let heather_syntax::OnTarget::Stmt(t) = &on.target {
                    this.ty(t);
                }
                this.expr(&on.expr);
            }
        });
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Var(name) => self.mark(name),
            ExprKind::OpSymbol { .. }
            | ExprKind::Univ { .. }
            | ExprKind::Num(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl
            | ExprKind::Hole(_) => {}
            ExprKind::TyLit(t) => self.ty(t),
            ExprKind::App { head, args, named, .. } => {
                self.expr(head);
                args.iter().for_each(|a| self.expr(a));
                named.iter().for_each(|a| self.expr(&a.expr));
            }
            ExprKind::TyApp { head, args } => {
                self.expr(head);
                args.iter().for_each(|a| self.ty(a));
            }
            ExprKind::Lam { binders, body } => self.scoped(|this| {
                for binder in binders {
                    binder.ty.iter().for_each(|t| this.ty(t));
                    this.bind_shadow(&binder.name);
                }
                this.expr(body);
            }),
            ExprKind::VecLit(xs) => xs.iter().for_each(|x| self.expr(x)),
            ExprKind::Eq(a, b) | ExprKind::Index { recv: a, idx: b } => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Match { scrut, motive, arms, eqbind, .. } => {
                self.expr(scrut);
                motive.iter().for_each(|m| self.expr(m));
                for arm in arms {
                    self.scoped(|this| {
                        let mut ignored = Vec::new();
                        arm.binders.iter().for_each(|p| this.bind_pattern(p, &mut ignored, false));
                        if let Some(name) = eqbind {
                            this.bind_shadow(name);
                        }
                        this.expr(&arm.body);
                    });
                }
            }
            ExprKind::MatchCode { scrut, motive, arms } => {
                self.expr(scrut);
                self.ty(motive);
                for arm in arms {
                    self.scoped(|this| {
                        let mut ignored = Vec::new();
                        arm.binders
                            .iter()
                            .for_each(|p| this.bind_pattern(p, &mut ignored, false));
                        this.expr(&arm.body);
                    });
                }
            }
            ExprKind::Dot { recv, args, named, .. } => {
                self.expr(recv);
                args.iter().flatten().for_each(|a| self.expr(a));
                named.iter().for_each(|a| self.expr(&a.expr));
            }
            ExprKind::RecordLit { tyargs, fields, .. } => {
                tyargs.iter().for_each(|t| self.ty(t));
                fields.iter().for_each(|f| self.expr(&f.expr));
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

fn pattern_names(pat: &heather_syntax::Pat) -> Vec<&str> {
    match pat {
        heather_syntax::Pat::Var { name, .. } => vec![name],
        heather_syntax::Pat::Ctor { args, .. } => args.iter().flat_map(pattern_names).collect(),
        heather_syntax::Pat::Named { pat, .. } => pattern_names(pat),
    }
}

fn tight_negation_spacing(item: &Item, source: &Source<'_>, out: &mut Vec<Finding>) {
    let toks = source.item_tokens(item).collect::<Vec<_>>();
    for pair in toks.windows(2) {
        let [neg, next] = pair else { unreachable!() };
        if !matches!(neg.kind, TokKind::Neg) || next.span.start == neg.span.end {
            continue;
        }
        let gap = &source.text[neg.span.end..next.span.start];
        // Comments are lexically skipped too, but deleting one is never a
        // spacing fix. Only diagnose a gap made entirely of whitespace.
        if gap.chars().all(char::is_whitespace) {
            out.push(Finding {
                lint: Lint::TightNegationSpacing,
                msg: "prefix negation is written tightly; remove the space after `¬`".into(),
                span: Span { start: neg.span.start, end: next.span.start },
                fix: Some(crate::LintFix {
                    span: Span { start: neg.span.end, end: next.span.start },
                    replacement: String::new(),
                }),
            });
        }
    }
}

fn stdlib_unicode_spelling(item: &Item, source: &Source<'_>, out: &mut Vec<Finding>) {
    if source.profile != LintProfile::Stdlib {
        return;
    }
    for tok in source.item_tokens(item) {
        let replacement = match (&tok.kind, source.written(tok.span)) {
            (TokKind::Arrow, "->") => Some("→"),
            (TokKind::Iff, "<->") => Some("↔"),
            (TokKind::Turnstile, "|-") => Some("⊢"),
            (TokKind::Ident(name), "fun") if name == "fun" => Some("λ"),
            _ => None,
        };
        if let Some(replacement) = replacement {
            out.push(Finding {
                lint: Lint::StdlibUnicodeSpelling,
                msg: format!(
                    "the standard library uses the canonical Unicode spelling; replace `{}` with `{replacement}`",
                    source.written(tok.span),
                ),
                span: tok.span,
                fix: Some(crate::LintFix {
                    span: tok.span,
                    replacement: replacement.into(),
                }),
            });
        }
    }
}

fn item_span(item: &Item) -> Span {
    match item {
        Item::Decl(x) => x.span,
        Item::Inductive(x) => x.span,
        Item::Class(x) => x.span,
        Item::Instance(x) => x.span,
        Item::Designation(x) => x.span,
        Item::Datarepr(x) => x.span,
        Item::Impl(x) => x.span,
        Item::Import(x) => x.span,
    }
}
