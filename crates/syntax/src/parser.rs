//! Recursive-descent parser for the stage-1 grammar.
//!
//! ```text
//! file    := item*
//! item    := decl | inductive
//! decl    := "fn" name "(" params? ")" "->" type block
//!          | "theorem" name "(" params? ")" ":" type block
//! induct  := "inductive" name ("<" name ("," name)* ">")? "{" ctors? "}"
//! ctors   := ctor ("," ctor)* ","?
//! ctor    := name ("(" field ("," field)* ","? ")")?
//! field   := (name ":")? type
//! params  := param ("," param)* ","?
//! param   := name ":" type | "{" name ":" type "}"   -- implicit
//! type    := "(" name ":" type ")" "->" type         -- dependent function
//!          | tyatom "->" type                        -- right-associative
//!          | tyatom
//! tyatom  := "[" type ";" expr "]"                   -- length-indexed vector
//!          | name ("<" type ("," type)* ">")         -- applied inductive
//!          | expr ("=" expr)?       -- bare `Nat`/`Bool` is that type; `=` is
//!                                      propositional equality (`==` rejected)
//!          | "(" type ")"
//! block   := "{" stmt* expr on_stmt* "}"
//! stmt    := "let" name (":" type)? "=" expr ";"
//! on_stmt := "on" ("?" name ("." numeral)? | "_" ":" type) ":=" expr ";"
//! expr    := "match" expr ("as" name "->" type)? "{" arms "}"
//!          | "refl" | "?" name?
//!          | "j" "(" expr "," "(" name "," name ")" "->" type "," expr ")"
//!          | ("λ"|"fun") binder+ "=>" expr
//!          | "@" name "(" args ")"
//!          | atom (("." name)? "(" args ")")*      -- application is postfix
//!          | "[" (expr ("," expr)*)? "]"           -- vector literal
//!          | name | numeral | "(" expr ")"
//! binder  := name | "(" name ":" type ")"
//! arms    := arm ("," arm)* ","?    -- one per constructor, any order
//! arm     := name ("(" name ("," name)* ")")? "=>" expr
//! ```
//!
//! `on` discharges are trailing: order-free among themselves, but after the
//! result expression (issues/goal-holes.md). `let`/`on` are contextual
//! keywords like every other keyword here — an expression can never be
//! *continued* by a bare identifier, so a statement head is unambiguous.

use crate::ast::*;
use crate::lexer::{lex, Tok, TokKind};

#[derive(Debug, Clone)]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
}

pub fn parse_file(src: &str) -> Result<File, ParseError> {
    let toks = lex(src).map_err(|e| ParseError { msg: e.msg, span: e.span })?;
    let mut p = Parser { toks, pos: 0 };
    let mut items = Vec::new();
    while !p.at_eof() {
        items.push(p.item()?);
    }
    Ok(File { items })
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

type R<T> = Result<T, ParseError>;

/// `name(args…)` as an [`ExprKind::App`] with a `Var` head — what the operator
/// and `calc` desugarings build.
fn named_call(name: &str, args: Vec<Expr>, explicit: bool, span: Span) -> Expr {
    let head = Expr { kind: ExprKind::Var(name.to_string()), span };
    Expr { kind: ExprKind::App { head: Box::new(head), args, explicit }, span }
}

impl Parser {
    /// The token `k` positions ahead (`nth(0)` is [`Self::peek`]). Clamped to
    /// `Eof`, which the token stream always ends with.
    fn nth(&self, k: usize) -> &TokKind {
        let i = (self.pos + k).min(self.toks.len() - 1);
        &self.toks[i].kind
    }

    /// Is the parenthesised group at the current position a **type** rather
    /// than the start of an expression?
    ///
    /// In type position a leading `(` is ambiguous: `(A -> B) -> C` groups a
    /// type, while `(a + b) + c = d` opens the *expression* that is an
    /// equality's left endpoint. `->` is the discriminator, because it is not
    /// an expression operator — so the group is a type exactly when it
    /// contains a top-level `->` of its own, or is immediately followed by
    /// one. One scan, no backtracking.
    fn group_is_type(&self) -> bool {
        let mut depth = 0usize;
        let mut i = self.pos;
        while i < self.toks.len() {
            match self.toks[i].kind {
                TokKind::LParen => depth += 1,
                TokKind::Arrow if depth == 1 => return true,
                TokKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.nth(i + 1 - self.pos), TokKind::Arrow);
                    }
                }
                TokKind::Eof => break,
                _ => {}
            }
            i += 1;
        }
        false
    }

    fn peek(&self) -> &TokKind {
        &self.toks[self.pos].kind
    }

    fn peek_span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek(), TokKind::Eof)
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    fn err<T>(&self, msg: impl Into<String>) -> R<T> {
        Err(ParseError { msg: msg.into(), span: self.peek_span() })
    }

    fn expect(&mut self, kind: &TokKind, what: &str) -> R<Span> {
        if self.peek() == kind {
            Ok(self.bump().span)
        } else {
            self.err(format!("expected {what}, found {:?}", self.peek()))
        }
    }

    /// Accept an identifier token; keywords are contextual, so any ident
    /// works where a name is demanded.
    fn ident(&mut self, what: &str) -> R<(String, Span)> {
        match self.peek() {
            TokKind::Ident(s) => {
                let s = s.clone();
                let sp = self.bump().span;
                Ok((s, sp))
            }
            _ => self.err(format!("expected {what}, found {:?}", self.peek())),
        }
    }

    /// Is the next token the identifier `kw`?
    fn at_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), TokKind::Ident(s) if s == kw)
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    // -- declarations -------------------------------------------------------

    fn item(&mut self) -> R<Item> {
        if self.at_kw("inductive") {
            return Ok(Item::Inductive(self.inductive()?));
        }
        Ok(Item::Decl(self.decl()?))
    }

    /// `inductive D<p, …> { c(f: T, …), … }`. Zero constructors is legal (the
    /// empty type); so is a constructor with no field list.
    fn inductive(&mut self) -> R<InductiveDecl> {
        let start = self.peek_span();
        self.bump(); // `inductive`
        let (name, _) = self.ident("inductive name")?;
        let mut params = Vec::new();
        if matches!(self.peek(), TokKind::Lt) {
            self.bump();
            loop {
                params.push(self.ident("type parameter name")?.0);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::Gt, "`>` to close the type parameters")?;
        }
        self.expect(&TokKind::LBrace, "`{` (constructor list)")?;
        let mut ctors = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let (cname, cspan) = self.ident("constructor name")?;
            let mut fields = Vec::new();
            let mut span = cspan;
            if matches!(self.peek(), TokKind::LParen) {
                self.bump();
                while !matches!(self.peek(), TokKind::RParen) {
                    fields.push(self.field()?);
                    if !matches!(self.peek(), TokKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                span = span.join(self.expect(&TokKind::RParen, "`)` (field list)")?);
            }
            ctors.push(CtorDecl { name: cname, fields, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}` (constructor list)")?;
        Ok(InductiveDecl { name, params, ctors, span: start.join(end) })
    }

    /// A constructor field: `name: T` or a bare `T`. Named fields are in scope
    /// in the later fields' types.
    fn field(&mut self) -> R<FieldDecl> {
        let start = self.peek_span();
        // `name :` — but only when the `:` really follows, since a bare type
        // is also an identifier (`Nat`).
        let named = matches!(self.peek(), TokKind::Ident(_))
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Colon));
        let name = if named {
            let (n, _) = self.ident("field name")?;
            self.bump(); // `:`
            Some(n)
        } else {
            None
        };
        let ty = self.ty()?;
        let span = start.join(ty.span);
        Ok(FieldDecl { name, ty, span })
    }

    fn decl(&mut self) -> R<Decl> {
        let start = self.peek_span();
        let kind = if self.eat_kw("fn") {
            DeclKind::Fn
        } else if self.eat_kw("theorem") {
            DeclKind::Theorem
        } else {
            return self.err("expected `fn`, `theorem`, or `inductive`");
        };
        let (name, _) = self.ident("declaration name")?;
        self.expect(&TokKind::LParen, "`(`")?;
        let mut params = Vec::new();
        while !matches!(self.peek(), TokKind::RParen) {
            // `{name: T}` marks an implicit parameter (filled by unification);
            // `name: T` is explicit.
            let implicit = matches!(self.peek(), TokKind::LBrace);
            if implicit {
                self.bump();
            }
            let (pname, psp) = self.ident("parameter name")?;
            self.expect(&TokKind::Colon, "`:`")?;
            let ty = self.ty()?;
            let mut span = psp.join(ty.span);
            if implicit {
                span = span.join(self.expect(&TokKind::RBrace, "`}` to close implicit parameter")?);
            }
            params.push(Param { name: pname, ty, implicit, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::RParen, "`)`")?;
        match kind {
            DeclKind::Fn => {
                self.expect(&TokKind::Arrow, "`->`")?;
            }
            DeclKind::Theorem => {
                self.expect(&TokKind::Colon, "`:`")?;
            }
        }
        let result = self.ty()?;
        let body = self.block()?;
        let span = start.join(body.span);
        Ok(Decl { kind, name, params, result, body, span })
    }

    // -- blocks and statements ----------------------------------------------

    fn block(&mut self) -> R<Block> {
        let open = self.expect(&TokKind::LBrace, "`{`")?;
        let mut stmts = Vec::new();
        while self.at_kw("let") {
            stmts.push(self.let_stmt()?);
        }
        if self.at_kw("on") {
            return self
                .err("a block's `on` discharges come after its result expression");
        }
        let result = self.expr()?;
        let mut ons = Vec::new();
        while self.at_kw("on") {
            ons.push(self.on_stmt()?);
        }
        let close = self.expect(&TokKind::RBrace, "`}`")?;
        Ok(Block { stmts, result: Box::new(result), ons, span: open.join(close) })
    }

    /// `let x = e;` / `let x: T = e;`. The `=` here is the same `=` as the
    /// equality type former ([`Self::expect_eq`]); `let p: a = b = pf;` parses
    /// because `=` is not an expression operator, so `ty()` stops after `a = b`.
    fn let_stmt(&mut self) -> R<Stmt> {
        let start = self.bump().span; // `let`
        let (name, _) = self.ident("`let` binding name")?;
        let ty = if matches!(self.peek(), TokKind::Colon) {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        self.expect_eq("`let` binding")?;
        let expr = self.expr()?;
        let end = self.expect(&TokKind::Semi, "`;` to end the `let`")?;
        Ok(Stmt::Let { name, ty, expr, span: start.join(end) })
    }

    fn on_stmt(&mut self) -> R<OnStmt> {
        let start = self.bump().span; // `on`
        let target = match self.peek().clone() {
            TokKind::Hole(Some(name)) => {
                self.bump();
                // `?bound.1` — the checker's ordinal suffix for a deduplicated
                // default name. Only a numeral follows; `.f(…)` is a method
                // call, which a goal name never carries.
                let mut name = name;
                if matches!(self.peek(), TokKind::Dot)
                    && let Some(TokKind::Num(n)) = self.toks.get(self.pos + 1).map(|t| &t.kind)
                {
                    name = format!("{name}.{n}");
                    self.bump();
                    self.bump();
                }
                OnTarget::Name(name)
            }
            TokKind::Hole(None) => {
                return self.err(
                    "`on ?` needs a goal name; write `on _: P := …` to discharge by statement",
                )
            }
            _ if self.at_kw("_") => {
                self.bump();
                self.expect(&TokKind::Colon, "`:` (discharge by statement)")?;
                OnTarget::Stmt(self.ty()?)
            }
            _ => return self.err("expected `?name` or `_: P` after `on`"),
        };
        self.expect(&TokKind::ColonEq, "`:=` (goal discharge)")?;
        let expr = self.expr()?;
        let end = self.expect(&TokKind::Semi, "`;` to end the `on`")?;
        Ok(OnStmt { target, expr, span: start.join(end) })
    }

    // -- types --------------------------------------------------------------

    /// Consume the equality operator `=`. Heather merges binding and equality
    /// onto one `=` (ML-style, disambiguated by `let`; issues/surface-syntax.md);
    /// `==` is lexed but not part of the grammar, so it gets a targeted hint
    /// where equality is expected (`a = b`, calc steps) — catching C/Rust habit.
    fn expect_eq(&mut self, what: &str) -> R<()> {
        if matches!(self.peek(), TokKind::EqEq) {
            return self.err(format!("`==` is not used in Heather; write `=` ({what})"));
        }
        self.expect(&TokKind::Eq, "`=`")?;
        Ok(())
    }

    /// Types, arrow-aware. `->` is right-associative, and a *binder-headed*
    /// group `(x: A) -> B` makes it dependent
    /// (docs/surface-function-types.md §3.1).
    ///
    /// The arrow check has to live above [`Self::ty_atom`] rather than inside
    /// it: `ty_atom`'s `D<A>` case returns early, so folding the arrow into it
    /// would silently drop the `-> B` of `D<A> -> B`.
    fn ty(&mut self) -> R<Ty> {
        // `(x: A) -> B`. Three-token lookahead; `:` is not in the expression
        // grammar, so a binder-headed group cannot be anything else.
        if matches!(self.peek(), TokKind::LParen)
            && matches!(self.nth(1), TokKind::Ident(_))
            && matches!(self.nth(2), TokKind::Colon)
        {
            let start = self.bump().span; // `(`
            let (name, _) = self.ident("binder name")?;
            self.expect(&TokKind::Colon, "`:`")?;
            let dom = self.ty()?;
            self.expect(&TokKind::RParen, "`)` to close the binder")?;
            self.expect(&TokKind::Arrow, "`->` after a function-type binder")?;
            let cod = self.ty()?;
            let span = start.join(cod.span);
            return Ok(Ty {
                kind: TyKind::Fn {
                    binder: Some(name),
                    dom: Box::new(dom),
                    cod: Box::new(cod),
                },
                span,
            });
        }
        // `{x: A} -> B` — diagnosed rather than parsed
        // (issues/implicit-binders-in-function-types.md).
        if matches!(self.peek(), TokKind::LBrace)
            && matches!(self.nth(1), TokKind::Ident(_))
            && matches!(self.nth(2), TokKind::Colon)
        {
            return self.err(
                "implicit binders are not supported in function types yet: \
                 implicitness is a property of a declaration's parameters \
                 (see issues/implicit-binders-in-function-types.md)",
            );
        }
        let lhs = self.ty_atom()?;
        if matches!(self.peek(), TokKind::Arrow) {
            self.bump();
            let cod = self.ty()?; // right-associative
            let span = lhs.span.join(cod.span);
            return Ok(Ty {
                kind: TyKind::Fn { binder: None, dom: Box::new(lhs), cod: Box::new(cod) },
                span,
            });
        }
        Ok(lhs)
    }

    /// A type with no top-level arrow.
    fn ty_atom(&mut self) -> R<Ty> {
        // `( ty )` — needed so `(A -> B) -> C` groups. Guarded by
        // `group_is_type`, because in type position a leading `(` far more
        // often opens an *expression*: `(a + b) + c = a + (b + c)` is a type,
        // but every parenthesis in it is an arithmetic one.
        if matches!(self.peek(), TokKind::LParen) && self.group_is_type() {
            let start = self.bump().span;
            let inner = self.ty()?;
            let end = self.expect(&TokKind::RParen, "`)`")?;
            return Ok(Ty { kind: inner.kind, span: start.join(end) });
        }
        // `[T; n]` — a length-indexed vector (docs/container-fields.md §2.1).
        if matches!(self.peek(), TokKind::LBracket) {
            let start = self.bump().span;
            let elem = self.ty()?;
            self.expect(&TokKind::Semi, "`;` (a vector type is `[T; n]`)")?;
            let len = self.expr()?;
            let end = self.expect(&TokKind::RBracket, "`]`")?;
            return Ok(Ty {
                kind: TyKind::Vec { elem: Box::new(elem), len: Box::new(len) },
                span: start.join(end),
            });
        }
        // `D<A, B>` — an applied inductive. Unambiguous: `<` is the `lt`
        // operator only in *expression* position, and no expression is a type.
        if matches!(self.peek(), TokKind::Ident(_))
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Lt))
        {
            let (name, start) = self.ident("type name")?;
            self.bump(); // `<`
            let mut args = Vec::new();
            loop {
                args.push(self.ty()?);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            let end = self.expect(&TokKind::Gt, "`>` to close the type arguments")?;
            return Ok(Ty { kind: TyKind::Named { name, args }, span: start.join(end) });
        }
        let lhs = self.expr()?;
        if matches!(self.peek(), TokKind::Eq | TokKind::EqEq) {
            self.expect_eq("equality type `a = b`")?;
            let rhs = self.expr()?;
            let span = lhs.span.join(rhs.span);
            return Ok(Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rhs)), span });
        }
        // A bare name in type position is `Nat` or a declared type; whether the
        // name is in fact a type is the elaborator's call, not the grammar's.
        match &lhs.kind {
            ExprKind::Var(s) if s == "Nat" => Ok(Ty { kind: TyKind::Nat, span: lhs.span }),
            ExprKind::Var(s) => Ok(Ty {
                kind: TyKind::Named { name: s.clone(), args: vec![] },
                span: lhs.span,
            }),
            _ => Err(ParseError {
                msg: "expected a type (`Nat`, a declared type, or `a = b`)".into(),
                span: lhs.span,
            }),
        }
    }

    // -- expressions --------------------------------------------------------

    /// Expressions, with infix operators. Note `=` is *not* an expression
    /// operator: it is the identity-type former, parsed by [`Self::ty`] and by
    /// `calc` steps. Precedence, loosest to tightest: `<` (→ `lt`), `+`
    /// (→ `add`), `*` (→ `mul`), then postfix `.method(args)` / calls, then
    /// atoms. Each infix operator desugars to an ordinary [`ExprKind::Call`]
    /// on a fixed name table (issues/surface-operators.md — the decorated
    /// `+_Z` grammar and trait hookup arrive with the real trait design).
    fn expr(&mut self) -> R<Expr> {
        self.expr_bp(0)
    }

    /// Binding powers for the infix operators. `(name, left_bp, right_bp)`;
    /// `right_bp > left_bp` makes every operator left-associative.
    fn infix_op(tok: &TokKind) -> Option<(&'static str, u8, u8)> {
        match tok {
            TokKind::Lt => Some(("lt", 1, 2)),
            TokKind::Plus => Some(("add", 3, 4)),
            TokKind::Star => Some(("mul", 5, 6)),
            _ => None,
        }
    }

    /// Precedence-climbing loop: parse a postfix expression, then fold in
    /// infix operators whose left binding power is at least `min_bp`.
    fn expr_bp(&mut self, min_bp: u8) -> R<Expr> {
        let mut lhs = self.postfix()?;
        while let Some((name, l_bp, r_bp)) = Self::infix_op(self.peek()) {
            if l_bp < min_bp {
                break;
            }
            self.bump();
            let rhs = self.expr_bp(r_bp)?;
            let span = lhs.span.join(rhs.span);
            lhs = named_call(name, vec![lhs, rhs], false, span);
        }
        Ok(lhs)
    }

    /// An atom followed by zero or more method calls `.f(args)`. A method call
    /// desugars to `f(args…, receiver)` — the receiver is the *last* argument,
    /// so with stage-2 implicit endpoints (issues/elab-stage2-metas.md) the
    /// earlier implicit parameters are inferred from it (`p.sym()` ⇒ `sym(p)`,
    /// `add_succ(n, k).sym()` ⇒ `sym(add_succ(n, k))`).
    /// …and by zero or more applications `(args)`, so the head of a call can
    /// be any expression: `g(a)(b)`, `(λ x => x)(3)`
    /// (docs/surface-function-types.md §1.3).
    fn postfix(&mut self) -> R<Expr> {
        let mut e = self.atom()?;
        loop {
            match self.peek() {
                TokKind::Dot => {
                    self.bump();
                    let (method, _) = self.ident("method name")?;
                    self.expect(&TokKind::LParen, "`(` (method call)")?;
                    let (mut args, end) = self.call_args()?;
                    let span = e.span.join(end);
                    args.push(e);
                    let head = Expr { kind: ExprKind::Var(method), span };
                    e = Expr {
                        kind: ExprKind::App { head: Box::new(head), args, explicit: false },
                        span,
                    };
                }
                TokKind::LParen => {
                    self.bump();
                    let (args, end) = self.call_args()?;
                    let span = e.span.join(end);
                    e = Expr {
                        kind: ExprKind::App { head: Box::new(e), args, explicit: false },
                        span,
                    };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    /// A primary expression: keyword forms (`match`/`refl`/`j`/`calc`), an
    /// `@`- or plain call, a variable, a numeral, or a parenthesised group.
    fn atom(&mut self) -> R<Expr> {
        let start = self.peek_span();
        if self.at_kw("match") {
            return self.match_expr();
        }
        if self.at_kw("calc") {
            return self.calc_expr();
        }
        if self.at_kw("refl") {
            self.bump();
            return Ok(Expr { kind: ExprKind::Refl, span: start });
        }
        if self.at_kw("j") {
            return self.j_expr();
        }
        if matches!(self.peek(), TokKind::Lambda) || self.at_kw("fun") {
            return self.lambda();
        }
        // `@f(args)` — a fully-explicit call (implicit params given
        // positionally). Stays an atom-level *named* form rather than a
        // prefix on any application: `@` suppresses implicit-argument
        // insertion, which is name-directed, so on a non-name there is
        // nothing to suppress (docs/surface-function-types.md §1.3).
        if matches!(self.peek(), TokKind::At) {
            let at = self.bump().span;
            let (name, nsp) = self.ident("call head after `@`")?;
            self.expect(&TokKind::LParen, "`(` (`@` marks a call)")?;
            let (args, end) = self.call_args()?;
            let head = Expr { kind: ExprKind::Var(name), span: nsp };
            return Ok(Expr {
                kind: ExprKind::App { head: Box::new(head), args, explicit: true },
                span: at.join(end),
            });
        }
        // `[a, b, c]` — a vector literal (docs/container-fields.md §2.2).
        if matches!(self.peek(), TokKind::LBracket) {
            let open = self.bump().span;
            let mut elems = Vec::new();
            while !matches!(self.peek(), TokKind::RBracket) {
                elems.push(self.expr()?);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            let close = self.expect(&TokKind::RBracket, "`]` (vector literal)")?;
            return Ok(Expr { kind: ExprKind::VecLit(elems), span: open.join(close) });
        }
        match self.peek().clone() {
            TokKind::Hole(name) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Hole(name), span: sp })
            }
            TokKind::Num(n) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Num(n), span: sp })
            }
            TokKind::LParen => {
                self.bump();
                let e = self.expr()?;
                self.expect(&TokKind::RParen, "`)`")?;
                Ok(e)
            }
            // Application is postfix now, so a bare name is just a name;
            // `f(a)` is assembled by `postfix`.
            TokKind::Ident(name) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Var(name), span: sp })
            }
            _ => self.err("expected an expression"),
        }
    }

    /// `λ (x: A) (y: B) => e`, or `fun` for the ASCII spelling. Multiple
    /// binders are sugar for nesting. The body is parsed at binding power 0,
    /// so it extends as far as it can and stops at `,` `)` `}` `;` — none of
    /// which are infix operators.
    fn lambda(&mut self) -> R<Expr> {
        let start = self.bump().span; // `λ` or `fun`
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                TokKind::Ident(_) => {
                    let (name, sp) = self.ident("lambda binder")?;
                    binders.push(LamBinder { name, ty: None, span: sp });
                }
                TokKind::LParen => {
                    let open = self.bump().span;
                    let (name, _) = self.ident("lambda binder")?;
                    self.expect(&TokKind::Colon, "`:` (annotated lambda binder)")?;
                    let ty = self.ty()?;
                    let close = self.expect(&TokKind::RParen, "`)`")?;
                    binders.push(LamBinder {
                        name,
                        ty: Some(ty),
                        span: open.join(close),
                    });
                }
                TokKind::LBrace => {
                    return self.err(
                        "implicit lambda binders are not supported yet \
                         (see issues/implicit-binders-in-function-types.md)",
                    )
                }
                _ => break,
            }
        }
        if binders.is_empty() {
            return self.err("a lambda needs at least one binder");
        }
        self.expect(&TokKind::FatArrow, "`=>` (a lambda's body follows `=>`)")?;
        let body = self.expr()?;
        let span = start.join(body.span);
        Ok(Expr { kind: ExprKind::Lam { binders, body: Box::new(body) }, span })
    }

    /// Parse a comma-separated argument list up to and including the closing
    /// `)` (the opening `(` is already consumed). Returns the args and the
    /// span of the `)`.
    fn call_args(&mut self) -> R<(Vec<Expr>, Span)> {
        let mut args = Vec::new();
        while !matches!(self.peek(), TokKind::RParen) {
            args.push(self.expr()?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RParen, "`)`")?;
        Ok((args, end))
    }

    fn match_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `match`
        let scrut = self.expr()?;
        let motive = if self.eat_kw("as") {
            let (bind, _) = self.ident("motive binder")?;
            self.expect(&TokKind::Arrow, "`->`")?;
            let m = self.ty()?;
            Some((bind, Box::new(m)))
        } else {
            None
        };
        self.expect(&TokKind::LBrace, "`{`")?;
        // Arms are `C(x, …) => body`, one per constructor. Which constructors
        // exist — and so whether the arms are complete, duplicated, or of the
        // wrong arity — is the elaborator's business: it knows the scrutinee's
        // type, and the grammar does not.
        let mut arms: Vec<Arm> = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let (ctor, cspan) = self.ident("constructor name in a `match` arm")?;
            let mut binders = Vec::new();
            if matches!(self.peek(), TokKind::LParen) {
                self.bump();
                while !matches!(self.peek(), TokKind::RParen) {
                    binders.push(self.ident("pattern binder")?.0);
                    if !matches!(self.peek(), TokKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                self.expect(&TokKind::RParen, "`)` (pattern binders)")?;
            }
            self.expect(&TokKind::FatArrow, "`=>`")?;
            let body = self.expr()?;
            let span = cspan.join(body.span);
            arms.push(Arm { ctor, binders, body, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        Ok(Expr {
            kind: ExprKind::Match { scrut: Box::new(scrut), motive, arms },
            span: start.join(end),
        })
    }

    fn j_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `j`
        self.expect(&TokKind::LParen, "`(`")?;
        let proof = self.expr()?;
        self.expect(&TokKind::Comma, "`,`")?;
        self.expect(&TokKind::LParen, "`(`")?;
        let (y, _) = self.ident("endpoint binder")?;
        self.expect(&TokKind::Comma, "`,`")?;
        let (p, _) = self.ident("path binder")?;
        self.expect(&TokKind::RParen, "`)`")?;
        self.expect(&TokKind::Arrow, "`->`")?;
        let motive = self.ty()?;
        self.expect(&TokKind::Comma, "`,`")?;
        let case = self.expr()?;
        let end = self.expect(&TokKind::RParen, "`)`")?;
        Ok(Expr {
            kind: ExprKind::J {
                proof: Box::new(proof),
                y,
                p,
                motive: Box::new(motive),
                case: Box::new(case),
            },
            span: start.join(end),
        })
    }

    /// `calc { e0 = e1 := p1 (, = e_i := p_i)* ,? }` — an equational chain
    /// (surface-v1 §1). Desugars to a right-nested `@trans` over the step
    /// proofs, carrying the step terms as the *explicit* endpoints so that
    /// `refl` steps still receive a checking type. Proves `e0 = e_last`;
    /// a single step is just its proof.
    fn calc_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `calc`
        self.expect(&TokKind::LBrace, "`{`")?;
        // The chain: terms[i] are the endpoints, proofs[i] : terms[i] = terms[i+1].
        // The first step carries both endpoints (`e0 = e1 := p1`); later steps
        // reuse the previous right endpoint (`= e_{i+1} := p_{i+1}`).
        let mut terms = vec![self.expr()?];
        let mut proofs = Vec::new();
        self.expect_eq("calc step")?;
        loop {
            terms.push(self.expr()?);
            self.expect(&TokKind::ColonEq, "`:=` (calc step proof)")?;
            proofs.push(self.expr()?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump(); // `,`
            if matches!(self.peek(), TokKind::RBrace) {
                break; // trailing comma
            }
            self.expect_eq("calc step")?;
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        let span = start.join(end);
        // Fold right: acc proves terms[i+1] = e_last; prepend step i.
        let m = proofs.len();
        let last = &terms[m];
        let mut acc = proofs[m - 1].clone();
        for i in (0..m - 1).rev() {
            acc = named_call(
                "trans",
                vec![
                    terms[i].clone(),
                    terms[i + 1].clone(),
                    last.clone(),
                    proofs[i].clone(),
                    acc,
                ],
                true,
                span,
            );
        }
        acc.span = span;
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The file's single `fn`/`theorem` declaration.
    fn only_decl(f: &File) -> &Decl {
        match &f.items[0] {
            Item::Decl(d) => d,
            other => panic!("expected a declaration, got {other:?}"),
        }
    }

    #[test]
    fn implicit_and_explicit_params() {
        let f = parse_file("theorem t({a: Nat}, b: Nat, p: a = b): b = a { refl }").unwrap();
        let ps = &only_decl(&f).params;
        assert_eq!(ps.len(), 3);
        assert!(ps[0].implicit, "`{{a}}` is implicit");
        assert!(!ps[1].implicit, "`b` is explicit");
        assert!(!ps[2].implicit, "`p` is explicit");
    }

    #[test]
    fn at_marks_a_fully_explicit_call() {
        let f = parse_file("fn f(n: Nat) -> Nat { @g(a, b, p) }").unwrap();
        match &only_decl(&f).body.result.kind {
            ExprKind::App { head, args, explicit } => {
                assert!(matches!(&head.kind, ExprKind::Var(n) if n == "g"));
                assert_eq!(args.len(), 3);
                assert!(*explicit);
            }
            other => panic!("expected an explicit call, got {other:?}"),
        }
    }

    #[test]
    fn plain_call_is_not_explicit() {
        let f = parse_file("fn f(n: Nat) -> Nat { g(a) }").unwrap();
        match &only_decl(&f).body.result.kind {
            ExprKind::App { explicit, .. } => assert!(!*explicit),
            other => panic!("expected a call, got {other:?}"),
        }
    }

    #[test]
    fn unclosed_implicit_param_errors() {
        assert!(parse_file("theorem t({a: Nat, b: Nat): a = b { refl }").is_err());
    }

    // Parse a single-declaration `fn f(n: Nat) -> Nat { <body> }` and return
    // the body kind, for exercising expression desugaring.
    fn body(src_body: &str) -> ExprKind {
        let src = format!("fn f(n: Nat) -> Nat {{ {src_body} }}");
        parse_file(&src).unwrap().items.remove(0).into_decl().body.result.kind
    }

    fn as_call(k: &ExprKind) -> (&str, &[Expr], bool) {
        match k {
            ExprKind::App { head, args, explicit } => match &head.kind {
                ExprKind::Var(name) => (name.as_str(), args.as_slice(), *explicit),
                other => panic!("expected a named call, got {other:?}"),
            },
            other => panic!("expected a call, got {other:?}"),
        }
    }

    #[test]
    fn operators_desugar_with_precedence() {
        // `a + b * c` ⇒ add(a, mul(b, c)); `*` binds tighter than `+`.
        let k = body("a + b * c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "add");
        assert_eq!(args.len(), 2);
        let (inner, iargs, _) = as_call(&args[1].kind);
        assert_eq!(inner, "mul");
        assert!(matches!(&iargs[0].kind, ExprKind::Var(v) if v == "b"));
    }

    #[test]
    fn addition_is_left_associative() {
        // `a + b + c` ⇒ add(add(a, b), c).
        let k = body("a + b + c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "add");
        assert_eq!(as_call(&args[0].kind).0, "add");
        assert!(matches!(&args[1].kind, ExprKind::Var(v) if v == "c"));
    }

    #[test]
    fn method_call_puts_receiver_last() {
        // `add_succ(n, k).sym()` ⇒ sym(add_succ(n, k)); receiver is last.
        let k = body("add_succ(n, k).sym()");
        let (name, args, explicit) = as_call(&k);
        assert_eq!(name, "sym");
        assert!(!explicit);
        assert_eq!(args.len(), 1);
        assert_eq!(as_call(&args[0].kind).0, "add_succ");
    }

    #[test]
    fn method_call_appends_receiver_after_args() {
        // `x.f(a, b)` ⇒ f(a, b, x).
        let k = body("x.f(a, b)");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "f");
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[2].kind, ExprKind::Var(v) if v == "x"));
    }

    #[test]
    fn calc_single_step_is_the_bare_proof() {
        // `calc { a = b := p }` ⇒ p.
        let k = body("calc { a = b := p }");
        assert!(matches!(&k, ExprKind::Var(v) if v == "p"));
    }

    #[test]
    fn calc_multi_step_nests_explicit_trans() {
        // `calc { a = b := p1, = c := p2 }` ⇒ @trans(a, b, c, p1, p2).
        let k = body("calc { a = b := p1, = c := p2 }");
        let (name, args, explicit) = as_call(&k);
        assert_eq!(name, "trans");
        assert!(explicit, "calc lowers to the explicit `@trans`");
        assert_eq!(args.len(), 5);
        assert!(matches!(&args[0].kind, ExprKind::Var(v) if v == "a"));
        assert!(matches!(&args[1].kind, ExprKind::Var(v) if v == "b"));
        assert!(matches!(&args[2].kind, ExprKind::Var(v) if v == "c"));
        assert!(matches!(&args[3].kind, ExprKind::Var(v) if v == "p1"));
        assert!(matches!(&args[4].kind, ExprKind::Var(v) if v == "p2"));
    }

    #[test]
    fn calc_three_steps_fold_right() {
        // `calc { a=b:=p1, =c:=p2, =d:=p3 }` ⇒ @trans(a,b,d,p1,@trans(b,c,d,p2,p3)).
        let k = body("calc { a = b := p1, = c := p2, = d := p3 }");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[2].kind, ExprKind::Var(v) if v == "d"), "shared right endpoint");
        let (inner, iargs, iexpl) = as_call(&args[4].kind);
        assert_eq!(inner, "trans");
        assert!(iexpl);
        assert!(matches!(&iargs[0].kind, ExprKind::Var(v) if v == "b"));
        assert!(matches!(&iargs[2].kind, ExprKind::Var(v) if v == "d"));
    }

    #[test]
    fn single_eq_is_the_equality_type_former() {
        // `a = b` in type position is the identity type (not an expression
        // operator — the elaborator never sees `=` as a Call).
        let f = parse_file("theorem t(a: Nat, b: Nat): a = b { refl }").unwrap();
        assert!(matches!(only_decl(&f).result.kind, crate::ast::TyKind::Eq(..)));
    }

    #[test]
    fn double_eq_is_rejected_with_a_hint() {
        // `==` is lexed but not grammatical; equality is `=`. The parser
        // rejects it with a targeted message (C/Rust muscle memory).
        let err = parse_file("theorem t(a: Nat, b: Nat): a == b { refl }").unwrap_err();
        assert!(err.msg.contains("=="), "hint should mention `==`: {}", err.msg);
        assert!(err.msg.contains('='), "hint should point at `=`: {}", err.msg);
    }

    // -- goal holes (issues/goal-holes.md) ----------------------------------

    fn decl_of(src: &str) -> Decl {
        parse_file(src).unwrap().items.remove(0).into_decl()
    }

    #[test]
    fn named_and_anonymous_holes_parse() {
        // Adjacency decides: `?p` is named, `? ` is anonymous. Both are atoms,
        // so they nest inside calls like any other expression.
        let k = body("f(?p, ?)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Hole(Some(n)) if n == "p"), "{:?}", args[0]);
        assert!(matches!(args[1].kind, ExprKind::Hole(None)), "{:?}", args[1]);
    }

    #[test]
    fn on_discharges_by_name_and_by_statement() {
        let d = decl_of(
            "theorem t(a: Nat, b: Nat): a = b {
                 ?first
                 on ?first := p;
                 on ?bound.1 := q;
                 on _: a = b := r;
             }",
        );
        assert_eq!(d.body.ons.len(), 3);
        match &d.body.ons[0].target {
            OnTarget::Name(n) => assert_eq!(n, "first"),
            other => panic!("expected a name target, got {other:?}"),
        }
        // The checker's ordinal suffix is part of the name, not a method call.
        match &d.body.ons[1].target {
            OnTarget::Name(n) => assert_eq!(n, "bound.1"),
            other => panic!("expected a name target, got {other:?}"),
        }
        assert!(matches!(d.body.ons[2].target, OnTarget::Stmt(_)));
    }

    #[test]
    fn let_binds_with_and_without_an_annotation() {
        let d = decl_of(
            "fn f(n: Nat) -> Nat {
                 let a = n;
                 let p: n = n = refl;
                 a
             }",
        );
        assert_eq!(d.body.stmts.len(), 2);
        let Stmt::Let { name, ty, .. } = &d.body.stmts[0];
        assert_eq!(name, "a");
        assert!(ty.is_none());
        // `let p: n = n = refl;` — `=` is not an expression operator, so the
        // annotation stops after `n = n` and the binding `=` follows.
        let Stmt::Let { name, ty, expr, .. } = &d.body.stmts[1];
        assert_eq!(name, "p");
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Eq(..))));
        assert!(matches!(expr.kind, ExprKind::Refl));
    }

    #[test]
    fn statements_need_semicolons() {
        assert!(parse_file("fn f(n: Nat) -> Nat { let a = n a }").is_err());
        assert!(parse_file("theorem t(n: Nat): n = n { ?p on ?p := refl }").is_err());
    }

    #[test]
    fn on_before_the_result_expression_is_rejected() {
        let err = parse_file("theorem t(n: Nat): n = n { on ?p := refl; ?p }").unwrap_err();
        assert!(err.msg.contains("result expression"), "{}", err.msg);
    }

    #[test]
    fn on_and_let_are_still_usable_as_names() {
        // Contextual keywords: an expression is never continued by a bare
        // identifier, so a statement head is unambiguous and these still parse.
        let k = body("add(on, let)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "on"));
        assert!(matches!(&args[1].kind, ExprKind::Var(n) if n == "let"));
    }
}
