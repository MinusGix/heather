//! Recursive-descent parser for the stage-1 grammar.
//!
//! ```text
//! file    := item*
//! item    := decl | inductive | record
//! decl    := "fn" name tyvars? "(" params? ")" "->" type block
//!          | "theorem" name tyvars? "(" params? ")" ":" type block
//! tyvars  := "<" tyvar ("," tyvar)* ">"
//! tyvar   := name (":" univ)?                        -- default `Type<0>`
//! univ    := "Type" ("<" numeral ">")?
//! induct  := "inductive" name tyvars? "{" ctors? "}"
//! record  := "record" name tyvars? "{" rfield ("," rfield)* ","? "}"
//! rfield  := name ":" type            -- a record field is always named
//! ctors   := ctor ("," ctor)* ","?
//! ctor    := name ("(" field ("," field)* ","? ")")?
//! field   := (name ":")? type
//! params  := param ("," param)* ","?
//! param   := name ":" type | "{" name ":" type "}"   -- implicit
//! type    := "(" name ":" type ")" "->" type         -- dependent function
//!          | tyatom "->" type                        -- right-associative
//!          | tyatom
//! tyatom  := univ                                    -- Type, Type<n>
//!          | "[" type ";" expr "]"                   -- length-indexed vector
//!          | name ("<" type ("," type)* ">")         -- applied inductive
//!          | cmp                    -- bare `Nat`/`Bool` is that type
//!          | "(" type ")"
//! cmp     := expr (("=" | "<=" | "<") expr)?   -- ONE non-associative rung:
//!                                      `=` is propositional equality (`==`
//!                                      rejected), `<=` is `Le(a, b)`, `<` is
//!                                      `lt(a, b)`; none of them chain
//! block   := "{" stmt* expr on_stmt* "}"
//! stmt    := "let" name (":" type)? "=" expr ";"
//!          | "let" "{" name ("," name)* ","? "}" "=" expr ";"   -- destructure
//! on_stmt := "on" ("?" name ("." numeral)? | "_" ":" type) ":=" expr ";"
//! expr    := "match" expr ("as" name "->" type)? "{" arms "}"
//!          | "refl" | "?" name?
//!          | "j" "(" expr "," "(" name "," name ")" "->" type "," expr ")"
//!          | ("λ"|"fun") binder+ "=>" expr
//!          | "@" name ("<" type ("," type)* ">")? "(" args ")"
//!          | atom ("<" type ("," type)* ">")?     -- explicit type application
//!                 ("{" (name ":" expr)* "}")?     -- record literal
//!                 (("." name ("(" args ")")?) | "(" args ")")*   -- postfix
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
    let mut p = Parser { toks, pos: 0, no_record_lit: false, no_eq: false, motive_body: false };
    let mut items = Vec::new();
    while !p.at_eof() {
        items.push(p.item()?);
    }
    Ok(File { items })
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    /// Suppress the record literal `D { … }` (docs/surface-records.md §6.1).
    ///
    /// `{` after an expression is ambiguous exactly where a *block* follows
    /// one: `match m { … }` would otherwise read `m { … }` as a literal. Rust
    /// has the same problem and the same fix — the restriction is set for the
    /// scrutinee and the block-preceding types, and **lifted inside any
    /// bracket**, so `match f(D { x: 1 }) { … }` is fine and a literal that
    /// really is wanted in scrutinee position is parenthesised.
    no_record_lit: bool,
    /// Suppress the whole **comparison level** — `a = b`, `a <= b`, `a < b` —
    /// as an *expression* (docs/surface-universe.md §13).
    ///
    /// `=` is loosest-binding and non-associative, which is right everywhere
    /// except the two contexts that use it as punctuation: a `calc` step
    /// (`e0 = e1 := p`) reads its endpoints with `=` as the separator, and
    /// [`Parser::ty_atom`] must not re-consume the `=` it is about to inspect.
    /// Same shape as `no_record_lit`: set in the punctuation contexts, and the
    /// escape hatch is a parenthesis.
    no_eq: bool,
    /// The next lambda body parsed is a **motive** body, so it is a type and
    /// is parsed with [`Parser::ty`] rather than [`Parser::expr`].
    ///
    /// One-shot: [`Parser::lambda`] takes the flag, so only the motive's own
    /// lambda is affected and a lambda *inside* the motive body is an
    /// ordinary expression lambda. Needed because a motive body may be a
    /// function type — an IH-generalizing motive is
    /// `λ z => (env: Val) -> … -> P(z)` — and `->` is not in the expression
    /// grammar (`issues/ih-generalization.md`). Every type the old grammar
    /// accepted here still parses: [`Parser::ty`] falls through to
    /// [`Parser::expr`] for `a = b`, names and applications.
    motive_body: bool,
}

type R<T> = Result<T, ParseError>;

/// `name(args…)` as an [`ExprKind::App`] with a `Var` head — what the operator
/// and `calc` desugarings build.
fn named_call(name: &str, args: Vec<Expr>, explicit: bool, span: Span) -> Expr {
    let head = Expr { kind: ExprKind::Var(name.to_string()), span };
    Expr { kind: ExprKind::App { head: Box::new(head), args, explicit }, span }
}

/// Read an already-parsed expression **as a type**, syntactically and totally.
///
/// The one place the grammar decides what an expression means in type
/// position, shared by `ty_atom`'s fall-through and by `expr`'s arrow
/// domain, so the two cannot drift. Nothing here is a judgement about whether
/// the thing *is* a type: a bare name becomes `TyKind::Named` whether or not a
/// type by that name exists, and everything unrecognised becomes
/// `TyKind::OfExpr`, a *decoded* type the elaborator checks sits at a universe
/// (docs/surface-universe.md §4).
fn expr_as_ty(e: &Expr) -> Ty {
    let span = e.span;
    let kind = match &e.kind {
        // `a = b` is an *expression* former, so it arrives already built; a
        // type position simply names it (docs/surface-universe.md §13).
        ExprKind::Eq(a, b) => TyKind::Eq(a.clone(), b.clone()),
        // A type that was written in type syntax in the first place — a
        // function type, or a motive body. Unwrap rather than re-wrap, so
        // `Nat -> Nat` in type position is the same `TyKind::Fn` it always was
        // and not an `El` of its own code.
        ExprKind::TyLit(t) => return (**t).clone(),
        // A bare name in type position is `Nat` or a declared type; whether
        // the name is in fact a type is the elaborator's call.
        ExprKind::Var(s) if s == "Nat" => TyKind::Nat,
        ExprKind::Var(s) => TyKind::Named { name: s.clone(), args: vec![] },
        // `Type<n>` and `List<Nat>` — the two forms `atom` already parses with
        // type syntax inside them, so reading them back costs nothing.
        ExprKind::Univ { level } => TyKind::Univ { level: *level },
        ExprKind::TyApp { head, args } => match &head.kind {
            ExprKind::Var(name) => TyKind::Named { name: name.clone(), args: args.clone() },
            _ => TyKind::OfExpr(Box::new(e.clone())),
        },
        // Any other expression: a decoded type. `m.carrier` is why this
        // exists. Deliberately last, so every shape that already parsed as a
        // type still does.
        _ => TyKind::OfExpr(Box::new(e.clone())),
    };
    Ty { kind, span }
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

    /// Run `f` with the record-literal restriction set to `no`, restoring it
    /// after. Every bracketed context clears it; the three block-preceding
    /// contexts set it (see [`Parser::no_record_lit`]).
    fn with_record_lit<T>(&mut self, no: bool, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.no_record_lit, no);
        let r = f(self);
        self.no_record_lit = saved;
        r
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
        if self.at_kw("record") {
            return Ok(Item::Inductive(self.record()?));
        }
        Ok(Item::Decl(self.decl()?))
    }

    /// `record D<p, …>(v: T, …) { f: T, … }` — desugared here into the
    /// one-constructor `InductiveDecl` the tier-0 generator already handles
    /// (docs/surface-records.md §2.1), with the constructor named after the
    /// record. What makes it a distinct *surface* form is the checks the flag
    /// earns downstream, not a distinct lowering.
    ///
    /// Every field must be named: `record D { Nat }` has nothing to project.
    fn record(&mut self) -> R<InductiveDecl> {
        let start = self.peek_span();
        self.bump(); // `record`
        let (name, _) = self.ident("record name")?;
        let params = self.tyvar_list()?;
        let valparams = self.valparam_list()?;
        self.expect(&TokKind::LBrace, "`{` (field list)")?;
        let mut fields = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let f = self.field()?;
            if f.name.is_none() {
                return Err(ParseError {
                    msg: "a record field needs a name (`unit: Nat`): the name is what \
                          `m.unit` projects by"
                        .into(),
                    span: f.span,
                });
            }
            fields.push(f);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}` (field list)")?;
        let span = start.join(end);
        let ctor = CtorDecl { name: name.clone(), fields, result: None, span };
        Ok(InductiveDecl {
            name,
            params,
            valparams,
            ctors: vec![ctor],
            is_record: true,
            index: None,
            span,
        })
    }

    /// `(p: T, …)` after a declaration name (and after its `<…>`), or nothing —
    /// the **value** parameter list (docs/surface-value-parameters.md §1).
    ///
    /// The position is free and unambiguous: before this grammar existed, a `(`
    /// here was `parse error: expected `{``, and `fn`/`theorem` share no
    /// grammar with `record`/`inductive` (they have their own inline binder
    /// loop). Every parameter must be named — a value parameter is referred to
    /// by name inside the field types, which is the whole point of it.
    fn valparam_list(&mut self) -> R<Vec<Param>> {
        let mut params = Vec::new();
        if !matches!(self.peek(), TokKind::LParen) {
            return Ok(params);
        }
        self.bump();
        while !matches!(self.peek(), TokKind::RParen) {
            let (n, span) = self.ident("value parameter name")?;
            self.expect(&TokKind::Colon, "`:` (a value parameter is `name: T`)")?;
            let ty = self.ty()?;
            let span = span.join(ty.span);
            params.push(Param { name: n, ty, implicit: false, is_self: false, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::RParen, "`)` to close the value parameters")?;
        Ok(params)
    }

    /// `<A, B>` after a declaration name, or nothing.
    fn tyvar_list(&mut self) -> R<Vec<String>> {
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
        Ok(params)
    }

    /// `inductive D<p, …> { c(f: T, …), … }`. Zero constructors is legal (the
    /// empty type); so is a constructor with no field list.
    fn inductive(&mut self) -> R<InductiveDecl> {
        let start = self.peek_span();
        self.bump(); // `inductive`
        let (name, _) = self.ident("inductive name")?;
        let params = self.tyvar_list()?;
        // Parsed, then rejected by the elaborator: value parameters are a
        // `record` form this round (docs/surface-value-parameters.md §6), and a
        // named rejection beats `expected `{`, found LParen`.
        let valparams = self.valparam_list()?;
        // `: (n: Nat) -> Type` — an index telescope
        // (docs/inductive-indexed-lowering.md §2). Parsed with the ordinary
        // type grammar; its shape is the elaborator's to validate.
        let index = if matches!(self.peek(), TokKind::Colon) {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
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
            // `Nil : Vec<A>(0)` — a constructor's result annotation, an
            // expression by the same backtracking rule that makes `Vec<A>(0)`
            // an expression in type position (`ty_atom`): an applied type is
            // never called, so the call *is* the index application.
            let result = if matches!(self.peek(), TokKind::Colon) {
                self.bump();
                let r = self.expr()?;
                span = span.join(r.span);
                Some(r)
            } else {
                None
            };
            ctors.push(CtorDecl { name: cname, fields, result, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}` (constructor list)")?;
        Ok(InductiveDecl {
            name,
            params,
            valparams,
            ctors,
            is_record: false,
            index,
            span: start.join(end),
        })
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
        // `meta fn` — a layer-m declaration (docs/in-language-map-design.md
        // §3). Only `fn`: a theorem is an opaque Ψ-global, and meta
        // definitions never reach Ψ, so `meta theorem` has no meaning.
        let is_meta = self.eat_kw("meta");
        let kind = if self.eat_kw("fn") {
            DeclKind::Fn
        } else if !is_meta && self.eat_kw("theorem") {
            DeclKind::Theorem
        } else if is_meta {
            return self.err("`meta` marks a `fn`: write `meta fn name(…)`");
        } else {
            return self.err("expected `fn`, `theorem`, or `inductive`");
        };
        let (name, _) = self.ident("declaration name")?;
        // `fn map<A, B>(…)` — type parameters (docs/surface-polymorphism.md
        // §1). Unambiguous here: a declaration's name is always followed by
        // `(` or `<`, and neither is an expression continuation.
        let mut tyvars = Vec::new();
        if matches!(self.peek(), TokKind::Lt) {
            self.bump();
            loop {
                let (tv, tvsp) = self.ident("type parameter name")?;
                if tv == "self" {
                    // Type arguments are never passed at a call site
                    // (issues/at-and-type-arguments.md), so there is no slot
                    // here for a receiver either.
                    return Err(ParseError {
                        msg: "a type parameter cannot be `self`: type arguments are \
                              never passed at a call site, so there is nothing for a \
                              receiver to fill"
                            .into(),
                        span: tvsp,
                    });
                }
                // `<A: Type<1>>` — the universe the parameter ranges over,
                // defaulting to `Type<0>` (docs/surface-universe.md §2). The
                // annotation is a *universe*, not any type: a type parameter
                // ranges over a universe by definition.
                let mut level = 0;
                if matches!(self.peek(), TokKind::Colon) {
                    self.bump();
                    let Some((n, _)) = self.univ()? else {
                        return self.err(
                            "a type parameter's annotation must be a universe: write \
                             `<A: Type<n>>`, or `<A>` for `Type<0>`",
                        );
                    };
                    level = n;
                }
                tyvars.push(TyParam { name: tv, level, span: tvsp });
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::Gt, "`>` to close the type parameters")?;
        }
        self.expect(&TokKind::LParen, "`(`")?;
        let mut params = Vec::new();
        while !matches!(self.peek(), TokKind::RParen) {
            // `{name: T}` marks an implicit parameter (filled by unification);
            // `name: T` is explicit.
            let implicit = matches!(self.peek(), TokKind::LBrace);
            if implicit {
                self.bump();
            }
            // `self p: T` marks the parameter a method receiver fills
            // (issues/method-receiver-position.md). `self: T` marks *and*
            // names it, so a record method reads the Rust way; there is no
            // third reading, which is what keeps a parameter merely named
            // `self` from silently not being the subject.
            let is_self = self.at_kw("self");
            let self_sp = self.peek_span();
            if is_self {
                self.bump();
            }
            let (pname, psp) = if is_self && matches!(self.peek(), TokKind::Colon) {
                ("self".to_string(), self_sp)
            } else {
                self.ident("parameter name")?
            };
            if is_self && implicit {
                return Err(ParseError {
                    msg: "`self` cannot be implicit: an implicit parameter has no \
                          argument slot for the receiver to fill"
                        .into(),
                    span: self_sp.join(psp),
                });
            }
            if is_self && let Some(prev) = params.iter().find(|p: &&Param| p.is_self) {
                return Err(ParseError {
                    msg: format!(
                        "a declaration has at most one `self`, and `{}` is already it",
                        prev.name
                    ),
                    span: self_sp.join(psp),
                });
            }
            self.expect(&TokKind::Colon, "`:`")?;
            let ty = self.ty()?;
            let mut span = psp.join(ty.span);
            if implicit {
                span = span.join(self.expect(&TokKind::RBrace, "`}` to close implicit parameter")?);
            }
            params.push(Param { name: pname, ty, implicit, is_self, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::RParen, "`)`")?;
        // `for vec.map` — the elaboration slot this template fills
        // (docs/meta-def-registration-design.md §2.1). The parse point is
        // unambiguous: what follows a parameter list is `->` or `:`, never an
        // identifier, so the contextual keyword cannot be read as anything
        // else. The path's *vocabulary* is the elaborator's, so an unknown
        // slot is a registration diagnostic, not a parse error.
        let elaborates = if self.at_kw("for") {
            let start = self.bump().span;
            let (family, _) = self.ident("a slot family (`for vec.map`)")?;
            self.expect(&TokKind::Dot, "`.` (a slot is written `family.name`)")?;
            let (sname, nsp) = self.ident("a slot name (`for vec.map`)")?;
            let span = start.join(nsp);
            if !is_meta {
                return Err(ParseError {
                    msg: "`for` marks a `meta fn` as an elaboration template: an \
                          ordinary declaration elaborates nothing but itself"
                        .into(),
                    span,
                });
            }
            Some(SlotPath { family, name: sname, span })
        } else {
            None
        };
        match kind {
            DeclKind::Fn => {
                self.expect(&TokKind::Arrow, "`->`")?;
            }
            DeclKind::Theorem => {
                self.expect(&TokKind::Colon, "`:`")?;
            }
        }
        // The declaration's body block follows immediately, so a `{` here
        // opens it, not a record literal in the last endpoint of a
        // `theorem t: a = D { … }` (docs/surface-records.md §6.1).
        let result = self.with_record_lit(true, |p| p.ty())?;
        let body = self.block()?;
        let span = start.join(body.span);
        Ok(Decl { kind, is_meta, elaborates, name, tyvars, params, result, body, span })
    }

    // -- blocks and statements ----------------------------------------------

    fn block(&mut self) -> R<Block> {
        let open = self.expect(&TokKind::LBrace, "`{`")?;
        // Inside the braces nothing is waiting for a block, so a literal is
        // unambiguous again.
        let saved = std::mem::replace(&mut self.no_record_lit, false);
        let r = self.block_body(open);
        self.no_record_lit = saved;
        r
    }

    fn block_body(&mut self, open: Span) -> R<Block> {
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
        // `let { unit, op } = m;` — record destructuring
        // (docs/surface-records.md §5). Unambiguous against `let x = …`: a
        // binding name cannot start with `{`.
        if matches!(self.peek(), TokKind::LBrace) {
            self.bump();
            let mut fields = Vec::new();
            while !matches!(self.peek(), TokKind::RBrace) {
                let (n, sp) = self.ident("field name in a `let` pattern")?;
                fields.push((n, sp));
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::RBrace, "`}` (`let` pattern)")?;
            self.expect_eq("`let` pattern")?;
            let expr = self.expr()?;
            let end = self.expect(&TokKind::Semi, "`;` to end the `let`")?;
            return Ok(Stmt::LetRecord { fields, expr, span: start.join(end) });
        }
        // `let code x = e;` — the surface letbox (surface-v0 §4). Unambiguous
        // against `let code = …`: two names in a row were never a parse.
        if self.at_kw("code") && matches!(self.nth(1), TokKind::Ident(_)) {
            self.bump(); // `code`
            let (name, _) = self.ident("`let code` binding name")?;
            self.expect_eq("`let code` binding")?;
            let expr = self.expr()?;
            let end = self.expect(&TokKind::Semi, "`;` to end the `let code`")?;
            return Ok(Stmt::LetCode { name, expr, span: start.join(end) });
        }
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
        if self.at_binder_group() {
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
    /// `Type` / `Type<n>` in either position. Shared by [`Self::ty_atom`] and
    /// [`Self::atom`] so the two spellings cannot drift, and tried *before*
    /// the applied-inductive rule, which parses its arguments with
    /// [`Self::ty`] and would reject the numeral in `Type<0>`
    /// (docs/surface-universe.md §3).
    fn univ(&mut self) -> R<Option<(u64, Span)>> {
        if !self.at_kw("Type") {
            return Ok(None);
        }
        let start = self.bump().span;
        if !matches!(self.peek(), TokKind::Lt) {
            return Ok(Some((0, start)));
        }
        self.bump(); // `<`
        let &TokKind::Num(n) = self.peek() else {
            return self.err(
                "a universe level must be a numeral: levels cannot be quantified over \
                 at the surface (universe polymorphism is layer m) and joins are \
                 computed rather than written",
            );
        };
        self.bump();
        let end = self.expect(&TokKind::Gt, "`>` to close a universe level")?;
        Ok(Some((n, start.join(end))))
    }

    fn ty_atom(&mut self) -> R<Ty> {
        // `Type` / `Type<n>`. Before the applied-inductive rule below, which
        // would try to parse `0` as a type.
        if let Some((level, span)) = self.univ()? {
            return Ok(Ty { kind: TyKind::Univ { level }, span });
        }
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
        // The modal slice (docs/in-language-map-design.md §3): `Ctx`,
        // `TyCode(g)`, `Code(g |- T)`, and `$a` for a `TyCode` binder used as
        // a type. Keyword-shaped, so they are tried before the general rules;
        // a user type named `Ctx`/`TyCode`/`Code` was possible before and is
        // shadowed now, the usual cost of a keyword.
        if self.at_kw("Ctx") && !matches!(self.nth(1), TokKind::Lt | TokKind::LParen) {
            let span = self.bump().span;
            return Ok(Ty { kind: TyKind::Ctx, span });
        }
        if self.at_kw("TyCode") && matches!(self.nth(1), TokKind::LParen) {
            let start = self.bump().span;
            self.bump(); // `(`
            let (ctx, _) = self.ident("context name in `TyCode(g)`")?;
            let end = self.expect(&TokKind::RParen, "`)` to close `TyCode(g)`")?;
            return Ok(Ty { kind: TyKind::TyCode { ctx }, span: start.join(end) });
        }
        if self.at_kw("Code") && matches!(self.nth(1), TokKind::LParen) {
            let start = self.bump().span;
            self.bump(); // `(`
            let (ctx, _) = self.ident("context name in `Code(g |- T)`")?;
            self.expect(&TokKind::Turnstile, "`|-` (a code type is `Code(g |- T)`)")?;
            let ty = self.ty()?;
            let end = self.expect(&TokKind::RParen, "`)` to close `Code(g |- T)`")?;
            return Ok(Ty { kind: TyKind::Code { ctx, ty: Box::new(ty) }, span: start.join(end) });
        }
        if matches!(self.peek(), TokKind::Dollar) {
            let start = self.bump().span;
            let (name, nsp) = self.ident("name after `$` in type position")?;
            return Ok(Ty { kind: TyKind::Splice { name }, span: start.join(nsp) });
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
            let save = self.pos;
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
            // …unless a call follows, in which case this was an *expression*
            // with explicit type arguments opening an equality type —
            // `theorem t(): id<Nat>(3) = 3`. `(` is the discriminator for the
            // same reason `->` is in `group_is_type`: an applied type is
            // never called (docs/surface-polymorphism.md §1).
            if matches!(self.peek(), TokKind::LParen) {
                self.pos = save;
            } else {
                return Ok(Ty { kind: TyKind::Named { name, args }, span: start.join(end) });
            }
        }
        let lhs = self.expr()?;
        Ok(expr_as_ty(&lhs))
    }

    // -- expressions --------------------------------------------------------

    /// Expressions, with infix operators. Precedence, loosest to tightest: the
    /// **comparison level** ([`Self::comparison`] — `=`, `<=` (→ `Le`), `<`
    /// (→ `lt`)), then `+` (→ `add`), `*` (→ `mul`), then postfix
    /// `.method(args)` / calls, then atoms. The arithmetic operators desugar
    /// to an ordinary [`ExprKind::Call`] on a fixed name table
    /// (issues/surface-operators.md — the decorated `+_Z` grammar and trait
    /// hookup arrive with the real trait design).
    ///
    /// **Function types are expressions** (`docs/types-as-expressions.md`): a
    /// leading binder group `(x: A) -> …` and a trailing `->` both hand off to
    /// [`Self::ty`] and come back as an [`ExprKind::TyLit`]. Neither spelling
    /// was previously a parse — `->` after an expression was always an error,
    /// and `:` is not in the expression grammar — so this is a pure extension
    /// with no backtracking. `=` binds tighter than `->`, exactly as in
    /// [`Self::ty`], where the arrow's sides are `ty_atom`s and `ty_atom`
    /// falls through to this function.
    fn expr(&mut self) -> R<Expr> {
        // `(x: A) -> B`. The same three-token lookahead `ty()` uses; `:` is
        // not in the expression grammar, so a binder-headed group cannot be
        // anything else.
        if self.at_binder_group() {
            let ty = self.ty()?;
            let span = ty.span;
            return Ok(Expr { kind: ExprKind::TyLit(Box::new(ty)), span });
        }
        let lhs = self.expr_bp(0)?;
        let lhs = if self.no_eq { lhs } else { self.comparison(lhs)? };
        if !matches!(self.peek(), TokKind::Arrow) {
            return Ok(lhs);
        }
        // `A -> B`: read what we have as the domain and let `ty()` take the
        // (right-associative) codomain, so the two spellings share one parse.
        self.bump();
        let dom = expr_as_ty(&lhs);
        let cod = self.ty()?;
        let span = lhs.span.join(cod.span);
        let kind = TyKind::Fn { binder: None, dom: Box::new(dom), cod: Box::new(cod) };
        Ok(Expr { kind: ExprKind::TyLit(Box::new(Ty { kind, span })), span })
    }

    /// The **comparison level**: one non-associative rung, loosest of all, sitting
    /// above the arithmetic table (`a + b <= c` is `Le(add(a, b), c)`).
    ///
    /// Three spellings share it, because they are one notion — a relation
    /// between two arithmetic expressions — and because sharing a rung is what
    /// makes chaining impossible:
    ///
    /// - `a = b`, the identity-type former (an [`ExprKind::Eq`], not a call —
    ///   the elaborator never sees `=` as a `Call`);
    /// - `a <= b` ⇒ `Le(a, b)`, the *proposition* from lib/ir_v1.hthr, never
    ///   the boolean `leb`; a computational position calls `leb` by name
    ///   (issues/comparison-operators.md);
    /// - `a < b` ⇒ `lt(a, b)`, which has no lib target yet — it stays here so
    ///   `<` cannot chain either, and so the speculative type-argument parse
    ///   keeps its documented fallback (docs/surface-polymorphism.md §1).
    ///
    /// Non-associativity is structural first: the right operand is read with
    /// [`Parser::no_eq`] set, so it is an *arithmetic* expression and cannot
    /// grow a second comparison of its own. What is left over is then a
    /// dangling operator, which would surface as whatever error the caller
    /// happens to raise next — so a trailing `<=`/`==` gets a targeted message
    /// instead. A trailing `=` deliberately does **not**: `let p: a = b = pf;`
    /// and `let h: n <= m = pf;` are annotated `let`s whose binder `=` lands
    /// exactly there (issues/annotated-let-swallows-the-equals.md), and the
    /// parser cannot tell those from a chain without deciding that issue.
    fn comparison(&mut self, lhs: Expr) -> R<Expr> {
        let out = match self.peek() {
            TokKind::Eq | TokKind::EqEq => {
                self.expect_eq("equality type `a = b`")?;
                let rhs = self.with_eq(true, |p| p.expr_bp(0))?;
                let span = lhs.span.join(rhs.span);
                Expr { kind: ExprKind::Eq(Box::new(lhs), Box::new(rhs)), span }
            }
            TokKind::LtEq | TokKind::Lt => {
                let name = if matches!(self.peek(), TokKind::LtEq) { "Le" } else { "lt" };
                self.bump();
                let rhs = self.with_eq(true, |p| p.expr_bp(0))?;
                let span = lhs.span.join(rhs.span);
                named_call(name, vec![lhs, rhs], false, span)
            }
            _ => return Ok(lhs),
        };
        const CHAIN: &str = "comparisons do not chain: `=`, `<=` and `<` share one \
             non-associative level, so `a <= b <= c` has no reading. Write the two \
             comparisons separately, or parenthesise the one that is meant to be an \
             operand";
        match self.peek() {
            TokKind::LtEq => self.err(CHAIN),
            TokKind::EqEq => {
                self.err(format!("{CHAIN} (and `==` is not used in Heather: equality is `=`)"))
            }
            _ => Ok(out),
        }
    }

    /// `( ident :` — the start of a dependent function type's binder group.
    fn at_binder_group(&self) -> bool {
        matches!(self.peek(), TokKind::LParen)
            && matches!(self.nth(1), TokKind::Ident(_))
            && matches!(self.nth(2), TokKind::Colon)
    }

    /// Run `f` with the next lambda body flagged as a motive body. Restores
    /// the flag afterwards, so a motive that is not a lambda at all (the
    /// elaborator's diagnostic, not the grammar's) leaves nothing set.
    fn with_motive<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.motive_body, true);
        let r = f(self);
        self.motive_body = saved;
        r
    }

    /// Run `f` with `a = b` suppressed (or restored). Mirrors
    /// [`Parser::with_record_lit`].
    fn with_eq<T>(&mut self, no: bool, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.no_eq, no);
        let r = f(self);
        self.no_eq = saved;
        r
    }

    /// Binding powers for the infix operators. `(name, left_bp, right_bp)`;
    /// `right_bp > left_bp` makes every operator left-associative.
    fn infix_op(tok: &TokKind) -> Option<(&'static str, u8, u8)> {
        match tok {
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

    /// An atom followed by zero or more field accesses `.f` / `.f(args)`, a
    /// record literal `D { … }`, and zero or more applications `(args)` — so
    /// the head of a call can be any expression: `g(a)(b)`, `(λ x => x)(3)`
    /// (docs/surface-function-types.md §1.3).
    ///
    /// `.f` is **not** desugared here any more. It used to become
    /// `f(args…, receiver)` — a call to a global with the receiver last;
    /// where the receiver goes is now the callee's business, decided by its
    /// `self` parameter (issues/method-receiver-position.md). That reading is
    /// wrong anyway for a record of functions, where
    /// `m.op(x)` must be `(m.op)(x)`, and choosing between the two needs the
    /// receiver's *type*. So the parser emits [`ExprKind::Dot`] and the
    /// elaborator decides, keeping the old desugaring as the fallback
    /// (docs/surface-records.md §4.2).
    fn postfix(&mut self) -> R<Expr> {
        let mut e = self.atom()?;
        if let Some((args, end)) = self.try_tyargs() {
            let span = e.span.join(end);
            e = Expr { kind: ExprKind::TyApp { head: Box::new(e), args }, span };
        }
        // `D { … }` / `D<T> { … }` — a record literal. Only on a *name* head,
        // and only where a block cannot follow (see `no_record_lit`).
        if matches!(self.peek(), TokKind::LBrace) && !self.no_record_lit {
            let (name, tyargs) = match &e.kind {
                ExprKind::Var(n) => (Some(n.clone()), Vec::new()),
                ExprKind::TyApp { head, args } => match &head.kind {
                    ExprKind::Var(n) => (Some(n.clone()), args.clone()),
                    _ => (None, Vec::new()),
                },
                _ => (None, Vec::new()),
            };
            if let Some(name) = name {
                e = self.record_lit(name, tyargs, e.span)?;
            }
        }
        loop {
            match self.peek() {
                TokKind::Dot => {
                    self.bump();
                    let (field, fsp) = self.ident("field or method name")?;
                    let (args, end) = if matches!(self.peek(), TokKind::LParen) {
                        self.bump();
                        let (args, end) = self.call_args()?;
                        (Some(args), end)
                    } else {
                        (None, fsp)
                    };
                    let span = e.span.join(end);
                    e = Expr {
                        kind: ExprKind::Dot { recv: Box::new(e), name: field, args },
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

    /// `< T, … >` after an expression — explicit type application
    /// (docs/surface-polymorphism.md §1). `<` is *also* the `lt` operator
    /// ([`Self::comparison`]), so this is **speculative**: save the position, try, and
    /// restore on any failure. Backtracking is free (the parser is a token
    /// vector plus an index) and total, so unlike a lookahead heuristic it
    /// cannot be wrong about a program: `a < b` fails at the missing `>` and
    /// falls back to `lt`, `f<A>(x)` succeeds.
    ///
    /// The closing `>` alone is the discriminator — no `(` is required, so a
    /// bare `nil<Nat>` is a value. That is safe because `>` is not an
    /// expression operator (lexer.rs:28), so no `lt` expression can be
    /// followed by one.
    fn try_tyargs(&mut self) -> Option<(Vec<Ty>, Span)> {
        if !matches!(self.peek(), TokKind::Lt) {
            return None;
        }
        let save = self.pos;
        self.bump();
        let mut args = Vec::new();
        loop {
            match self.ty() {
                Ok(t) => args.push(t),
                Err(_) => {
                    self.pos = save;
                    return None;
                }
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        if !matches!(self.peek(), TokKind::Gt) {
            self.pos = save;
            return None;
        }
        Some((args, self.bump().span))
    }

    /// A primary expression: keyword forms (`match`/`refl`/`j`/`calc`), an
    /// `@`- or plain call, a variable, a numeral, or a parenthesised group.
    fn atom(&mut self) -> R<Expr> {
        let start = self.peek_span();
        // `Type<n>` where a term is expected. Before the operator loop sees
        // the `<`, which would otherwise read it as `lt`.
        if let Some((level, span)) = self.univ()? {
            return Ok(Expr { kind: ExprKind::Univ { level }, span });
        }
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
        // `code { e }` — a quotation (docs/in-language-map-design.md §3).
        // Before the general `Ident` case; the `{` lookahead is what keeps a
        // plain variable named `code` working everywhere else.
        if self.at_kw("code") && matches!(self.nth(1), TokKind::LBrace) {
            let start = self.bump().span; // `code`
            self.bump(); // `{`
            // Inside the braces nothing is waiting for a block (same reasoning
            // as `block`), and the payload is one expression — quotes have no
            // statements.
            let saved = std::mem::replace(&mut self.no_record_lit, false);
            let body = self.expr();
            self.no_record_lit = saved;
            let body = body?;
            let end = self.expect(&TokKind::RBrace, "`}` to close the quote")?;
            return Ok(Expr {
                kind: ExprKind::Quote(Box::new(body)),
                span: start.join(end),
            });
        }
        // `$x` / `${e}` — a splice (surface-v0 §4, verdict (c)).
        if matches!(self.peek(), TokKind::Dollar) {
            let start = self.bump().span;
            if matches!(self.peek(), TokKind::LBrace) {
                self.bump();
                let e = self.with_record_lit(false, |p| p.expr())?;
                let end = self.expect(&TokKind::RBrace, "`}` to close `${…}`")?;
                return Ok(Expr { kind: ExprKind::Splice(Box::new(e)), span: start.join(end) });
            }
            let (name, nsp) = self.ident("name after `$` (or `${expr}`)")?;
            let inner = Expr { kind: ExprKind::Var(name), span: nsp };
            return Ok(Expr { kind: ExprKind::Splice(Box::new(inner)), span: start.join(nsp) });
        }
        // `@f(args)` — a fully-explicit call (implicit params given
        // positionally). Stays an atom-level *named* form rather than a
        // prefix on any application: `@` suppresses implicit-argument
        // insertion, which is name-directed, so on a non-name there is
        // nothing to suppress (docs/surface-function-types.md §1.3).
        if matches!(self.peek(), TokKind::At) {
            let at = self.bump().span;
            let (name, nsp) = self.ident("call head after `@`")?;
            // `@f<T, …>(…)` — the two knobs compose: `<…>` writes the type
            // arguments, `@` makes the *value* implicits positional
            // (issues/at-and-type-arguments.md). Not speculative here, unlike
            // `try_tyargs`: after `@` a name is always a callee, so `<` can
            // only open a type-argument list.
            let mut head = Expr { kind: ExprKind::Var(name), span: nsp };
            if matches!(self.peek(), TokKind::Lt) {
                self.bump();
                let mut targs = Vec::new();
                loop {
                    targs.push(self.ty()?);
                    if !matches!(self.peek(), TokKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                let gt = self.expect(&TokKind::Gt, "`>` to close the type arguments")?;
                head = Expr {
                    kind: ExprKind::TyApp { head: Box::new(head), args: targs },
                    span: nsp.join(gt),
                };
            }
            self.expect(&TokKind::LParen, "`(` (`@` marks a call)")?;
            let (args, end) = self.call_args()?;
            return Ok(Expr {
                kind: ExprKind::App { head: Box::new(head), args, explicit: true },
                span: at.join(end),
            });
        }
        // `[a, b, c]` — a vector literal (docs/container-fields.md §2.2).
        if matches!(self.peek(), TokKind::LBracket) {
            let open = self.bump().span;
            return self.with_record_lit(false, |p| {
                let mut elems = Vec::new();
                while !matches!(p.peek(), TokKind::RBracket) {
                    elems.push(p.expr()?);
                    if !matches!(p.peek(), TokKind::Comma) {
                        break;
                    }
                    p.bump();
                }
                let close = p.expect(&TokKind::RBracket, "`]` (vector literal)")?;
                Ok(Expr { kind: ExprKind::VecLit(elems), span: open.join(close) })
            });
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
                // Parenthesising is the escape hatch for a record literal in
                // scrutinee position, so the restriction must lift here.
                let e = self.with_record_lit(false, |p| p.expr())?;
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
        // A motive body is a *type* (docs/surface-universe.md §13), and may be
        // a function type; nothing else in expression position may be.
        let body = if std::mem::take(&mut self.motive_body) {
            let ty = self.ty()?;
            let span = ty.span;
            Expr { kind: ExprKind::TyLit(Box::new(ty)), span }
        } else {
            self.expr()?
        };
        let span = start.join(body.span);
        Ok(Expr { kind: ExprKind::Lam { binders, body: Box::new(body) }, span })
    }

    /// Parse a comma-separated argument list up to and including the closing
    /// `)` (the opening `(` is already consumed). Returns the args and the
    /// span of the `)`.
    fn call_args(&mut self) -> R<(Vec<Expr>, Span)> {
        // Inside brackets a `{` cannot be a block, so the record-literal
        // restriction lifts here (and in every other bracketed context).
        self.with_record_lit(false, |p| {
            let mut args = Vec::new();
            while !matches!(p.peek(), TokKind::RParen) {
                args.push(p.expr()?);
                if !matches!(p.peek(), TokKind::Comma) {
                    break;
                }
                p.bump();
            }
            let end = p.expect(&TokKind::RParen, "`)`")?;
            Ok((args, end))
        })
    }

    /// `{ f: e, … }` after the record name, which the caller has consumed.
    /// Field order is free — it is normalized against the declaration in the
    /// elaborator (docs/surface-records.md §6), which is also where an unknown
    /// or missing field is reported, since only it knows the declaration.
    fn record_lit(&mut self, name: String, tyargs: Vec<Ty>, head: Span) -> R<Expr> {
        self.expect(&TokKind::LBrace, "`{` (record literal)")?;
        self.with_record_lit(false, |p| {
            let mut fields = Vec::new();
            while !matches!(p.peek(), TokKind::RBrace) {
                let (fname, fsp) = p.ident("record field name")?;
                p.expect(&TokKind::Colon, "`:` (record field)")?;
                let expr = p.expr()?;
                let span = fsp.join(expr.span);
                fields.push(RecordLitField { name: fname, expr, span });
                if !matches!(p.peek(), TokKind::Comma) {
                    break;
                }
                p.bump();
            }
            let end = p.expect(&TokKind::RBrace, "`}` (record literal)")?;
            Ok(Expr {
                kind: ExprKind::RecordLit { name, tyargs, fields },
                span: head.join(end),
            })
        })
    }

    fn match_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `match`
        // The scrutinee and the motive are both immediately followed by the
        // arm block, so a `{` here closes the `match` rather than opening a
        // record literal (docs/surface-records.md §6.1).
        let scrut = self.with_record_lit(true, |p| p.expr())?;
        let motive = if self.eat_kw("as") {
            // The retired spelling `as z -> T`, diagnosed rather than parsed:
            // `->` is the type arrow and nothing else now
            // (docs/surface-universe.md §13).
            if matches!(self.peek(), TokKind::Ident(_)) && matches!(self.nth(1), TokKind::Arrow) {
                return self.err(
                    "a motive is a lambda: write `as \u{3bb} z => T` (or `as fun z => T`) \
                     rather than `as z -> T`",
                );
            }
            Some(Box::new(self.with_motive(|p| p.with_record_lit(true, |p| p.expr()))?))
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
        // The retired spelling `(y, q) -> T`.
        if matches!(self.peek(), TokKind::LParen)
            && matches!(self.nth(1), TokKind::Ident(_))
            && matches!(self.nth(2), TokKind::Comma)
        {
            return self.err(
                "a motive is a lambda: write `j(p, \u{3bb} y q => T, case)` rather than \
                 `j(p, (y, q) -> T, case)`",
            );
        }
        let motive = self.with_motive(|p| p.expr())?;
        self.expect(&TokKind::Comma, "`,`")?;
        let case = self.expr()?;
        let end = self.expect(&TokKind::RParen, "`)`")?;
        Ok(Expr {
            kind: ExprKind::J {
                proof: Box::new(proof),
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
        // Endpoints are read with `=` suppressed: here it is the step
        // separator, not the identity type (docs/surface-universe.md §13).
        let mut terms = vec![self.with_eq(true, |p| p.expr())?];
        let mut proofs = Vec::new();
        self.expect_eq("calc step")?;
        loop {
            terms.push(self.with_eq(true, |p| p.expr())?);
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

    // -- the comparison level (issues/comparison-operators.md) --------------

    #[test]
    fn le_desugars_to_the_proposition_not_the_boolean() {
        // `a <= b` ⇒ `Le(a, b)`, the Type-valued proposition. `leb` is still
        // callable by name where a Bool is wanted; `<=` is not
        // context-sensitive.
        let k = body("a <= b");
        let (name, args, explicit) = as_call(&k);
        assert_eq!(name, "Le");
        assert!(!explicit);
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0].kind, ExprKind::Var(v) if v == "a"));
        assert!(matches!(&args[1].kind, ExprKind::Var(v) if v == "b"));
    }

    #[test]
    fn comparison_binds_looser_than_arithmetic() {
        // `a + b <= c * d` ⇒ Le(add(a, b), mul(c, d)) — the whole arithmetic
        // expression on each side, no parentheses needed.
        let k = body("a + b <= c * d");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "Le");
        assert_eq!(as_call(&args[0].kind).0, "add");
        assert_eq!(as_call(&args[1].kind).0, "mul");
    }

    #[test]
    fn comparisons_do_not_chain() {
        // Non-associative at their shared level: `a <= b <= c` has no reading,
        // and says so rather than silently grouping.
        for src in ["a <= b <= c", "a <= b == c", "a = b <= c", "a < b <= c"] {
            let e = parse_file(&format!("fn f() -> Nat {{ {src} }}")).unwrap_err();
            assert!(e.msg.contains("do not chain"), "{src}: {}", e.msg);
        }
    }

    #[test]
    fn a_comparison_still_parses_in_a_type() {
        // The statement position is where `<=` earns its keep:
        // `hle: n <= m` is the `Le(n, m)` hypothesis, and it composes with
        // `->` exactly as `Le(n, m)` did (`<=` binds tighter than the arrow).
        let f = parse_file("theorem t(n: Nat, m: Nat, h: n <= m): m <= m { h }").unwrap();
        let d = only_decl(&f);
        let TyKind::OfExpr(e) = &d.params[2].ty.kind else {
            panic!("expected a decoded type, got {:?}", d.params[2].ty.kind)
        };
        assert_eq!(as_call(&e.kind).0, "Le");
        let f = parse_file("theorem t(n: Nat): (m: Nat) -> n <= m -> n <= m { ?p }").unwrap();
        assert!(matches!(only_decl(&f).result.kind, TyKind::Fn { .. }));
    }

    #[test]
    fn a_type_argument_list_survives_the_two_char_token() {
        // `<=` is lexed greedily, and generics must not notice: a declaration
        // with type parameters, an applied inductive, and a `<=` all in one
        // file (issues/comparison-operators.md, the lexer worry).
        let f = parse_file(
            "record Boxed<A> { v: A }
             fn unbox<A>(b: Boxed<A>) -> A { b.v }
             theorem t(n: Nat, m: Nat, h: n <= m): n <= m { h }",
        )
        .unwrap();
        assert_eq!(f.items.len(), 3);
    }

    // `.f` is no longer desugared here: the parser emits `Dot` and the
    // elaborator decides between a record projection and the method call,
    // since only it knows the receiver's type (docs/surface-records.md §4.2).
    // What that desugaring *becomes* is pinned in the elaborator's tests; what
    // is pinned here is that the shape survives parsing intact.
    #[test]
    fn method_call_parses_as_dot_with_args() {
        let k = body("add_succ(n, k).sym()");
        let ExprKind::Dot { recv, name, args } = &k else { panic!("expected a Dot, got {k:?}") };
        assert_eq!(name, "sym");
        assert_eq!(args.as_ref().expect("`()` means a call").len(), 0);
        assert_eq!(as_call(&recv.kind).0, "add_succ");
    }

    #[test]
    fn field_access_parses_without_parens() {
        // `m.op` — a bare projection, which used to be a parse error.
        let k = body("m.op");
        let ExprKind::Dot { recv, name, args } = &k else { panic!("expected a Dot, got {k:?}") };
        assert_eq!(name, "op");
        assert!(args.is_none(), "no `()` means no call");
        assert!(matches!(&recv.kind, ExprKind::Var(v) if v == "m"));
    }

    #[test]
    fn dot_chains_left_associatively() {
        // `m.a.b(c)` — `(m.a).b(c)`, so the receiver of `b` is `m.a`.
        let k = body("m.a.b(c)");
        let ExprKind::Dot { recv, name, args } = &k else { panic!("expected a Dot, got {k:?}") };
        assert_eq!(name, "b");
        assert_eq!(args.as_ref().expect("a call").len(), 1);
        let ExprKind::Dot { name: inner, .. } = &recv.kind else { panic!("expected a Dot") };
        assert_eq!(inner, "a");
    }

    #[test]
    fn record_literal_parses_with_free_field_order() {
        let src = "record P { x: Nat, y: Nat }
                   fn f() -> P { P { y: 1, x: 0 } }";
        let mut items = parse_file(src).unwrap().items;
        let d = items.remove(1).into_decl();
        let ExprKind::RecordLit { name, tyargs, fields } = &d.body.result.kind else {
            panic!("expected a record literal, got {:?}", d.body.result.kind)
        };
        assert_eq!(name, "P");
        assert!(tyargs.is_empty());
        // Written order is preserved here; the permutation into declaration
        // order happens in the elaborator, which is what knows the order.
        assert_eq!(fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["y", "x"]);
    }

    // The `match m { … }` ambiguity (docs/surface-records.md §6.1): a `{`
    // after the scrutinee closes the `match`, and parenthesising is the escape
    // hatch for a literal that really is the scrutinee.
    #[test]
    fn a_match_scrutinee_does_not_swallow_the_arm_block() {
        let src = "record P { x: Nat }
                   inductive B { T, F }
                   fn f(b: B, m: P) -> Nat { match b { T => m.x, F => 0 } }";
        parse_file(src).expect("the arm block is not a record literal");
    }

    #[test]
    fn a_parenthesised_literal_may_be_a_scrutinee() {
        let src = "record P { x: Nat }
                   inductive B { T, F }
                   fn f(b: B) -> Nat { match (P { x: 1 }).x { Zero => 0, Succ(k) => k } }";
        parse_file(src).expect("parens lift the restriction");
    }

    #[test]
    fn a_record_field_must_be_named() {
        let msg = parse_file("record P { Nat }").unwrap_err().msg;
        assert!(msg.contains("record field needs a name"), "{msg}");
    }

    #[test]
    fn let_destructuring_parses() {
        let src = "record P { x: Nat, y: Nat }
                   fn f(p: P) -> Nat { let { x, y } = p; x }";
        let mut items = parse_file(src).unwrap().items;
        let d = items.remove(1).into_decl();
        let Stmt::LetRecord { fields, .. } = &d.body.stmts[0] else {
            panic!("expected a destructuring let")
        };
        assert_eq!(fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(), ["x", "y"]);
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
        let Stmt::Let { name, ty, .. } = &d.body.stmts[0] else { panic!("plain let") };
        assert_eq!(name, "a");
        assert!(ty.is_none());
        // `let p: n = n = refl;` — `=` is not an expression operator, so the
        // annotation stops after `n = n` and the binding `=` follows.
        let Stmt::Let { name, ty, expr, .. } = &d.body.stmts[1] else { panic!("plain let") };
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

    // -- the quotation slice (docs/in-language-map-design.md §3) ------------

    #[test]
    fn meta_fn_with_modal_signature() {
        let f = parse_file(
            "meta fn map_code(g: Ctx, a: TyCode(g), f: Code(g |- $a -> Nat)) \
             -> Code(g |- Nat) { code { 0 } }",
        )
        .unwrap();
        let d = only_decl(&f);
        assert!(d.is_meta);
        assert!(matches!(d.params[0].ty.kind, TyKind::Ctx));
        assert!(matches!(&d.params[1].ty.kind, TyKind::TyCode { ctx } if ctx == "g"));
        let TyKind::Code { ctx, ty } = &d.params[2].ty.kind else {
            panic!("expected a Code type, got {:?}", d.params[2].ty.kind)
        };
        assert_eq!(ctx, "g");
        let TyKind::Fn { dom, .. } = &ty.kind else { panic!("expected `$a -> Nat`") };
        assert!(matches!(&dom.kind, TyKind::Splice { name } if name == "a"));
        assert!(matches!(&d.result.kind, TyKind::Code { .. }));
        assert!(matches!(&d.body.result.kind, ExprKind::Quote(_)));
    }

    /// The registration clause (docs/meta-def-registration-design.md §2.1).
    /// The parser only shapes the path; whether `vec.map` names a slot is the
    /// elaborator's question, where the vocabulary can be listed.
    #[test]
    fn meta_fn_declares_its_slot() {
        let f =
            parse_file("meta fn map_code(g: Ctx) for vec.map -> Code(g |- Nat) { code { 0 } }")
                .unwrap();
        let d = only_decl(&f);
        let s = d.elaborates.as_ref().expect("a `for` clause");
        assert_eq!((s.family.as_str(), s.name.as_str()), ("vec", "map"));
        // …and a `meta fn` without one parses exactly as before.
        let g = parse_file("meta fn m(g: Ctx) -> Code(g |- Nat) { code { 0 } }").unwrap();
        assert!(only_decl(&g).elaborates.is_none());
    }

    #[test]
    fn a_for_clause_marks_a_meta_fn_only() {
        let err = parse_file("fn f(n: Nat) for vec.map -> Nat { n }").unwrap_err();
        assert!(err.msg.contains("meta fn"), "{}", err.msg);
    }

    #[test]
    fn meta_marks_a_fn_only() {
        let err = parse_file("meta theorem t(): Nat { 0 }").unwrap_err();
        assert!(err.msg.contains("meta"), "{}", err.msg);
    }

    #[test]
    fn quote_splices_and_let_code() {
        // `$x` and `${e}` are one node; `let code` is its own statement.
        let d = parse_file(
            "meta fn f(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { \
             let code y = x; code { add($y, ${x}) } }",
        )
        .unwrap()
        .items
        .remove(0)
        .into_decl();
        assert!(matches!(&d.body.stmts[0], Stmt::LetCode { name, .. } if name == "y"));
        let ExprKind::Quote(payload) = &d.body.result.kind else { panic!("expected a quote") };
        let (_, args, _) = as_call(&payload.kind);
        assert!(matches!(&args[0].kind, ExprKind::Splice(_)));
        assert!(matches!(&args[1].kind, ExprKind::Splice(_)));
    }

    #[test]
    fn code_is_still_an_ordinary_name() {
        // The `{` lookahead is what keeps `code` usable as a variable, and
        // `Code`/`Ctx` stay ordinary type names when their follow set says so.
        let k = body("add(code, 1)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "code"));
        // `Code<Nat>` — a user inductive named `Code` applied to arguments
        // still parses as a Named type (no `(` after the name).
        let f = parse_file("fn f(x: Code<Nat>) -> Nat { 0 }").unwrap();
        assert!(matches!(&only_decl(&f).params[0].ty.kind, TyKind::Named { name, .. } if name == "Code"));
    }

    #[test]
    fn let_code_needs_a_name() {
        // `let code = e;` binds a plain variable named `code`, unchanged.
        let f = parse_file("fn f(n: Nat) -> Nat { let code = n; code }").unwrap();
        assert!(matches!(&only_decl(&f).body.stmts[0], Stmt::Let { name, .. } if name == "code"));
    }

    #[test]
    fn turnstile_is_required_in_code_types() {
        let err =
            parse_file("meta fn f(g: Ctx, x: Code(g, Nat)) -> Code(g |- Nat) { code { 0 } }")
                .unwrap_err();
        assert!(err.msg.contains("|-"), "{}", err.msg);
    }
}
