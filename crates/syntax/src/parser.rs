//! Recursive-descent parser for the stage-1 grammar.
//!
//! ```text
//! file    := decl*
//! decl    := "fn" name "(" params? ")" "->" type block
//!          | "theorem" name "(" params? ")" ":" type block
//! params  := param ("," param)* ","?
//! param   := name ":" type | "{" name ":" type "}"   -- implicit
//! type    := expr ("=" expr)?       -- bare `Nat` is the type Nat; `=` is
//!                                      propositional equality (`==` rejected)
//! block   := "{" expr "}"
//! expr    := "match" expr ("as" name "->" type)? "{" arms "}"
//!          | "refl"
//!          | "j" "(" expr "," "(" name "," name ")" "->" type "," expr ")"
//!          | "@"? name "(" args ")" | name | numeral | "(" expr ")"
//! arms    := arm ("," arm)* ","?    -- exactly a Zero arm and a Succ arm
//! arm     := "Zero" "=>" expr | "Succ" "(" name ("," name)? ")" "=>" expr
//! ```

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
    let mut decls = Vec::new();
    while !p.at_eof() {
        decls.push(p.decl()?);
    }
    Ok(File { decls })
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

type R<T> = Result<T, ParseError>;

impl Parser {
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

    fn decl(&mut self) -> R<Decl> {
        let start = self.peek_span();
        let kind = if self.eat_kw("fn") {
            DeclKind::Fn
        } else if self.eat_kw("theorem") {
            DeclKind::Theorem
        } else {
            return self.err("expected `fn` or `theorem`");
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
        self.expect(&TokKind::LBrace, "`{`")?;
        let body = self.expr()?;
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        Ok(Decl { kind, name, params, result, body, span: start.join(end) })
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

    fn ty(&mut self) -> R<Ty> {
        let lhs = self.expr()?;
        if matches!(self.peek(), TokKind::Eq | TokKind::EqEq) {
            self.expect_eq("equality type `a = b`")?;
            let rhs = self.expr()?;
            let span = lhs.span.join(rhs.span);
            return Ok(Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rhs)), span });
        }
        // A bare expression in type position must be the type `Nat`.
        match &lhs.kind {
            ExprKind::Var(s) if s == "Nat" => Ok(Ty { kind: TyKind::Nat, span: lhs.span }),
            _ => Err(ParseError {
                msg: "expected a type (`Nat` or `a = b`)".into(),
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
            lhs = Expr {
                kind: ExprKind::Call { name: name.to_string(), args: vec![lhs, rhs], explicit: false },
                span,
            };
        }
        Ok(lhs)
    }

    /// An atom followed by zero or more method calls `.f(args)`. A method call
    /// desugars to `f(args…, receiver)` — the receiver is the *last* argument,
    /// so with stage-2 implicit endpoints (issues/elab-stage2-metas.md) the
    /// earlier implicit parameters are inferred from it (`p.sym()` ⇒ `sym(p)`,
    /// `add_succ(n, k).sym()` ⇒ `sym(add_succ(n, k))`).
    fn postfix(&mut self) -> R<Expr> {
        let mut e = self.atom()?;
        while matches!(self.peek(), TokKind::Dot) {
            self.bump();
            let (method, _) = self.ident("method name")?;
            self.expect(&TokKind::LParen, "`(` (method call)")?;
            let (mut args, end) = self.call_args()?;
            let span = e.span.join(end);
            args.push(e);
            e = Expr { kind: ExprKind::Call { name: method, args, explicit: false }, span };
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
        // `@f(args)` — a fully-explicit call (implicit params given positionally).
        if matches!(self.peek(), TokKind::At) {
            let at = self.bump().span;
            let (name, _) = self.ident("call head after `@`")?;
            self.expect(&TokKind::LParen, "`(` (`@` marks a call)")?;
            let (args, end) = self.call_args()?;
            return Ok(Expr {
                kind: ExprKind::Call { name, args, explicit: true },
                span: at.join(end),
            });
        }
        match self.peek().clone() {
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
            TokKind::Ident(name) => {
                let sp = self.bump().span;
                if matches!(self.peek(), TokKind::LParen) {
                    self.bump();
                    let (args, end) = self.call_args()?;
                    Ok(Expr {
                        kind: ExprKind::Call { name, args, explicit: false },
                        span: sp.join(end),
                    })
                } else {
                    Ok(Expr { kind: ExprKind::Var(name), span: sp })
                }
            }
            _ => self.err("expected an expression"),
        }
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
        let mut zero: Option<Expr> = None;
        let mut succ: Option<(String, Option<String>, Expr)> = None;
        while !matches!(self.peek(), TokKind::RBrace) {
            if self.eat_kw("Zero") {
                self.expect(&TokKind::FatArrow, "`=>`")?;
                if zero.replace(self.expr()?).is_some() {
                    return self.err("duplicate `Zero` arm");
                }
            } else if self.eat_kw("Succ") {
                self.expect(&TokKind::LParen, "`(`")?;
                let (k, _) = self.ident("predecessor name")?;
                // `Succ(k)` is the unified form (ih = guarded self-call);
                // `Succ(k, ih)` stays as the low-level explicit fallback.
                let ih = if matches!(self.peek(), TokKind::Comma) {
                    self.bump();
                    Some(self.ident("ih name")?.0)
                } else {
                    None
                };
                self.expect(&TokKind::RParen, "`)`")?;
                self.expect(&TokKind::FatArrow, "`=>`")?;
                if succ.replace((k, ih, self.expr()?)).is_some() {
                    return self.err("duplicate `Succ` arm");
                }
            } else {
                return self.err("expected a `Zero` or `Succ(k)` arm");
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        let (Some(zero), Some((k, ih, body))) = (zero, succ) else {
            return Err(ParseError {
                msg: "`match` needs both a `Zero` and a `Succ(k)` arm".into(),
                span: start.join(end),
            });
        };
        Ok(Expr {
            kind: ExprKind::Match {
                scrut: Box::new(scrut),
                motive,
                zero: Box::new(zero),
                succ: (k, ih, Box::new(body)),
            },
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
            acc = Expr {
                kind: ExprKind::Call {
                    name: "trans".to_string(),
                    args: vec![
                        terms[i].clone(),
                        terms[i + 1].clone(),
                        last.clone(),
                        proofs[i].clone(),
                        acc,
                    ],
                    explicit: true,
                },
                span,
            };
        }
        acc.span = span;
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implicit_and_explicit_params() {
        let f = parse_file("theorem t({a: Nat}, b: Nat, p: a = b): b = a { refl }").unwrap();
        let ps = &f.decls[0].params;
        assert_eq!(ps.len(), 3);
        assert!(ps[0].implicit, "`{{a}}` is implicit");
        assert!(!ps[1].implicit, "`b` is explicit");
        assert!(!ps[2].implicit, "`p` is explicit");
    }

    #[test]
    fn at_marks_a_fully_explicit_call() {
        let f = parse_file("fn f(n: Nat) -> Nat { @g(a, b, p) }").unwrap();
        match &f.decls[0].body.kind {
            ExprKind::Call { name, args, explicit } => {
                assert_eq!(name, "g");
                assert_eq!(args.len(), 3);
                assert!(*explicit);
            }
            other => panic!("expected an explicit call, got {other:?}"),
        }
    }

    #[test]
    fn plain_call_is_not_explicit() {
        let f = parse_file("fn f(n: Nat) -> Nat { g(a) }").unwrap();
        match &f.decls[0].body.kind {
            ExprKind::Call { explicit, .. } => assert!(!*explicit),
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
        parse_file(&src).unwrap().decls.remove(0).body.kind
    }

    fn as_call(k: &ExprKind) -> (&str, &[Expr], bool) {
        match k {
            ExprKind::Call { name, args, explicit } => (name.as_str(), args.as_slice(), *explicit),
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
        assert!(matches!(f.decls[0].result.kind, crate::ast::TyKind::Eq(..)));
    }

    #[test]
    fn double_eq_is_rejected_with_a_hint() {
        // `==` is lexed but not grammatical; equality is `=`. The parser
        // rejects it with a targeted message (C/Rust muscle memory).
        let err = parse_file("theorem t(a: Nat, b: Nat): a == b { refl }").unwrap_err();
        assert!(err.msg.contains("=="), "hint should mention `==`: {}", err.msg);
        assert!(err.msg.contains('='), "hint should point at `=`: {}", err.msg);
    }
}
