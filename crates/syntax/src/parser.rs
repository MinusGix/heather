//! Recursive-descent parser for the stage-1 grammar.
//!
//! ```text
//! file    := decl*
//! decl    := "fn" name "(" params? ")" "->" type block
//!          | "theorem" name "(" params? ")" ":" type block
//! params  := name ":" type ("," name ":" type)* ","?
//! type    := expr ("==" expr)?      -- bare `Nat` is the type Nat
//! block   := "{" expr "}"
//! expr    := "match" expr ("as" name "->" type)? "{" arms "}"
//!          | "refl"
//!          | "j" "(" expr "," "(" name "," name ")" "->" type "," expr ")"
//!          | name "(" args ")" | name | numeral | "(" expr ")"
//! arms    := arm ("," arm)* ","?    -- exactly a Zero arm and a Succ arm
//! arm     := "Zero" "=>" expr | "Succ" "(" name "," name ")" "=>" expr
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
            let (pname, psp) = self.ident("parameter name")?;
            self.expect(&TokKind::Colon, "`:`")?;
            let ty = self.ty()?;
            let span = psp.join(ty.span);
            params.push(Param { name: pname, ty, span });
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

    fn ty(&mut self) -> R<Ty> {
        let lhs = self.expr()?;
        if matches!(self.peek(), TokKind::EqEq) {
            self.bump();
            let rhs = self.expr()?;
            let span = lhs.span.join(rhs.span);
            return Ok(Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rhs)), span });
        }
        // A bare expression in type position must be the type `Nat`.
        match &lhs.kind {
            ExprKind::Var(s) if s == "Nat" => Ok(Ty { kind: TyKind::Nat, span: lhs.span }),
            _ => Err(ParseError {
                msg: "expected a type (`Nat` or `a == b`)".into(),
                span: lhs.span,
            }),
        }
    }

    // -- expressions --------------------------------------------------------

    fn expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        if self.at_kw("match") {
            return self.match_expr();
        }
        if self.at_kw("refl") {
            self.bump();
            return Ok(Expr { kind: ExprKind::Refl, span: start });
        }
        if self.at_kw("j") {
            return self.j_expr();
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
                    let mut args = Vec::new();
                    while !matches!(self.peek(), TokKind::RParen) {
                        args.push(self.expr()?);
                        if !matches!(self.peek(), TokKind::Comma) {
                            break;
                        }
                        self.bump();
                    }
                    let end = self.expect(&TokKind::RParen, "`)`")?;
                    Ok(Expr { kind: ExprKind::Call(name, args), span: sp.join(end) })
                } else {
                    Ok(Expr { kind: ExprKind::Var(name), span: sp })
                }
            }
            _ => self.err("expected an expression"),
        }
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
        let mut succ: Option<(String, String, Expr)> = None;
        while !matches!(self.peek(), TokKind::RBrace) {
            if self.eat_kw("Zero") {
                self.expect(&TokKind::FatArrow, "`=>`")?;
                if zero.replace(self.expr()?).is_some() {
                    return self.err("duplicate `Zero` arm");
                }
            } else if self.eat_kw("Succ") {
                self.expect(&TokKind::LParen, "`(`")?;
                let (k, _) = self.ident("predecessor name")?;
                self.expect(&TokKind::Comma, "`,`")?;
                let (ih, _) = self.ident("ih name")?;
                self.expect(&TokKind::RParen, "`)`")?;
                self.expect(&TokKind::FatArrow, "`=>`")?;
                if succ.replace((k, ih, self.expr()?)).is_some() {
                    return self.err("duplicate `Succ` arm");
                }
            } else {
                return self.err("expected `Zero` or `Succ(k, ih)` arm");
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        let (Some(zero), Some((k, ih, body))) = (zero, succ) else {
            return Err(ParseError {
                msg: "`match` needs both a `Zero` and a `Succ(k, ih)` arm".into(),
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
}
