//! Hand-rolled lexer. `//` line comments; identifiers, numerals, and the
//! fixed punctuation set of the stage-1 grammar.

use crate::ast::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    Ident(String),
    Num(u64),
    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    At,        // @
    Arrow,     // ->
    FatArrow,  // =>
    EqEq,      // ==
    Eof,
}

#[derive(Debug, Clone)]
pub struct Tok {
    pub kind: TokKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LexError {
    pub msg: String,
    pub span: Span,
}

pub fn lex(src: &str) -> Result<Vec<Tok>, LexError> {
    let bytes = src.as_bytes();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        // whitespace
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // line comments
        if c == b'/' && bytes.get(i + 1) == Some(&b'/') {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        // identifiers / keywords
        if c.is_ascii_alphabetic() || c == b'_' {
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let text = &src[start..i];
            toks.push(Tok {
                kind: TokKind::Ident(text.to_string()),
                span: Span { start, end: i },
            });
            continue;
        }
        // numerals
        if c.is_ascii_digit() {
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let text = &src[start..i];
            let n: u64 = text.parse().map_err(|_| LexError {
                msg: format!("numeral out of range: {text}"),
                span: Span { start, end: i },
            })?;
            toks.push(Tok { kind: TokKind::Num(n), span: Span { start, end: i } });
            continue;
        }
        // punctuation
        let two = if i + 1 < bytes.len() { &src[i..i + 2] } else { "" };
        let (kind, len) = match two {
            "->" => (TokKind::Arrow, 2),
            "=>" => (TokKind::FatArrow, 2),
            "==" => (TokKind::EqEq, 2),
            _ => match c {
                b'(' => (TokKind::LParen, 1),
                b')' => (TokKind::RParen, 1),
                b'{' => (TokKind::LBrace, 1),
                b'}' => (TokKind::RBrace, 1),
                b',' => (TokKind::Comma, 1),
                b':' => (TokKind::Colon, 1),
                b'@' => (TokKind::At, 1),
                _ => {
                    return Err(LexError {
                        msg: format!("unexpected character {:?}", c as char),
                        span: Span { start, end: start + 1 },
                    })
                }
            },
        };
        toks.push(Tok { kind, span: Span { start, end: start + len } });
        i += len;
    }
    toks.push(Tok { kind: TokKind::Eof, span: Span { start: i, end: i } });
    Ok(toks)
}
