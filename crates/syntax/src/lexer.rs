//! Hand-rolled lexer. `//` line comments; identifiers, numerals, and the
//! fixed punctuation set of the stage-1 grammar.

use crate::ast::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    Ident(String),
    Num(u64),
    /// `?name` (named goal) or bare `?` (anonymous goal). Named-vs-anonymous
    /// is decided here, by *adjacency*: `?p` is the hole `p`, `? p` is an
    /// anonymous hole followed by the variable `p`. Settling it in the lexer
    /// means the parser never has to (issues/goal-holes.md).
    Hole(Option<String>),
    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Semi,      // ;
    At,        // @
    Dot,       // .
    Plus,      // +
    Star,      // *
    Lt,        // <
    Gt,        // >   (closes a type-argument list; `>` is not an operator)
    Arrow,     // ->
    FatArrow,  // =>
    /// `λ` (U+03BB). `fun` is the ASCII synonym and stays an `Ident`, matched
    /// by the parser's keyword helpers (docs/surface-function-types.md §3.2).
    Lambda,
    Eq,        // =   (both `let x = e` binding and `a = b` equality)
    EqEq,      // ==  (lexed but rejected by the parser — see `=`)
    ColonEq,   // :=
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
        // goal holes: `?name` if an identifier follows immediately, else `?`
        if c == b'?' {
            i += 1;
            let name_start = i;
            if i < bytes.len() && (bytes[i].is_ascii_alphabetic() || bytes[i] == b'_') {
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
            }
            let name = (i > name_start).then(|| src[name_start..i].to_string());
            toks.push(Tok { kind: TokKind::Hole(name), span: Span { start, end: i } });
            continue;
        }
        // punctuation
        // `get` rather than an index: the two-byte window can land *inside* a
        // multi-byte codepoint (`(λ` puts `λ`'s first byte at `i + 1`), and
        // slicing there panics. A non-boundary simply means "not a two-byte
        // token".
        let two = src.get(i..i + 2).unwrap_or("");
        let (kind, len) = match two {
            // `λ` (U+03BB) is two bytes and is *not* an identifier character,
            // so it lexes here rather than in the identifier rule above.
            // `fun` is the ASCII synonym and is an ordinary keyword.
            "λ" => (TokKind::Lambda, 2),
            "->" => (TokKind::Arrow, 2),
            "=>" => (TokKind::FatArrow, 2),
            "==" => (TokKind::EqEq, 2),
            ":=" => (TokKind::ColonEq, 2),
            _ => match c {
                b'(' => (TokKind::LParen, 1),
                b')' => (TokKind::RParen, 1),
                b'{' => (TokKind::LBrace, 1),
                b'}' => (TokKind::RBrace, 1),
                b',' => (TokKind::Comma, 1),
                b':' => (TokKind::Colon, 1),
                b';' => (TokKind::Semi, 1),
                b'@' => (TokKind::At, 1),
                b'.' => (TokKind::Dot, 1),
                b'+' => (TokKind::Plus, 1),
                b'*' => (TokKind::Star, 1),
                b'<' => (TokKind::Lt, 1),
                b'>' => (TokKind::Gt, 1),
                b'=' => (TokKind::Eq, 1),
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
