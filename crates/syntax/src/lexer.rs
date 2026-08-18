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
    /// `++` — list append notation (issues/list-append-symbol.md). Like the
    /// Boolean doubles, it has no single-name fallback: a designation or a
    /// binder supplies its meaning.
    PlusPlus,  // ++
    Star,      // *
    Lt,        // <
    /// `<=` — the ordering comparison, desugared to `Le(n, m)` by the parser.
    ///
    /// Two-byte, so it is matched *before* `<`. That cannot steal a `<` from
    /// the generics path: a type-argument list is `<` followed by a type, and
    /// no type starts with `=` (`Foo<=` is not a program today and is not one
    /// after this either), so the only `<=` in a well-formed file is the
    /// operator (issues/comparison-operators.md).
    LtEq,      // <=
    Gt,        // >   (closes a type-argument list; `>` is not an operator)
    LBracket,  // [
    RBracket,  // ]
    Arrow,     // ->
    FatArrow,  // =>
    /// `|-` — the turnstile of a contextual type `Code(g |- T)`. Two-byte like
    /// `->`; a bare `|` stays a lex error, so nothing existing changes shape.
    Turnstile, // |-
    /// `&&` and `||` — the Boolean operator spellings
    /// (issues/bool-operator-designations.md). Two-byte; the bare `&` and `|`
    /// stay lex errors, deliberately: the single characters are unclaimed
    /// tokens (`|` in particular is reserved against a future or-pattern),
    /// and doubling is what keeps them so.
    AmpAmp,    // &&
    PipePipe,  // ||
    /// `∙` (U+2219, BULLET OPERATOR) — the **reserved generic** operator
    /// (issues/notation-extensibility.md, log 2026-08-09). One token, no
    /// designation row anywhere in the library, and no fallback name, so rungs
    /// 2 and 3 of the resolution ladder can never fire for it: away from a
    /// binder that named it, `∙` *cannot* mean anything. That is the whole
    /// point — it is the right spelling for bare `Semigroup`/`Monoid` theory,
    /// where `+` would whisper commutativity over `append`.
    ///
    /// Three bytes, so it is matched in a window of its own; the two-byte
    /// window would land mid-codepoint and see nothing.
    Bullet,    // ∙
    /// The propositional connectives (issues/std-logic-module.md). Unicode is
    /// the spelling, not an alternative to an ASCII digraph set: `λ` and `∙`
    /// already lex, so this follows the precedent rather than setting one.
    /// `<->` is the single deliberate ASCII survivor — it is the connective
    /// people reach for casually — and it lexes to the same [`TokKind::Iff`],
    /// so nothing downstream can tell the two apart.
    ///
    /// `¬` (U+00AC) is two bytes; the other four are three, so they are
    /// matched in the three-byte window beside `∙`.
    Neg,       // ¬
    Wedge,     // ∧
    Vee,       // ∨
    Iff,       // ↔   (and `<->`)
    Exists,    // ∃
    Forall,    // ∀
    /// `$` — splice, inside a `code { … }` quote (`$x`, `${e}`) and in type
    /// position for a `TyCode` binder (`[$a; $k]`). The splice *form* is
    /// decided by the parser; the lexer only knows the sigil.
    Dollar,    // $
    /// `λ` (U+03BB). `fun` is the ASCII synonym and stays an `Ident`, matched
    /// by the parser's keyword helpers (docs/surface-function-types.md §3.2).
    Lambda,
    Eq,        // =   (both `let x = e` binding and `a = b` equality)
    EqEq,      // ==  (lexed but rejected by the parser — see `=`)
    ColonEq,   // :=
    /// `::` — qualification (docs/modules-design.md §4). Only ever *seen* by
    /// the parser in `import m::{a, b};`: a `::` between two identifiers is
    /// joined into a single qualified [`TokKind::Ident`] here (see the
    /// identifier rule), because a qualified name is one name and no
    /// expression may come between its halves. Two-byte, so it is matched
    /// before `:`; `::` was a parse error everywhere before this token
    /// existed, so nothing that lexed changes shape.
    ColonColon, // ::
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
            // `nat::sub` is **one** identifier token (docs/modules-design.md
            // §4). Adjacency decides, as it does for `?name`: a `::` followed
            // by an identifier start joins, so `nat::{Le}` (the import-list
            // form) still lexes as `nat` `::` `{`.
            //
            // A **chain**, not one join (2026-08-17,
            // docs/instance-resolved-key-design.md §5). Module names are
            // single-segment, so for a long time one join was the whole
            // grammar; a *member of a member's* namespace is three segments —
            // `int::Le::Decide` is the module, the carrier and the class — and
            // is now the printed form of a name the registry hands out, so it
            // has to be writable verbatim (docs/repr-access-spellings-design.md
            // §2's invariant). The loop is the whole change: what a joined name
            // *means* is decided by `names::resolve_kinds` against the tables,
            // exactly as it was for two segments, and `split_qual`'s
            // first-`::` split already reads a three-segment name as
            // (qualifier, declared name).
            //
            // Nothing regressed by widening this: a standalone `::` after an
            // identifier was a parse error in every expression position
            // (`Parser`'s postfix `::` arm needs an *applied* owner,
            // `Impl(add, BinNat)::refines`, which ends in `)` and never
            // reaches here).
            while src.get(i..i + 2) == Some("::")
                && bytes.get(i + 2).is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_')
            {
                i += 2;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
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
        // The three-byte window comes first, and for the same reason the
        // two-byte one exists: `∙` (U+2219) is three bytes, so no shorter
        // window can see it. `get` again rather than an index — a window that
        // runs off the end, or lands inside a codepoint, simply means "not a
        // token of this width".
        let three = src.get(i..i + 3).unwrap_or("");
        // `<->` is three ASCII bytes and so is matched here, before the
        // two-byte window could take a `<` off it. `<=` is unaffected: no
        // three-byte window spells it.
        let three_kind = match three {
            "∙" => Some(TokKind::Bullet),
            "∧" => Some(TokKind::Wedge),
            "∨" => Some(TokKind::Vee),
            "↔" | "<->" => Some(TokKind::Iff),
            "∃" => Some(TokKind::Exists),
            "∀" => Some(TokKind::Forall),
            _ => None,
        };
        if let Some(kind) = three_kind {
            toks.push(Tok { kind, span: Span { start, end: start + 3 } });
            i += 3;
            continue;
        }
        let two = src.get(i..i + 2).unwrap_or("");
        let (kind, len) = match two {
            // `λ` (U+03BB) is two bytes and is *not* an identifier character,
            // so it lexes here rather than in the identifier rule above.
            // `fun` is the ASCII synonym and is an ordinary keyword.
            "λ" => (TokKind::Lambda, 2),
            // `¬` (U+00AC), two bytes like `λ` and for the same reason it
            // cannot lex as an identifier character.
            "¬" => (TokKind::Neg, 2),
            "->" => (TokKind::Arrow, 2),
            "|-" => (TokKind::Turnstile, 2),
            "&&" => (TokKind::AmpAmp, 2),
            "||" => (TokKind::PipePipe, 2),
            "++" => (TokKind::PlusPlus, 2),
            "=>" => (TokKind::FatArrow, 2),
            "==" => (TokKind::EqEq, 2),
            "<=" => (TokKind::LtEq, 2),
            ":=" => (TokKind::ColonEq, 2),
            "::" => (TokKind::ColonColon, 2),
            _ => match c {
                b'(' => (TokKind::LParen, 1),
                b')' => (TokKind::RParen, 1),
                b'{' => (TokKind::LBrace, 1),
                b'}' => (TokKind::RBrace, 1),
                b'[' => (TokKind::LBracket, 1),
                b']' => (TokKind::RBracket, 1),
                b',' => (TokKind::Comma, 1),
                b':' => (TokKind::Colon, 1),
                b';' => (TokKind::Semi, 1),
                b'@' => (TokKind::At, 1),
                b'$' => (TokKind::Dollar, 1),
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
