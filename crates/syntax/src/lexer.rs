//! Hand-rolled lexer. `//` line comments; identifiers, numerals, and the
//! fixed punctuation set of the stage-1 grammar.

use heather_numeral::Numeral;
use crate::ast::{ScaledLit, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    Ident(String),
    Num(Numeral),
    /// `1.5`, `1e-3`, `0x1.8p3`: a numeral with a point or an exponent
    /// (docs/floating-point-design.md §15), held as its value.
    Scaled(ScaledLit),
    /// `'x'` — one Unicode scalar value (docs/string-char-design.md §3). The
    /// payload is Rust's `char`, which *is* the scalar-value type: the lexer
    /// refuses a surrogate escape, so nothing downstream has to re-check that
    /// a lexed character is a `Char`.
    Char(char),
    /// `"…"` — a sequence of scalar values, held decoded (escapes already
    /// resolved) for the same reason a numeral holds its value rather than
    /// its spelling: the radix, and here the escape, is a spelling.
    Str(String),
    /// `·` followed immediately by zero or more Unicode subscript digits.
    /// No subscript is the left-to-right anonymous mode; a subscript is an
    /// explicit zero-based argument position (issues/argument-slot-sections.md).
    ArgSlot(Option<u64>),
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
    Minus,     // -   (prefix negation or infix subtraction; `->` is matched first)
    Bang,      // !   (prefix Boolean negation; `!=` remains unsupported)
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
    /// Boolean-reflection delimiters: `⟦b⟧` is `bool::Bool::IsTrue(b)`.
    LSemantic, // ⟦
    RSemantic, // ⟧
    /// Anonymous constructor delimiters. `⟨a, b⟩` selects the sole
    /// constructor of the expected type; `⟨a |⟩` / `⟨| b⟩` select
    /// the first / second constructor of a binary sum.
    LAngle,    // ⟨
    RAngle,    // ⟩
    /// `|` — bitwise or (issues/integer-operator-symbols.md), and inside
    /// `⟨…⟩` the binary-sum injection mark (`⟨a |⟩`, `⟨| b⟩`). The parser
    /// tells the two apart: a `|` directly before `⟩` closes an injection
    /// and is never read as an operator.
    Pipe,      // |
    /// `&` — bitwise and (issues/integer-operator-symbols.md). `&&` is
    /// matched first, so a doubled ampersand is still the Boolean operator.
    Amp,       // &
    /// `/` — division. `//` is matched first and is a line comment, so
    /// `a // b` is `a` followed by a comment, exactly as in Rust.
    Slash,     // /
    Percent,   // %
    /// `<<` — left shift. Always one token: no type-argument list can begin
    /// with `<`, so two adjacent `<` have no other reading.
    Shl,       // <<
    /// `>>` — right shift, but **only when a space (or `(`, `,`, or the start
    /// of the file) comes before it**. A nested type-argument list closes as
    /// `List<List<A>>`, two `Gt`s hugging the argument, and that spelling is
    /// untouched: `>` is still never an operator by itself, and a tight `>>`
    /// is still two closers. `a >> b` is the shift; `a>>b` does not parse
    /// (issues/integer-operator-symbols.md).
    Shr,       // >>
    /// Function/implication arrow. `→` is the preferred mathematical
    /// spelling; `->` remains an ASCII alias and produces the same token.
    Arrow,     // → or ->
    FatArrow,  // =>
    /// `⊢` / `|-` — the turnstile of a contextual type `Code(g |- T)` and a
    /// checking-position sequent binder `x ⊢ body`. Both spellings become one
    /// token, so downstream syntax cannot assign them different semantics.
    /// `|-` is matched before a bare `|`, so `a |-b` is a turnstile: write
    /// `a | -b` for the bitwise or of a negation.
    Turnstile, // ⊢ or |-
    /// `&&` and `||` — the Boolean operator spellings
    /// (issues/bool-operator-designations.md). Two-byte, so they are matched
    /// before the bitwise `&` and `|`.
    AmpAmp,    // &&
    PipePipe,  // ||
    /// `∥` (U+2225, PARALLEL TO), the delimiter in `∥A∥`.
    NormBar,
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
    Approx,    // ≈ — relation notation, no fallback
    /// `^` — power, an infix operator on a rung of its own above `*`, and
    /// right-associative (docs/inverse-power-notation-design.md §2). ASCII,
    /// as Lean spells it: there is no Unicode power sign worth the typing.
    Caret,     // ^
    /// `⁻¹` (U+207B U+00B9) — the inverse, the grammar's one **postfix**
    /// operator. One token for the pair: `⁻` alone spells nothing, and
    /// lexing `¹` as a digit would invite `x⁻²`, which is `^` written
    /// differently. Five bytes, so it has a window of its own.
    SupInverse, // ⁻¹
    Join,      // ⊔ — additive-precedence operation notation, no fallback
    /// `⊓` — the meet beside `⊔`'s join, on the multiplicative rung as `∙`
    /// is, so `x ⊔ y ⊓ z` reads as `+` over `*` does. Notation only: like
    /// `⊔` it has no fallback name, so it means whatever index a binder
    /// spelled with it (`meet as ⊓`, `lib/std/algebra/lattice.hthr`).
    Meet,      // ⊓
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
    /// `<-` and `←` (U+2190): the bind of a binding statement, `let x <- e;`,
    /// and the nested bind `(<- e)` (docs/sequencing-surface-design.md §3.1).
    /// `<-` is matched after `<->` takes its three bytes, so `a <-> b` is
    /// unchanged; `a<-b` for `a < -b` is written nowhere in the library.
    LArrow,    // ←   (and `<-`)
    Exists,    // ∃
    /// `∑` (U+2211) and `∏` (U+220F) — the big-operator binders, `∑ k < n, e`
    /// (issues/notation-extensibility.md, the one binder production). Three
    /// bytes each, matched in the three-byte window beside `∃`.
    BigSum,    // ∑
    BigProd,   // ∏
    /// `↑` (U+2191) — a cast (docs/casting-design.md §5.2, §14): a prefix
    /// operator whose target the checking position supplies. Three bytes,
    /// matched beside `∑`.
    UpArrow,   // ↑
    Forall,    // ∀
    /// `$` — splice, inside a `code { … }` quote (`$x`, `${e}`) and in type
    /// position for a `TyCode` binder (`[$a; $k]`). The splice *form* is
    /// decided by the parser; the lexer only knows the sigil.
    Dollar,    // $
    /// `λ` (U+03BB). `fun` is the ASCII synonym and stays an `Ident`, matched
    /// by the parser's keyword helpers (docs/surface-function-types.md §3.2).
    Lambda,
    Eq,        // =   (both `let x = e` binding and `a = b` equality)
    /// `≠` (U+2260), the Unicode-only negated-equality spelling. It is a
    /// three-byte comparison token and desugars in the parser; there is no
    /// `!=` alias.
    Ne,
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

/// One numeral starting at `start` (an ASCII digit). Returns the value and
/// the byte offset just past the numeral.
///
/// Grammar: `0x` hexadecimal, `0o` octal, `0b` binary (lowercase prefix;
/// hex digits in either case), else decimal. A `_` may separate two digits
/// and may appear nowhere else — not after the prefix, not doubled, not
/// trailing. A numeral ends at the first byte that is not a digit,
/// letter, or `_`; a letter or `_` that cannot continue it is an error
/// rather than the start of the next token, so `0b12`, `0xfg`, `12abc`
/// and `1_` are all refused with the offending character named. The
/// value has no bound (docs/wide-numerals-design.md): a position that needs
/// a machine integer refuses a larger numeral itself, where it knows why.
fn lex_numeral(src: &str, start: usize) -> Result<(Lexed, usize), LexError> {
    let bytes = src.as_bytes();
    let (radix, name, mut i) = match (bytes[start], bytes.get(start + 1)) {
        (b'0', Some(b'x')) => (16u32, "hexadecimal", start + 2),
        (b'0', Some(b'o')) => (8, "octal", start + 2),
        (b'0', Some(b'b')) => (2, "binary", start + 2),
        _ => (10, "decimal", start),
    };
    let digits_start = i;
    let mut value = Numeral::ZERO;
    let mut digits = 0usize;
    let mut previous_was_separator = false;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'_' {
            // Between two digits, or nowhere: the byte before must be a
            // digit (rules out `0x_1` and `1__0`) and so must the byte
            // after (rules out `1_`).
            let after_digit = digits > 0 && !previous_was_separator;
            let before_digit = bytes.get(i + 1).is_some_and(|c| c.is_ascii_alphanumeric());
            if !after_digit || !before_digit {
                return Err(LexError {
                    msg: format!("a `_` in a numeral must sit between two digits: {}", &src[start..=i]),
                    span: Span { start: i, end: i + 1 },
                });
            }
            previous_was_separator = true;
            i += 1;
            continue;
        }
        if !(b.is_ascii_alphanumeric()) {
            break;
        }
        if digits > 0 && exponent_marker(bytes, i, radix) {
            break;
        }
        let digit = match (b as char).to_digit(36) {
            Some(d) if d < radix => u64::from(d),
            _ => {
                let bad = b as char;
                let msg = if radix == 10 && digits > 0 {
                    // `12abc`: a letter glued to a decimal numeral is
                    // not a suffix Heather knows.
                    format!("invalid digit `{bad}` in a decimal numeral: {}", &src[start..=i])
                } else {
                    format!("invalid digit `{bad}` in {} {name} numeral: {}", if name == "octal" { "an" } else { "a" }, &src[start..=i])
                };
                return Err(LexError { msg, span: Span { start: i, end: i + 1 } });
            }
        };
        value = value.mul_add(u64::from(radix), digit);
        digits += 1;
        previous_was_separator = false;
        i += 1;
    }
    if digits == 0 {
        // Only a radix prefix can get here: a decimal numeral starts with
        // a digit, which is its first digit.
        debug_assert!(radix != 10);
        return Err(LexError {
            msg: format!("`{}` needs at least one {name} digit", &src[start..digits_start]),
            span: Span { start, end: digits_start },
        });
    }
    let scaled = (radix == 10 || radix == 16)
        && ((bytes.get(i) == Some(&b'.') && fraction_follows(bytes, i, radix)) || exponent_marker(bytes, i, radix));
    if !scaled {
        return Ok((Lexed::Num(value), i));
    }
    // The fraction's digits extend the mantissa; each moves the point one
    // digit, a decimal place or four bits.
    let mut shift: i64 = 0;
    if bytes.get(i) == Some(&b'.') {
        i += 1;
        let mut previous_was_separator = true;
        while i < bytes.len() {
            let b = bytes[i];
            if b == b'_' && !previous_was_separator && bytes.get(i + 1).is_some_and(|c| (*c as char).is_digit(radix)) {
                previous_was_separator = true;
                i += 1;
                continue;
            }
            if exponent_marker(bytes, i, radix) {
                break;
            }
            let Some(d) = (b as char).to_digit(radix) else { break };
            value = value.mul_add(u64::from(radix), u64::from(d));
            shift -= if radix == 16 { 4 } else { 1 };
            previous_was_separator = false;
            i += 1;
        }
    }
    let mut exp: i64 = 0;
    if exponent_marker(bytes, i, radix) {
        i += 1;
        let negative = bytes[i] == b'-';
        if matches!(bytes[i], b'-' | b'+') {
            i += 1;
        }
        let exp_start = i;
        while i < bytes.len() && (bytes[i].is_ascii_digit() || (bytes[i] == b'_' && bytes.get(i + 1).is_some_and(u8::is_ascii_digit))) {
            if bytes[i] != b'_' {
                exp = exp.saturating_mul(10).saturating_add(i64::from(bytes[i] - b'0'));
            }
            i += 1;
        }
        if exp > i64::from(i32::MAX) {
            return Err(LexError {
                msg: format!("the exponent of `{}` is out of range", &src[start..i]),
                span: Span { start: exp_start, end: i },
            });
        }
        if negative {
            exp = -exp;
        }
    }
    if i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
        return Err(LexError {
            msg: format!("invalid character `{}` after the literal `{}`", bytes[i] as char, &src[start..i]),
            span: Span { start: i, end: i + 1 },
        });
    }
    Ok((Lexed::Scaled(ScaledLit { mant: value, exp: exp + shift, hex: radix == 16 }), i))
}

/// What a numeral lexed to: a whole number, or one with a point or an
/// exponent.
enum Lexed {
    Num(Numeral),
    Scaled(ScaledLit),
}

/// An exponent starts at `i`: `e`/`E` in a decimal numeral, `p`/`P` in a hex
/// one, followed by a digit or a signed digit. Anything else is not one, so
/// `1e` is still a bad digit and `1.e5` is not a literal.
fn exponent_marker(bytes: &[u8], i: usize, radix: u32) -> bool {
    let marker = match radix {
        10 => matches!(bytes.get(i), Some(b'e' | b'E')),
        16 => matches!(bytes.get(i), Some(b'p' | b'P')),
        _ => false,
    };
    let digit_at = |j: usize| bytes.get(j).is_some_and(u8::is_ascii_digit);
    marker && (digit_at(i + 1) || (matches!(bytes.get(i + 1), Some(b'+' | b'-')) && digit_at(i + 2)))
}

/// A point at `i` begins a fraction: a decimal point needs a digit after it
/// (so `1.method()` and `1..2` keep their meaning), and a hex point needs hex
/// digits and then a `p` exponent (so `0xff.f()` stays a method call).
fn fraction_follows(bytes: &[u8], i: usize, radix: u32) -> bool {
    let first = bytes.get(i + 1).is_some_and(|c| (*c as char).is_digit(radix));
    if radix == 10 || !first {
        return first;
    }
    let mut j = i + 1;
    while j < bytes.len() && ((bytes[j] as char).is_digit(16) || bytes[j] == b'_') {
        j += 1;
    }
    exponent_marker(bytes, j, 16)
}

/// One escape body, `i` pointing just past the `\`. Returns the scalar value
/// and the offset past the escape.
///
/// The set is `\n \t \r \\ \' \" \0` and `\u{hex}`
/// (docs/string-char-design.md §3) — deliberately small, and closed: a
/// spelling that is not in it is an error rather than a literal backslash, so
/// widening the set later cannot change what an existing file means.
fn lex_escape(src: &str, open: usize, i: usize) -> Result<(char, usize), LexError> {
    let bytes = src.as_bytes();
    let Some(&b) = bytes.get(i) else {
        return Err(LexError {
            msg: "a literal ends inside an escape".into(),
            span: Span { start: open, end: i },
        });
    };
    let simple = match b {
        b'n' => Some('\n'),
        b't' => Some('\t'),
        b'r' => Some('\r'),
        b'\\' => Some('\\'),
        b'\'' => Some('\''),
        b'"' => Some('"'),
        b'0' => Some('\0'),
        _ => None,
    };
    if let Some(c) = simple {
        return Ok((c, i + 1));
    }
    if b != b'u' {
        let bad = src[i..].chars().next().unwrap_or('\\');
        return Err(LexError {
            msg: format!(
                "unknown escape `\\{bad}`: the escapes are \\n \\t \\r \\\\ \\' \\\" \\0 and \\u{{hex}}"
            ),
            span: Span { start: i - 1, end: i + bad.len_utf8() },
        });
    }
    if bytes.get(i + 1) != Some(&b'{') {
        return Err(LexError {
            msg: "`\\u` needs a braced hexadecimal scalar value, as in `\\u{1F600}`".into(),
            span: Span { start: i - 1, end: i + 1 },
        });
    }
    let digits_start = i + 2;
    let mut end = digits_start;
    let mut value: u32 = 0;
    while let Some(&b) = bytes.get(end) {
        let Some(d) = (b as char).to_digit(16) else { break };
        value = value.checked_mul(16).and_then(|v| v.checked_add(d)).unwrap_or(u32::MAX);
        end += 1;
    }
    if end == digits_start || bytes.get(end) != Some(&b'}') {
        // The character that stopped the digits, whole: it need not be one
        // byte (`"\u{4∀"`), and a slice may not end inside it.
        let stop = end + src[end..].chars().next().map_or(0, char::len_utf8);
        return Err(LexError {
            msg: format!("`{}` is not a `\\u{{hex}}` escape", &src[i - 1..stop]),
            span: Span { start: i - 1, end: stop },
        });
    }
    let span = Span { start: i - 1, end: end + 1 };
    let text = &src[i - 1..end + 1];
    // `char::from_u32` is exactly the scalar-value predicate `std/char`
    // spells: below `0x110000` and not a surrogate. Refusing here is what
    // makes every lexed payload a `Char` by construction, so the literal's
    // elaboration never has a proof step that can fail.
    match char::from_u32(value) {
        Some(c) => Ok((c, end + 1)),
        None if (0xD800..0xE000).contains(&value) => Err(LexError {
            msg: format!(
                "`{text}` is a surrogate, not a Unicode scalar value: `Char` excludes \
                 `0xD800`–`0xDFFF` so that encoding stays injective"
            ),
            span,
        }),
        None => Err(LexError {
            msg: format!("`{text}` is above the last Unicode scalar value, `0x10FFFF`"),
            span,
        }),
    }
}

/// The body of a `'…'` or `"…"` literal. `open` points at the opening
/// delimiter; the returned offset is just past the closing one.
fn lex_quoted(src: &str, open: usize, delim: u8) -> Result<(String, usize), LexError> {
    let bytes = src.as_bytes();
    let what = if delim == b'\'' { "character" } else { "string" };
    let mut out = String::new();
    let mut i = open + 1;
    loop {
        let Some(&b) = bytes.get(i) else {
            return Err(LexError {
                msg: format!("unterminated {what} literal: no closing `{}`", delim as char),
                span: Span { start: open, end: open + 1 },
            });
        };
        if b == delim {
            return Ok((out, i + 1));
        }
        // A literal does not span lines. Reporting at the opening quote is
        // what makes a missing delimiter legible: without this the scan runs
        // to the end of the file and blames whatever it happens to stop at.
        if b == b'\n' {
            return Err(LexError {
                msg: format!("unterminated {what} literal: no closing `{}`", delim as char),
                span: Span { start: open, end: open + 1 },
            });
        }
        if b == b'\\' {
            let (c, next) = lex_escape(src, open, i + 1)?;
            out.push(c);
            i = next;
            continue;
        }
        let c = src[i..].chars().next().expect("a byte at `i` starts a character");
        out.push(c);
        i += c.len_utf8();
    }
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
            // `nat::Nat::sub` is **one** identifier token (docs/modules-design.md
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
        // numerals: decimal, or `0x`/`0o`/`0b` radix forms, with `_`
        // separators between digits (docs/radix-numerals-design.md). The
        // token carries only the value: a radix form is a *spelling* of the
        // same numeral, and everything downstream (carrier choice, the
        // emitted kernel term) is decided by the value alone.
        if c.is_ascii_digit() {
            let (n, end) = lex_numeral(src, start)?;
            i = end;
            let kind = match n {
                Lexed::Num(n) => TokKind::Num(n),
                Lexed::Scaled(s) => TokKind::Scaled(s),
            };
            toks.push(Tok { kind, span: Span { start, end: i } });
            continue;
        }
        // character and string literals (docs/string-char-design.md §3). One
        // syntax form each: `'x'` is a scalar value and `"…"` a sequence of
        // them, and neither delimiter had any other reading before this —
        // `'` and `"` were both "unexpected character".
        if c == b'\'' {
            let (text, end) = lex_quoted(src, start, b'\'')?;
            let mut chars = text.chars();
            let (Some(ch), None) = (chars.next(), chars.next()) else {
                return Err(LexError {
                    msg: format!(
                        "a character literal holds exactly one scalar value, and `{}` holds {}: \
                         write a string literal `\"…\"` for a sequence",
                        &src[start..end],
                        text.chars().count()
                    ),
                    span: Span { start, end },
                });
            };
            toks.push(Tok { kind: TokKind::Char(ch), span: Span { start, end } });
            i = end;
            continue;
        }
        if c == b'"' {
            let (text, end) = lex_quoted(src, start, b'"')?;
            toks.push(Tok { kind: TokKind::Str(text), span: Span { start, end } });
            i = end;
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
        if src.get(i..i + 5) == Some("⁻¹") {
            toks.push(Tok { kind: TokKind::SupInverse, span: Span { start, end: start + 5 } });
            i += 5;
            continue;
        }
        let three = src.get(i..i + 3).unwrap_or("");
        // `<->` is three ASCII bytes and so is matched here, before the
        // two-byte window could take a `<` off it. `<=` is unaffected: no
        // three-byte window spells it.
        let three_kind = match three {
            "∙" => Some(TokKind::Bullet),
            "≈" => Some(TokKind::Approx),
            "⊔" => Some(TokKind::Join),
            "⊓" => Some(TokKind::Meet),
            "∧" => Some(TokKind::Wedge),
            "∨" => Some(TokKind::Vee),
            "↔" | "<->" => Some(TokKind::Iff),
            "←" => Some(TokKind::LArrow),
            "∃" => Some(TokKind::Exists),
            "∑" => Some(TokKind::BigSum),
            "∏" => Some(TokKind::BigProd),
            "↑" => Some(TokKind::UpArrow),
            "∀" => Some(TokKind::Forall),
            "≠" => Some(TokKind::Ne),
            "⊢" => Some(TokKind::Turnstile),
            "→" => Some(TokKind::Arrow),
            "∥" => Some(TokKind::NormBar),
            "⟨" => Some(TokKind::LAngle),
            "⟩" => Some(TokKind::RAngle),
            "⟦" => Some(TokKind::LSemantic),
            "⟧" => Some(TokKind::RSemantic),
            _ => None,
        };
        if let Some(kind) = three_kind {
            toks.push(Tok { kind, span: Span { start, end: start + 3 } });
            i += 3;
            continue;
        }
        let two = src.get(i..i + 2).unwrap_or("");
        // `!` is Boolean negation, but `!=` is deliberately not an ASCII
        // alias for `≠`: keep diagnosing the pair at the lexer boundary
        // instead of tokenizing it as two unrelated operators.
        if two == "!=" {
            return Err(LexError {
                msg: "unexpected character '!' in `!=`; write `≠` for inequality".into(),
                span: Span { start, end: start + 2 },
            });
        }
        // `·`, U+00B7 MIDDLE DOT, is deliberately distinct from `∙`, the
        // generic infix bullet. Consume an immediately adjacent run of
        // Unicode subscript digits into the same token: adjacency and the
        // subscript alphabet make `·₁₂` unambiguously slot 12 while `·12`
        // remains a slot followed by an ordinary numeral.
        if two == "·" {
            i += 2;
            let mut index = 0u64;
            let mut indexed = false;
            while let Some(ch) = src.get(i..).and_then(|s| s.chars().next()) {
                let digit = match ch {
                    '₀' => 0,
                    '₁' => 1,
                    '₂' => 2,
                    '₃' => 3,
                    '₄' => 4,
                    '₅' => 5,
                    '₆' => 6,
                    '₇' => 7,
                    '₈' => 8,
                    '₉' => 9,
                    _ => break,
                };
                indexed = true;
                index = index
                    .checked_mul(10)
                    .and_then(|n| n.checked_add(digit))
                    .ok_or_else(|| LexError {
                        msg: "argument-slot index is out of range".into(),
                        span: Span { start, end: i + ch.len_utf8() },
                    })?;
                i += ch.len_utf8();
            }
            toks.push(Tok {
                kind: TokKind::ArgSlot(indexed.then_some(index)),
                span: Span { start, end: i },
            });
            continue;
        }
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
            "<-" => (TokKind::LArrow, 2),
            ":=" => (TokKind::ColonEq, 2),
            "::" => (TokKind::ColonColon, 2),
            "<<" => (TokKind::Shl, 2),
            // `>>` is a shift only after a space, `(`, `,` or the start of
            // the file; anywhere else it is two closers (see [`TokKind::Shr`]).
            ">>" if start == 0 || matches!(bytes[start - 1], b'(' | b',') || bytes[start - 1].is_ascii_whitespace() => {
                (TokKind::Shr, 2)
            }
            _ => match c {
                b'(' => (TokKind::LParen, 1),
                b')' => (TokKind::RParen, 1),
                b'{' => (TokKind::LBrace, 1),
                b'}' => (TokKind::RBrace, 1),
                b'[' => (TokKind::LBracket, 1),
                b']' => (TokKind::RBracket, 1),
                b'|' => (TokKind::Pipe, 1),
                b'&' => (TokKind::Amp, 1),
                b'/' => (TokKind::Slash, 1),
                b'%' => (TokKind::Percent, 1),
                b',' => (TokKind::Comma, 1),
                b':' => (TokKind::Colon, 1),
                b';' => (TokKind::Semi, 1),
                b'@' => (TokKind::At, 1),
                b'$' => (TokKind::Dollar, 1),
                b'.' => (TokKind::Dot, 1),
                b'+' => (TokKind::Plus, 1),
                b'-' => (TokKind::Minus, 1),
                b'!' => (TokKind::Bang, 1),
                b'*' => (TokKind::Star, 1),
                b'^' => (TokKind::Caret, 1),
                b'<' => (TokKind::Lt, 1),
                b'>' => (TokKind::Gt, 1),
                b'=' => (TokKind::Eq, 1),
                _ => {
                    // The whole character, not its first byte: `δ` is two.
                    let ch = src[start..].chars().next().unwrap_or(c as char);
                    return Err(LexError {
                        msg: format!("unexpected character {ch:?}"),
                        span: Span { start, end: start + ch.len_utf8() },
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

#[cfg(test)]
mod tests {
    use super::*;

    fn num(src: &str) -> u64 {
        let toks = lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
        assert_eq!(toks.len(), 2, "{src}: one numeral then Eof, got {toks:?}");
        let TokKind::Num(n) = &toks[0].kind else { panic!("{src}: not a numeral: {:?}", toks[0]) };
        assert_eq!(toks[0].span, Span { start: 0, end: src.len() });
        n.as_u64().expect("a numeral that fits in 64 bits")
    }

    fn scaled(src: &str) -> (u64, i64, bool) {
        let toks = lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
        assert_eq!(toks.len(), 2, "{src}: one literal then Eof, got {toks:?}");
        let TokKind::Scaled(lit) = &toks[0].kind else { panic!("{src}: not a scaled literal: {:?}", toks[0]) };
        (lit.mant.as_u64().expect("a mantissa that fits in 64 bits"), lit.exp, lit.hex)
    }

    fn kinds(src: &str) -> Vec<TokKind> {
        lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)).into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn integer_operator_symbols_lex() {
        use TokKind::*;
        assert_eq!(kinds("a / b % c & d | e << f"), [
            Ident("a".into()), Slash, Ident("b".into()), Percent, Ident("c".into()), Amp,
            Ident("d".into()), Pipe, Ident("e".into()), Shl, Ident("f".into()), Eof,
        ]);
        // `>>` is a shift after a space, `(` or `,`, and two closers when tight.
        assert_eq!(kinds("a >> b"), [Ident("a".into()), Shr, Ident("b".into()), Eof]);
        assert_eq!(kinds("(>>)"), [LParen, Shr, RParen, Eof]);
        assert_eq!(kinds("A>>"), [Ident("A".into()), Gt, Gt, Eof]);
        // The doubles and the comment are matched first.
        assert_eq!(kinds("&& || // c"), [AmpAmp, PipePipe, Eof]);
    }

    #[test]
    fn decimal_and_hex_floats_lex_to_their_values() {
        assert_eq!(scaled("1.5"), (15, -1, false));
        assert_eq!(scaled("0.1"), (1, -1, false));
        assert_eq!(scaled("1e-3"), (1, -3, false));
        assert_eq!(scaled("1E+3"), (1, 3, false));
        assert_eq!(scaled("12.345e-6"), (12345, -9, false));
        assert_eq!(scaled("1_000.000_1"), (10000001, -4, false));
        assert_eq!(scaled("0x1.8p3"), (0x18, -1, true));
        assert_eq!(scaled("0x1p-1074"), (1, -1074, true));
        assert_eq!(scaled("0xA.Bp0"), (0xAB, -4, true));
    }

    #[test]
    fn a_point_needs_a_digit_after_it_to_start_a_fraction() {
        // A method call, a range and a projection keep their meaning.
        assert!(matches!(kinds("1.foo")[..], [TokKind::Num(_), TokKind::Dot, TokKind::Ident(_), TokKind::Eof]));
        assert!(matches!(kinds("1..2")[0], TokKind::Num(_)));
        // A hex point is a fraction only when a `p` exponent follows.
        assert!(matches!(kinds("0xff.f")[..], [TokKind::Num(_), TokKind::Dot, TokKind::Ident(_), TokKind::Eof]));
        assert_eq!(num("0xe"), 14);
    }

    #[test]
    fn a_malformed_float_is_refused() {
        assert!(refused("1e").contains("invalid digit `e`"));
        assert!(refused("1.5e").contains("after the literal"));
        assert!(refused("1.5x").contains("after the literal"));
        assert!(refused("1e99999999999").contains("out of range"));
    }

    fn refused(src: &str) -> String {
        match lex(src) {
            Ok(toks) => panic!("{src} lexed: {toks:?}"),
            Err(e) => e.msg,
        }
    }

    #[test]
    fn an_unexpected_non_ascii_character_is_reported_whole() {
        // Identifiers are ASCII; a Greek letter is refused as itself, and its
        // span covers both of its bytes so a snippet never cuts it in half.
        let e = lex("theorem t(δ: Type)").unwrap_err();
        assert!(e.msg.contains("'δ'"), "{}", e.msg);
        assert_eq!(e.span.end - e.span.start, 'δ'.len_utf8());
    }

    #[test]
    fn radix_forms_denote_the_decimal_value() {
        assert_eq!(num("72"), 72);
        assert_eq!(num("0x48"), 72);
        assert_eq!(num("0xFF"), 255);
        assert_eq!(num("0xfF"), 255);
        assert_eq!(num("0b1001000"), 72);
        assert_eq!(num("0o110"), 72);
        assert_eq!(num("0"), 0);
        assert_eq!(num("0x0"), 0);
        assert_eq!(num("0b0"), 0);
    }

    #[test]
    fn separators_sit_between_digits_in_every_radix() {
        assert_eq!(num("1_000_000"), 1_000_000);
        assert_eq!(num("0xFFFF_FFFF"), 0xFFFF_FFFF);
        assert_eq!(num("0b0000_0111"), 7);
        assert_eq!(num("0o7_7"), 63);
    }

    #[test]
    fn misplaced_separators_are_named() {
        for src in ["1_", "1__0", "0x_1", "0b_", "0x1_"] {
            let msg = refused(src);
            assert!(msg.contains("must sit between two digits"), "{src}: {msg}");
        }
        // `_1` is an identifier, not a numeral with a leading separator.
        let toks = lex("_1").unwrap();
        assert!(matches!(&toks[0].kind, TokKind::Ident(s) if s == "_1"));
    }

    #[test]
    fn invalid_digits_are_named_with_the_radix() {
        assert!(refused("0b12").contains("invalid digit `2` in a binary numeral"));
        assert!(refused("0o8").contains("invalid digit `8` in an octal numeral"));
        assert!(refused("0xfg").contains("invalid digit `g` in a hexadecimal numeral"));
        assert!(refused("12abc").contains("invalid digit `a` in a decimal numeral"));
        // An uppercase prefix is not a prefix.
        assert!(refused("0X48").contains("invalid digit `X` in a decimal numeral"));
    }

    #[test]
    fn a_bare_prefix_needs_a_digit() {
        assert_eq!(refused("0x"), "`0x` needs at least one hexadecimal digit");
        assert_eq!(refused("0b"), "`0b` needs at least one binary digit");
        assert_eq!(refused("0o"), "`0o` needs at least one octal digit");
        assert!(refused("0x)").starts_with("`0x` needs"));
    }

    /// A numeral has no bound (docs/wide-numerals-design.md): `u64::MAX` and
    /// one past it read the same way in every radix.
    #[test]
    fn a_numeral_past_a_machine_word_reads_in_every_radix() {
        assert_eq!(num("18446744073709551615"), u64::MAX);
        assert_eq!(num("0xFFFF_FFFF_FFFF_FFFF"), u64::MAX);
        assert_eq!(num("0b1111111111111111111111111111111111111111111111111111111111111111"), u64::MAX);
        assert_eq!(num("0o1777777777777777777777"), u64::MAX);
        let two64 = Numeral::from_limbs(vec![0, 1]);
        for src in [
            "18446744073709551616",
            "0x1_0000_0000_0000_0000",
            "0b10000000000000000000000000000000000000000000000000000000000000000",
            "0o2000000000000000000000",
        ] {
            let toks = lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
            assert!(matches!(&toks[0].kind, TokKind::Num(n) if *n == two64), "{src}: {toks:?}");
        }
        let toks = lex("340282366920938463463374607431768211456").unwrap();
        assert!(matches!(&toks[0].kind, TokKind::Num(n) if n.to_string() == "340282366920938463463374607431768211456"));
    }

    fn chr(src: &str) -> char {
        let toks = lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
        assert_eq!(toks.len(), 2, "{src}: one literal then Eof, got {toks:?}");
        let TokKind::Char(c) = toks[0].kind else {
            panic!("{src}: not a character literal: {:?}", toks[0])
        };
        assert_eq!(toks[0].span, Span { start: 0, end: src.len() });
        c
    }

    fn text(src: &str) -> String {
        let toks = lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
        assert_eq!(toks.len(), 2, "{src}: one literal then Eof, got {toks:?}");
        let TokKind::Str(s) = &toks[0].kind else {
            panic!("{src}: not a string literal: {:?}", toks[0])
        };
        assert_eq!(toks[0].span, Span { start: 0, end: src.len() });
        s.clone()
    }

    #[test]
    fn literals_hold_scalar_values_and_not_their_spelling() {
        assert_eq!(chr("'x'"), 'x');
        assert_eq!(chr("'é'"), 'é');
        assert_eq!(chr("'\u{1F600}'"), '\u{1F600}');
        assert_eq!(chr(r"'\u{1F600}'"), '\u{1F600}');
        assert_eq!(chr(r"'\u{41}'"), 'A');
        assert_eq!(text(r#""hi""#), "hi");
        assert_eq!(text(r#""""#), "");
        assert_eq!(text(r#""λx. x""#), "λx. x");
    }

    #[test]
    fn the_escape_set_is_the_documented_one() {
        assert_eq!(chr(r"'\n'"), '\n');
        assert_eq!(chr(r"'\t'"), '\t');
        assert_eq!(chr(r"'\r'"), '\r');
        assert_eq!(chr(r"'\\'"), '\\');
        assert_eq!(chr(r"'\''"), '\'');
        assert_eq!(chr(r#"'\"'"#), '"');
        assert_eq!(chr(r"'\0'"), '\0');
        assert_eq!(text(r#""a\nb\\c\"d""#), "a\nb\\c\"d");
        assert!(refused(r"'\q'").starts_with("unknown escape `\\q`"));
        assert!(refused(r"'\u41'").contains("braced hexadecimal"));
        assert!(refused(r"'\u{}'").contains("is not a `\\u{hex}` escape"));
        assert!(refused(r"'\u{41'").contains("is not a `\\u{hex}` escape"));
    }

    #[test]
    fn a_surrogate_escape_is_refused_at_the_lexer() {
        for src in [r"'\u{D800}'", r"'\u{dfff}'", r#""a\u{D9AB}b""#] {
            let msg = refused(src);
            assert!(msg.contains("is a surrogate"), "{src}: {msg}");
        }
        // The two neighbours of the excluded block still lex.
        assert_eq!(chr(r"'\u{D7FF}'"), '\u{D7FF}');
        assert_eq!(chr(r"'\u{E000}'"), '\u{E000}');
        assert!(refused(r"'\u{110000}'").contains("above the last Unicode scalar value"));
        assert_eq!(chr(r"'\u{10FFFF}'"), '\u{10FFFF}');
    }

    #[test]
    fn a_malformed_scalar_escape_is_reported_up_to_a_whole_character() {
        // What stops the digits is quoted with them, and it may be wider
        // than a byte: the report ends after it, not inside it.
        assert_eq!(refused("\"\\u{4g}\""), "`\\u{4g` is not a `\\u{hex}` escape");
        assert_eq!(refused("\"\\u{4∀}\""), "`\\u{4∀` is not a `\\u{hex}` escape");
        assert_eq!(refused("\"\\u{→"), "`\\u{→` is not a `\\u{hex}` escape");
        assert_eq!(refused("\"\\u{41"), "`\\u{41` is not a `\\u{hex}` escape");
    }

    #[test]
    fn an_unterminated_literal_names_its_opening_quote() {
        for (src, what) in [("'x", "character"), ("\"hi", "string"), ("'x\ny'", "character")] {
            let msg = refused(src);
            assert!(msg.contains(&format!("unterminated {what} literal")), "{src}: {msg}");
        }
        assert_eq!(
            lex("\"hi").unwrap_err().span,
            Span { start: 0, end: 1 },
            "the span is the opening quote"
        );
        assert!(refused("''").contains("exactly one scalar value"));
        assert!(refused("'ab'").contains("exactly one scalar value"));
    }

    #[test]
    fn a_literal_ends_at_punctuation() {
        let toks = lex("f('a', \"bc\", 1)").unwrap();
        let kinds: Vec<_> = toks.iter().map(|t| &t.kind).collect();
        assert!(matches!(kinds[2], TokKind::Char('a')), "{kinds:?}");
        assert!(matches!(kinds[4], TokKind::Str(s) if s == "bc"), "{kinds:?}");
        assert!(matches!(&kinds[6], TokKind::Num(n) if n.as_u64() == Some(1)), "{kinds:?}");
    }

    #[test]
    fn a_numeral_ends_at_punctuation() {
        let toks = lex("f(0x48, 0b1)").unwrap();
        let kinds: Vec<_> = toks.iter().map(|t| &t.kind).collect();
        assert!(matches!(&kinds[2], TokKind::Num(n) if n.as_u64() == Some(72)), "{kinds:?}");
        assert!(matches!(&kinds[4], TokKind::Num(n) if n.as_u64() == Some(1)), "{kinds:?}");
    }
}
