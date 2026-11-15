//! Hand-rolled lexer. `//` line comments; identifiers, numerals, and the
//! fixed punctuation set of the stage-1 grammar.

use heather_numeral::Numeral;
use crate::ast::{ScaledLit, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    Ident(String),
    Num(Numeral),
    /// `42u64`, `0x80u8`, `7i32`: a whole numeral glued to a width-family
    /// name, held as its value and the name (issues/integer-literal-width-suffix.md).
    /// The name is the type: `42u64` means `42` read at `u64`, whatever stands
    /// around it. A suffix is `u` or `i` and a decimal width, so it is never a
    /// hexadecimal digit and `0x1fi8` is `0x1f` at `i8`.
    SuffixedNum(Numeral, String),
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
    /// `⊕` (U+2295, CIRCLED PLUS) — exclusive or
    /// (issues/bitvec-xor-complement-symbols.md), on a rung of its own
    /// between `|` and `&`, as Rust's `^` sits; `^` is power here. Notation
    /// only: a designation gives it a meaning.
    OPlus,     // ⊕
    /// `~` — prefix bitwise complement, beside `-` and `!`. `!` is the
    /// Boolean negation and `¬` the proposition's, so a word's complement
    /// has a symbol of its own.
    Tilde,     // ~
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

// The messages a source is refused with, one function each, so that the
// lexer and a scanner's refusal ([`ScanRefusal`]) say the same thing at the
// same place: the lexer finds where, the scanner names it, and both build
// the error here.

fn refused(msg: String, start: usize, end: usize) -> LexError {
    LexError { msg, span: Span { start, end } }
}

/// The radix of the numeral at `start` and its name, by its prefix.
fn numeral_radix(bytes: &[u8], start: usize) -> (u32, &'static str) {
    match (bytes[start], bytes.get(start + 1)) {
        (b'0', Some(b'x')) => (16, "hexadecimal"),
        (b'0', Some(b'o')) => (8, "octal"),
        (b'0', Some(b'b')) => (2, "binary"),
        _ => (10, "decimal"),
    }
}

/// The byte at `at` is no digit of the numeral that starts at `start`.
fn digit_error(src: &str, start: usize, at: usize) -> LexError {
    let bad = src.as_bytes()[at] as char;
    let (_, name) = numeral_radix(src.as_bytes(), start);
    let article = if name == "octal" { "an" } else { "a" };
    refused(format!("invalid digit `{bad}` in {article} {name} numeral: {}", &src[start..=at]), at, at + 1)
}

/// The `_` at `at` does not sit between two digits.
fn underscore_error(src: &str, start: usize, at: usize) -> LexError {
    refused(format!("a `_` in a numeral must sit between two digits: {}", &src[start..=at]), at, at + 1)
}

/// The radix prefix at `start` has no digit after it.
fn no_digits_error(src: &str, start: usize) -> LexError {
    let (_, name) = numeral_radix(src.as_bytes(), start);
    refused(format!("`{}` needs at least one {name} digit", &src[start..start + 2]), start, start + 2)
}

/// The byte at `at` continues the literal that starts at `start` and ends
/// there.
fn after_literal_error(src: &str, start: usize, at: usize) -> LexError {
    refused(format!("invalid character `{}` after the literal `{}`", src.as_bytes()[at] as char, &src[start..at]), at, at + 1)
}

/// The width suffix whose letter is at `letter` has a leading zero, and its
/// digits end at `end`.
fn leading_zeros_error(src: &str, start: usize, letter: usize, end: usize) -> LexError {
    refused(format!("a width suffix is written without leading zeros: {}", &src[start..end]), letter, end)
}

/// The literal opened at `open` is closed by no delimiter on its line.
fn unterminated_error(open: usize, delim: u8) -> LexError {
    let what = if delim == b'\'' { "character" } else { "string" };
    refused(format!("unterminated {what} literal: no closing `{}`", delim as char), open, open + 1)
}

/// The character literal `start..end` holds `count` scalar values, not one.
fn char_count_error(src: &str, start: usize, end: usize, count: usize) -> LexError {
    refused(
        format!(
            "a character literal holds exactly one scalar value, and `{}` holds {count}: \
             write a string literal `\"…\"` for a sequence",
            &src[start..end]
        ),
        start,
        end,
    )
}

/// The source ends at `at`, after the `\` of an escape in the literal
/// opened at `open`.
fn escape_end_error(open: usize, at: usize) -> LexError {
    refused("a literal ends inside an escape".into(), open, at)
}

/// The character at `at`, after a `\`, begins no escape.
fn unknown_escape_error(src: &str, at: usize) -> LexError {
    let bad = src[at..].chars().next().unwrap_or('\\');
    refused(
        format!("unknown escape `\\{bad}`: the escapes are \\n \\t \\r \\\\ \\' \\\" \\0 and \\u{{hex}}"),
        at - 1,
        at + bad.len_utf8(),
    )
}

/// The `\u` whose `u` is at `at` has no `{` after it.
fn escape_brace_error(at: usize) -> LexError {
    refused("`\\u` needs a braced hexadecimal scalar value, as in `\\u{1F600}`".into(), at - 1, at + 1)
}

/// The `\u{…}` escape whose `\` is at `slash` is stopped at `at` by what is
/// no hexadecimal digit and no `}`.
fn escape_hex_error(src: &str, slash: usize, at: usize) -> LexError {
    // The character that stopped the digits, whole: it need not be one
    // byte (`"\u{4∀"`), and a slice may not end inside it.
    let stop = at + src[at..].chars().next().map_or(0, char::len_utf8);
    refused(format!("`{}` is not a `\\u{{hex}}` escape", &src[slash..stop]), slash, stop)
}

/// The character at `start` begins no token.
fn unexpected_error(src: &str, start: usize) -> LexError {
    // The whole character, not its first byte: `δ` is two.
    let ch = src[start..].chars().next().unwrap_or(src.as_bytes()[start] as char);
    refused(format!("unexpected character {ch:?}"), start, start + ch.len_utf8())
}

fn bang_eq_error(start: usize) -> LexError {
    refused("unexpected character '!' in `!=`; write `≠` for inequality".into(), start, start + 2)
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
    let (radix, _) = numeral_radix(bytes, start);
    let mut i = if radix == 10 { start } else { start + 2 };
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
                return Err(underscore_error(src, start, i));
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
        if digits > 0 && !previous_was_separator && width_suffix_at(bytes, i) {
            break;
        }
        let digit = match (b as char).to_digit(36) {
            Some(d) if d < radix => u64::from(d),
            // `12abc`: a letter glued to a decimal numeral is not a suffix
            // Heather knows.
            _ => return Err(digit_error(src, start, i)),
        };
        value = value.mul_add(u64::from(radix), digit);
        digits += 1;
        previous_was_separator = false;
        i += 1;
    }
    if digits == 0 {
        // Only a radix prefix can get here: a decimal numeral starts with
        // a digit, which is its first digit.
        debug_assert!(radix != 10 && digits_start == start + 2);
        return Err(no_digits_error(src, start));
    }
    if width_suffix_at(bytes, i) {
        return lex_width_suffix(src, start, i).map(|(suffix, end)| (Lexed::Suffixed(value, suffix), end));
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
        return Err(after_literal_error(src, start, i));
    }
    Ok((Lexed::Scaled(ScaledLit { mant: value, exp: exp + shift, hex: radix == 16 }), i))
}

/// What a numeral lexed to: a whole number, one with a width suffix, or one
/// with a point or an exponent.
enum Lexed {
    Num(Numeral),
    Suffixed(Numeral, String),
    Scaled(ScaledLit),
}

/// A width suffix starts at `i`: `u` or `i` and then a decimal digit
/// (issues/integer-literal-width-suffix.md). Neither letter is a digit in
/// any radix a numeral is written in, so the numeral before it has already
/// ended: `0x1fi8` is `0x1f` and `i8`.
fn width_suffix_at(bytes: &[u8], i: usize) -> bool {
    matches!(bytes.get(i), Some(b'u' | b'i')) && bytes.get(i + 1).is_some_and(u8::is_ascii_digit)
}

/// The width suffix at `at`, after the numeral that began at `start`: its
/// name (`u64`) and the offset past it. The width is written as a type name
/// is, without leading zeros, and the literal ends with it: `42u64x` is
/// refused as `12abc` is.
fn lex_width_suffix(src: &str, start: usize, at: usize) -> Result<(String, usize), LexError> {
    let bytes = src.as_bytes();
    let mut i = at + 1;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if bytes[at + 1] == b'0' && i > at + 2 {
        return Err(leading_zeros_error(src, start, at, i));
    }
    if i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
        return Err(after_literal_error(src, start, i));
    }
    Ok((src[at..i].to_string(), i))
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
        return Err(escape_end_error(open, i));
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
        return Err(unknown_escape_error(src, i));
    }
    if bytes.get(i + 1) != Some(&b'{') {
        return Err(escape_brace_error(i));
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
        return Err(escape_hex_error(src, i - 1, end));
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
    let mut out = String::new();
    let mut i = open + 1;
    loop {
        let Some(&b) = bytes.get(i) else {
            return Err(unterminated_error(open, delim));
        };
        if b == delim {
            return Ok((out, i + 1));
        }
        // A literal does not span lines. Reporting at the opening quote is
        // what makes a missing delimiter legible: without this the scan runs
        // to the end of the file and blames whatever it happens to stop at.
        if b == b'\n' {
            return Err(unterminated_error(open, delim));
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
    let mut toks = Vec::new();
    lex_into(src, &mut toks, |_| true)?;
    Ok(toks)
}

/// The tokens of `src` before the first one `keep` refuses, or before the
/// first that does not lex, then `Eof`. The refused token is the last thing
/// read, so nothing past it is met, an error least of all; `Eof` stands at
/// its start, where an error's `Eof` stands at the error. What a token is
/// never depends on the tokens before it, which is why stopping early reads
/// a prefix of what [`lex`] reads.
pub fn lex_while(src: &str, keep: impl FnMut(&Tok) -> bool) -> Vec<Tok> {
    let mut toks = Vec::new();
    if let Err(stopped) = lex_into(src, &mut toks, keep) {
        let at = stopped.span.start;
        toks.push(Tok { kind: TokKind::Eof, span: Span { start: at, end: at } });
    }
    toks
}

/// [`lex`] by this lexer alone, whatever scanner is installed: the oracle a
/// scanner is held to.
pub fn lex_rust(src: &str) -> Result<Vec<Tok>, LexError> {
    let mut toks = Vec::new();
    lex_into_rust(src, &mut toks, |_| true)?;
    Ok(toks)
}

/// A scanner the lexer can be run by: the longest token of `source` from
/// `at`, after a token whose kind's code is `previous` (zero at the start),
/// as that kind's code and where it ends; or where it refuses, as the
/// reason's code ([`ScanRefusal`]) and the offset it refused at. The kind
/// codes are [`scan_code`]'s, with [`SCAN_SPACE`] and [`SCAN_COMMENT`] for
/// what a lexer drops.
///
/// This is the shape of Heather's own scanner compiled and linked
/// (`heather_linked::scanner::token`, from `lib/lang/lexer/lexer_span.hthr`).
/// This crate does not depend on it: whoever links it hands it over
/// ([`install_scanner`], or [`lex_scanned`] for one call), so the lexer and
/// everything built on it compile the same with and without it
/// (`issues/self-lexer-linked.md`).
pub type Scan = fn(source: &[u8], at: usize, previous: u64) -> Result<(u64, usize), (u64, usize)>;

/// Why a scanner refuses a token, numbered as `lexer_scan.hthr`'s
/// `REFUSED_*` (`crates/linked/tests/scanner.rs` holds the two to each
/// other). Each is one of this lexer's messages, and with where the token
/// starts and where the scanner refused (the byte that took its automaton
/// to `FAIL`, or the source's length where its end did) it is the whole of
/// it: [`ScanRefusal::error`]. The comments say which byte the message is
/// about, from the one refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ScanRefusal {
    /// The character the token starts with begins no token.
    Unexpected = 1,
    /// `!=`.
    BangEq = 2,
    /// The byte refused is no digit of the numeral's radix.
    Digit = 3,
    /// The letter before it began nothing, and is no digit.
    Mark = 4,
    /// The letter two before it, before a sign, began nothing.
    SignedMark = 5,
    /// The byte refused is a `_` before any digit.
    LeadingUnderscore = 6,
    /// The `_` before it has no digit after it.
    Underscore = 7,
    /// A radix prefix has no digit after it.
    NoDigits = 8,
    /// The byte refused continues a finished literal.
    After = 9,
    /// The exponent letter before it continues a finished literal.
    AfterMark = 10,
    /// The exponent letter two before it, before a sign, does.
    AfterSignedMark = 11,
    /// The `_` before it does.
    AfterUnderscore = 12,
    /// A width suffix with a leading zero, whose digits end here.
    LeadingZeros = 13,
    /// The first `_` of the hexadecimal fraction no digit follows continues
    /// the literal before it.
    FractionUnderscore = 14,
    /// The literal's line or the source ends here.
    Unterminated = 15,
    /// A character literal with no scalar value or more than one, closed
    /// here.
    CharCount = 16,
    /// The source ends after an escape's `\`.
    EscapeEnd = 17,
    /// The character refused follows a `\` and begins no escape.
    Escape = 18,
    /// The byte refused follows `\u` and is not `{`.
    EscapeBrace = 19,
    /// The byte refused is in a `\u{…}` and is no hexadecimal digit.
    EscapeHex = 20,
    /// A byte UTF-8 does not allow there, which text never holds.
    NotUtf8 = 21,
}

impl ScanRefusal {
    /// Every reason, in code order: `ALL[r as usize - 1] == r`.
    #[rustfmt::skip]
    pub const ALL: [ScanRefusal; 21] = [
        ScanRefusal::Unexpected, ScanRefusal::BangEq, ScanRefusal::Digit, ScanRefusal::Mark, ScanRefusal::SignedMark,
        ScanRefusal::LeadingUnderscore, ScanRefusal::Underscore, ScanRefusal::NoDigits, ScanRefusal::After,
        ScanRefusal::AfterMark, ScanRefusal::AfterSignedMark, ScanRefusal::AfterUnderscore, ScanRefusal::LeadingZeros,
        ScanRefusal::FractionUnderscore, ScanRefusal::Unterminated, ScanRefusal::CharCount, ScanRefusal::EscapeEnd,
        ScanRefusal::Escape, ScanRefusal::EscapeBrace, ScanRefusal::EscapeHex, ScanRefusal::NotUtf8,
    ];

    /// The reason with this code, if it is one.
    pub fn of_code(code: u64) -> Option<ScanRefusal> {
        let index = usize::try_from(code).ok()?.checked_sub(1)?;
        ScanRefusal::ALL.get(index).copied()
    }

    /// The message this lexer refuses `src` with, where a token that starts
    /// at `start` is refused at `at` for this reason; `None` where the two
    /// offsets cannot be such a refusal's, or for a byte text never holds.
    ///
    /// Nothing is lexed here but values: a literal's value or an escape's
    /// is refused before what follows it is, so where one comes before the
    /// refusal its own refusal is the answer, read from its span as a
    /// token's value is ([`scanned_token`]).
    pub fn error(self, src: &str, start: usize, at: usize) -> Option<LexError> {
        use ScanRefusal::*;
        let bytes = src.as_bytes();
        if start >= bytes.len() || at < start || at > bytes.len() || !src.is_char_boundary(start) {
            return None;
        }
        // The byte `back` before the one refused, inside the token.
        let before = |back: usize| at.checked_sub(back).filter(|&p| p >= start && p < bytes.len());
        let error = match self {
            Unexpected if at == start => unexpected_error(src, start),
            Unexpected => return None,
            BangEq => bang_eq_error(start),
            Digit | Mark | SignedMark => digit_error(src, start, before(self as usize - Digit as usize)?),
            LeadingUnderscore => underscore_error(src, start, before(0)?),
            Underscore => underscore_error(src, start, before(1)?),
            NoDigits if bytes.get(start + 1).is_some_and(|b| b.is_ascii_alphabetic()) => no_digits_error(src, start),
            NoDigits => return None,
            After => return Some(literal_then(src, start, before(0)?)),
            AfterMark | AfterUnderscore => return Some(literal_then(src, start, before(1)?)),
            AfterSignedMark => return Some(literal_then(src, start, before(2)?)),
            LeadingZeros => {
                let letter = start + bytes[start..at].iter().rposition(|b| matches!(b, b'u' | b'i'))?;
                leading_zeros_error(src, start, letter, at)
            }
            FractionUnderscore => {
                let point = start + bytes[start..at].iter().position(|&b| b == b'.')?;
                let at = (point + 1..at).find(|&j| bytes[j] == b'_' && !bytes.get(j + 1).is_some_and(u8::is_ascii_hexdigit))?;
                return Some(literal_then(src, start, at));
            }
            Unterminated | CharCount | EscapeEnd | Escape | EscapeBrace | EscapeHex => return quoted_refusal(self, src, start, at),
            NotUtf8 => return None,
        };
        Some(error)
    }
}

/// A numeral `start..at` and then a byte that continues it: the numeral's
/// own refusal if its value is refused (an exponent out of range), and the
/// byte's otherwise.
fn literal_then(src: &str, start: usize, at: usize) -> LexError {
    match lex_numeral(&src[..at], start) {
        Err(error) => error,
        Ok(_) => after_literal_error(src, start, at),
    }
}

/// A character or string literal opened at `start` and refused at `at`. The
/// escapes before the part refused are read for their values, which may be
/// refused first; a character literal's count of scalar values is theirs.
fn quoted_refusal(reason: ScanRefusal, src: &str, start: usize, at: usize) -> Option<LexError> {
    use ScanRefusal::*;
    let bytes = src.as_bytes();
    let delim = bytes[start];
    if !matches!(delim, b'\'' | b'"') {
        return None;
    }
    // Where the part refused begins: the escape's `\`, or the refusal.
    let refused = match reason {
        EscapeEnd | Escape => at.checked_sub(1)?,
        EscapeBrace => at.checked_sub(2)?,
        EscapeHex => start + bytes[start..at].iter().rposition(|&b| b == b'\\')?,
        _ => at,
    };
    if refused <= start || bytes.get(refused).is_some_and(|&b| b != b'\\') && refused != at {
        return None;
    }
    // The scalar values before it, each escape's read, which may be refused.
    let mut count = 0;
    let mut i = start + 1;
    while i < refused {
        if bytes[i] == b'\\' {
            match lex_escape(src, start, i + 1) {
                Ok((_, next)) => i = next,
                Err(error) => return Some(error),
            }
        } else {
            i += src[i..].chars().next()?.len_utf8();
        }
        count += 1;
    }
    Some(match reason {
        Unterminated => unterminated_error(start, delim),
        CharCount if delim == b'\'' && bytes.get(at) == Some(&b'\'') => char_count_error(src, start, at + 1, count),
        CharCount => return None,
        EscapeEnd => escape_end_error(start, at),
        Escape => unknown_escape_error(src, at),
        EscapeBrace => escape_brace_error(at - 1),
        EscapeHex => escape_hex_error(src, refused, at),
        _ => return None,
    })
}

/// A token's kind as a scanner numbers it: `crates/linked/generated/kinds.rs`,
/// which `scripts/linked` writes from the table `TOKEN_KINDS` of
/// `lib/lang/lexer/lexer_kinds.hthr`, and which `heather_linked::scanner::Kind`
/// is too. A file and not a dependency: this crate does not depend on the
/// linked one ([`Scan`]).
#[macro_use]
pub mod scan_kind {
    include!("../../linked/generated/kinds.rs");
}
pub use scan_kind::Kind as ScanKind;

/// The code [`Scan`] gives whitespace.
pub const SCAN_SPACE: u64 = ScanKind::Space.code();
/// The code [`Scan`] gives a comment.
pub const SCAN_COMMENT: u64 = ScanKind::Comment.code();

static SCANNER: std::sync::OnceLock<Scan> = std::sync::OnceLock::new();

/// From here on [`lex`] and [`lex_while`] cut their source with `scan`, as
/// [`lex_scanned`] does. The first call wins; the `heather` binary makes it
/// once, before anything is read, when `HEATHER_LEXER=linked`.
pub fn install_scanner(scan: Scan) {
    let _ = SCANNER.set(scan);
}

/// Whether a scanner is installed.
pub fn scanner_installed() -> bool {
    SCANNER.get().is_some()
}

static CUT_BY_SCANNER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static LEFT_TO_LEXER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// What the installed scanner has done in this process: how many sources
/// it answered for, tokens or refusal, and how many were this lexer's
/// answer instead. Both zero with no scanner installed.
/// `HEATHER_LEXER_REPORT` prints them when `heather` ends.
pub fn scanner_counts() -> (u64, u64) {
    use std::sync::atomic::Ordering::Relaxed;
    (CUT_BY_SCANNER.load(Relaxed), LEFT_TO_LEXER.load(Relaxed))
}

/// [`lex`] with `scan` deciding where each token starts and ends and which
/// kind it is, and why and where a source is refused. A token's value (an
/// identifier's text, a numeral, a string with its escapes resolved) is
/// read from its span by this lexer, on those bytes alone, and a value it
/// refuses is the source's refusal; a refusal of the scanner's is the
/// message its reason names ([`ScanRefusal::error`]). Where a span does not
/// read as one token of the scanner's kind, or a refusal is none this lexer
/// knows, the whole answer is this lexer's own. The flag says which
/// happened: `true` where the answer was the scanner's.
pub fn lex_scanned(scan: Scan, src: &str) -> (Result<Vec<Tok>, LexError>, bool) {
    let mut toks = Vec::new();
    let (answer, scanned) = lex_into_scanned(scan, src, &mut toks, |_| true);
    (answer.map(|()| toks), scanned)
}

/// [`lex_while`] with `scan`, as [`lex_scanned`] is [`lex`] with it.
pub fn lex_while_scanned(scan: Scan, src: &str, keep: impl FnMut(&Tok) -> bool) -> Vec<Tok> {
    let mut toks = Vec::new();
    if let (Err(stopped), _) = lex_into_scanned(scan, src, &mut toks, keep) {
        let at = stopped.span.start;
        toks.push(Tok { kind: TokKind::Eof, span: Span { start: at, end: at } });
    }
    toks
}

/// The code a scanner gives a token of this kind: its [`ScanKind`]'s.
pub fn scan_code(kind: &TokKind) -> u64 {
    kind.scan_kind().code()
}

// The kinds with a spelling are `TokKind`'s unit variants of the same
// names, both ways: the generated list, so a symbol added to the table is
// mapped here, and the match below stays exhaustive (a `TokKind` with no
// row, or a row with no `TokKind`, does not compile).
macro_rules! spelled_tok_kinds {
    ($($name:ident)*) => {
        impl ScanKind {
            /// The token of a kind the table spells: the unit `TokKind` of
            /// its name. Only [`ScanKind::spelled_at`]'s kinds are asked.
            fn spelled_tok(self) -> TokKind {
                match self {
                    $(ScanKind::$name => TokKind::$name,)*
                    _ => unreachable!("{self:?} has no spelling"),
                }
            }
        }

        impl TokKind {
            /// The kind a scanner cuts this token as. The numbering is the
            /// generated [`ScanKind`]'s, so this names kinds and never
            /// numbers them; that every [`ScanKind`] but the two a lexer
            /// drops is some token's is `crates/linked/tests/scanner.rs`.
            pub fn scan_kind(&self) -> ScanKind {
                match self {
                    TokKind::Ident(_) => ScanKind::Ident,
                    TokKind::Num(_) | TokKind::SuffixedNum(..) => ScanKind::Num,
                    TokKind::Scaled(_) => ScanKind::Scaled,
                    TokKind::Char(_) => ScanKind::Char,
                    TokKind::Str(_) => ScanKind::Str,
                    TokKind::ArgSlot(_) => ScanKind::ArgSlot,
                    TokKind::Hole(_) => ScanKind::Hole,
                    TokKind::Eof => ScanKind::Eof,
                    $(TokKind::$name => ScanKind::$name,)*
                }
            }
        }
    };
}
spelled_kinds!(spelled_tok_kinds);

/// The token the scanner cut at `start..end` with kind `code`, its value
/// read from those bytes alone. `Err(Some(_))` is a value this lexer
/// refuses, its refusal where it stands in the source; `Err(None)` is
/// bytes that are not one token of that kind to this lexer.
fn scanned_token(src: &str, start: usize, end: usize, code: u64) -> Result<TokKind, Option<LexError>> {
    // `>` and `>>` are told apart by what stands before them, which a span
    // alone does not hold, and neither has a value: the scanner's kind
    // stands.
    if code == scan_code(&TokKind::Gt) {
        return Ok(TokKind::Gt);
    }
    if code == scan_code(&TokKind::Shr) {
        return Ok(TokKind::Shr);
    }
    let mut alone = Vec::with_capacity(2);
    if let Err(error) = lex_into_rust(&src[start..end], &mut alone, |_| true) {
        let span = Span { start: error.span.start + start, end: error.span.end + start };
        return Err((span.end <= end).then_some(LexError { msg: error.msg, span }));
    }
    let [tok, _eof] = alone.as_slice() else { return Err(None) };
    let whole = tok.span.start == 0 && tok.span.end == end - start;
    if !(whole && scan_code(&tok.kind) == code) {
        return Err(None);
    }
    Ok(tok.kind.clone())
}

/// [`lex_into`] by a scanner, and whether the answer is the scanner's:
/// where it is not, the answer is [`lex_into_rust`]'s, begun again, with
/// `keep` not asked a second time about the tokens it has kept.
fn lex_into_scanned(scan: Scan, src: &str, toks: &mut Vec<Tok>, mut keep: impl FnMut(&Tok) -> bool) -> (Result<(), LexError>, bool) {
    let bytes = src.as_bytes();
    let base = toks.len();
    let (mut at, mut previous) = (0, 0);
    while at < bytes.len() {
        let start = at;
        let cut = match scan(bytes, start, previous) {
            Ok((code, end)) if end > start && end <= bytes.len() && src.is_char_boundary(end) => {
                if code == SCAN_SPACE || code == SCAN_COMMENT {
                    Ok((code, end, None))
                } else {
                    scanned_token(src, start, end, code).map(|kind| (code, end, Some(kind)))
                }
            }
            Ok(_) => Err(None),
            Err((reason, refused)) => Err(ScanRefusal::of_code(reason).and_then(|reason| reason.error(src, start, refused))),
        };
        let (code, end, kind) = match cut {
            Ok(cut) => cut,
            Err(Some(error)) => return (Err(error), true),
            Err(None) => {
                let kept = toks.len() - base;
                toks.truncate(base);
                let mut seen = 0;
                let answer = lex_into_rust(src, toks, |tok| {
                    if seen < kept {
                        seen += 1;
                        return true;
                    }
                    keep(tok)
                });
                return (answer, false);
            }
        };
        previous = code;
        at = end;
        let Some(kind) = kind else { continue };
        let tok = Tok { kind, span: Span { start, end } };
        if !keep(&tok) {
            // At the refused token's start, as `lex_into_rust` stands.
            toks.push(Tok { kind: TokKind::Eof, span: Span { start, end: start } });
            return (Ok(()), true);
        }
        toks.push(tok);
    }
    toks.push(Tok { kind: TokKind::Eof, span: Span { start: at, end: at } });
    (Ok(()), true)
}

/// [`lex`] into `toks`, stopping before the first token `keep` refuses. `Eof`
/// ends what was read unless an error does. By the installed scanner where
/// there is one ([`install_scanner`]), and by [`lex_into_rust`] otherwise.
fn lex_into(src: &str, toks: &mut Vec<Tok>, keep: impl FnMut(&Tok) -> bool) -> Result<(), LexError> {
    let Some(scan) = SCANNER.get() else { return lex_into_rust(src, toks, keep) };
    let (answer, scanned) = lex_into_scanned(*scan, src, toks, keep);
    let count = if scanned { &CUT_BY_SCANNER } else { &LEFT_TO_LEXER };
    count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    answer
}

/// The lexer itself, in Rust: what [`lex_into`] is with no scanner, what a
/// scanner's cut is held to, and where every message comes from.
fn lex_into_rust(src: &str, toks: &mut Vec<Tok>, mut keep: impl FnMut(&Tok) -> bool) -> Result<(), LexError> {
    let bytes = src.as_bytes();
    let mut i = 0;
    'toks: while i < bytes.len() {
        macro_rules! emit {
            ($tok:expr) => {{
                let tok = $tok;
                if !keep(&tok) {
                    // `Eof` at the refused token's start, whatever its
                    // kind: some kinds are measured before they are made.
                    i = tok.span.start;
                    break 'toks;
                }
                toks.push(tok);
            }};
        }
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
            emit!(Tok {
                kind: TokKind::Ident(text.to_string()),
                span: Span { start, end: i },
            });
            continue;
        }
        // numerals: decimal, or `0x`/`0o`/`0b` radix forms, with `_`
        // separators between digits (docs/archive/radix-numerals-design.md). The
        // token carries only the value: a radix form is a *spelling* of the
        // same numeral, and everything downstream (carrier choice, the
        // emitted kernel term) is decided by the value alone.
        if c.is_ascii_digit() {
            let (n, end) = lex_numeral(src, start)?;
            i = end;
            let kind = match n {
                Lexed::Num(n) => TokKind::Num(n),
                Lexed::Suffixed(n, suffix) => TokKind::SuffixedNum(n, suffix),
                Lexed::Scaled(s) => TokKind::Scaled(s),
            };
            emit!(Tok { kind, span: Span { start, end: i } });
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
                return Err(char_count_error(src, start, end, text.chars().count()));
            };
            emit!(Tok { kind: TokKind::Char(ch), span: Span { start, end } });
            i = end;
            continue;
        }
        if c == b'"' {
            let (text, end) = lex_quoted(src, start, b'"')?;
            emit!(Tok { kind: TokKind::Str(text), span: Span { start, end } });
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
            emit!(Tok { kind: TokKind::Hole(name), span: Span { start, end: i } });
            continue;
        }
        // A fixed token: the longest spelling the source has here of the
        // token kinds' table (`TOKEN_KINDS`, lib/lang/lexer/lexer_kinds.hthr),
        // matched by `ScanKind::spelled_at`, which `scripts/linked` generates
        // from it. A symbol is added there, not here; so are `λ` and `¬`,
        // which are not identifier characters and so reach this. Two pairs are
        // decided before it, and `>>` after it.
        let two = src.get(i..i + 2).unwrap_or("");
        // `!` is Boolean negation, but `!=` is deliberately not an ASCII
        // alias for `≠`: keep diagnosing the pair at the lexer boundary
        // instead of tokenizing it as two unrelated operators.
        if two == "!=" {
            return Err(bang_eq_error(start));
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
            emit!(Tok {
                kind: TokKind::ArgSlot(indexed.then_some(index)),
                span: Span { start, end: i },
            });
            continue;
        }
        let (kind, len) = match ScanKind::spelled_at(&bytes[i..]) {
            // `>>` is a shift only after a space, `(`, `,` or the start of
            // the file; anywhere else it is two closers (see [`TokKind::Shr`]).
            Some((ScanKind::Shr, _)) if !(start == 0 || matches!(bytes[start - 1], b'(' | b',') || bytes[start - 1].is_ascii_whitespace()) => {
                (TokKind::Gt, 1)
            }
            Some((kind, len)) => (kind.spelled_tok(), len),
            None => return Err(unexpected_error(src, start)),
        };
        emit!(Tok { kind, span: Span { start, end: start + len } });
        i += len;
    }
    toks.push(Tok { kind: TokKind::Eof, span: Span { start: i, end: i } });
    Ok(())
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
    fn exclusive_or_and_complement_lex() {
        use TokKind::*;
        assert_eq!(kinds("a ⊕ ~b"), [Ident("a".into()), OPlus, Tilde, Ident("b".into()), Eof]);
        assert_eq!(kinds("~~x"), [Tilde, Tilde, Ident("x".into()), Eof]);
    }

    fn suffixed(src: &str) -> (u64, String) {
        let toks = lex(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
        assert_eq!(toks.len(), 2, "{src}: one literal then Eof, got {toks:?}");
        let TokKind::SuffixedNum(n, suffix) = &toks[0].kind else { panic!("{src}: not a suffixed numeral: {:?}", toks[0]) };
        assert_eq!(toks[0].span, Span { start: 0, end: src.len() });
        (n.as_u64().expect("fits in 64 bits"), suffix.clone())
    }

    #[test]
    fn a_width_suffix_is_part_of_its_numeral() {
        assert_eq!(suffixed("42u64"), (42, "u64".into()));
        assert_eq!(suffixed("0x80u8"), (0x80, "u8".into()));
        assert_eq!(suffixed("7i32"), (7, "i32".into()));
        assert_eq!(suffixed("1_000u16"), (1000, "u16".into()));
        assert_eq!(suffixed("0b101u3"), (5, "u3".into()));
        assert_eq!(suffixed("0o17u27"), (15, "u27".into()));
        assert_eq!(suffixed("0u0"), (0, "u0".into()));
        // `f` is a hexadecimal digit and `i` is not: the numeral ends there.
        assert_eq!(suffixed("0x1fi8"), (0x1f, "i8".into()));
        assert_eq!(suffixed("0xFFFF_FFFFu32"), (0xFFFF_FFFF, "u32".into()));
        // A method call after a suffixed literal is a method call on it.
        assert!(matches!(kinds("1u8.add")[..], [TokKind::SuffixedNum(..), TokKind::Dot, TokKind::Ident(_), TokKind::Eof]));
        // Without a width the letters are still not part of a numeral.
        assert!(refused("42u").contains("invalid digit `u`"));
        assert!(refused("7in").contains("invalid digit `i`"));
        assert!(refused("1_u8").contains("invalid digit `u`"));
        assert!(refused("42u64x").contains("invalid character `x` after the literal `42u64`"));
        assert!(refused("42u64_").contains("after the literal"));
        assert!(refused("42u08").contains("without leading zeros"));
        // A point or an exponent is no whole number, so no suffix follows it.
        assert!(refused("1.5u8").contains("after the literal"));
        assert!(refused("1e3u8").contains("after the literal"));
        assert!(refused("0xu8").contains("needs at least one hexadecimal digit") || refused("0xu8").contains("invalid digit"));
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
