//! Whitespace normalization over the token stream (issues/heather-formatter.md).
//!
//! This is deliberately **not** a pretty-printer. It re-emits the file's own
//! tokens with canonical spacing and never moves a line break, which buys three
//! things a printer would have to earn: the safety check is total
//! (`lex(format(src))` must equal `lex(src)` kind-for-kind, which rules out
//! every adjacency hazard — `?p` vs `? p`, joined qualified names, `·₂`, `$x` —
//! without enumerating them); comments cost nothing, because the gap between
//! two token spans *is* the trivia and a `//` comment always runs to end of
//! line, so any gap holding one also holds a newline and is left alone; and a
//! whole-library reformat stays reviewable, being empty under `git diff -w`.
//!
//! It runs on source that does not elaborate, and degrades rather than refuses:
//! a file that does not lex is returned unchanged, and one that does not parse
//! is normalized except for the spacing that needs [`crate::roles`].

use crate::lexer::{lex, Tok, TokKind};
use crate::parse_file;
use crate::roles::{token_roles, TokenRole};
use std::collections::HashMap;

/// What the gap between two adjacent tokens should become.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gap {
    /// No space at all.
    Tight,
    /// At least one space: inserted if absent, left as written if present.
    Space,
    /// Exactly what the author wrote.
    ///
    /// The conservative default, and most of the table. Deciding *presence*
    /// everywhere would churn the whole library over questions it has no
    /// settled answer to — `{P: A → Type}` is written tight and
    /// `{ fst: A, snd: B }` spaced, 117 against 666.
    Keep,
}

/// Normalize the whitespace of one Heather source file.
pub fn format_source(src: &str) -> String {
    let Ok(toks) = lex(src) else {
        // Not lexable: there are no tokens to lay out, and guessing at the
        // byte level is exactly the kind of edit this module exists to avoid.
        return src.to_string();
    };
    let roles = token_role_map(src, &toks);
    let mut out = String::with_capacity(src.len());

    // Leading trivia: keep it, minus trailing blanks on each line.
    let first = toks.first().map(|t| t.span.start).unwrap_or(src.len());
    out.push_str(&clean_multiline(&src[..first]));

    for (i, tok) in toks.iter().enumerate() {
        if matches!(tok.kind, TokKind::Eof) {
            break;
        }
        out.push_str(&src[tok.span.start..tok.span.end]);
        let Some(next) = toks[i + 1..].iter().find(|t| !matches!(t.kind, TokKind::Eof)) else {
            break;
        };
        let raw = &src[tok.span.end..next.span.start];
        if raw.contains('\n') {
            // A line break is never moved, and a comment always brings one, so
            // this branch is also what keeps comments and indentation intact.
            out.push_str(&clean_multiline(raw));
        } else {
            // The formatter decides *whether* there is a space, never how
            // many. A run of them is the author lining a column up — 27 of
            // them across four library files, `tm_lam(dom, b)            =>`
            // and the like — and re-deciding that is not formatting.
            out.push_str(match gap_between(tok, next, roles.as_ref()) {
                Gap::Tight => "",
                Gap::Space if raw.is_empty() => " ",
                Gap::Space | Gap::Keep => raw,
            });
        }
    }

    // Trailing trivia, then exactly one final newline.
    if let Some(last) = toks.iter().rev().find(|t| !matches!(t.kind, TokKind::Eof)) {
        out.push_str(&clean_multiline(&src[last.span.end..]));
    }
    while out.ends_with('\n') || out.ends_with(' ') || out.ends_with('\t') {
        out.pop();
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// Strip trailing blanks from each line and allow at most one blank line.
///
/// The segment after the last newline is **not** a line to strip: it is the
/// indentation of the token that follows, and is kept verbatim. Everything
/// else about the author's line structure — where the breaks are, what the
/// comments say, how deep each line is indented — is passed through.
fn clean_multiline(trivia: &str) -> String {
    let segs: Vec<&str> = trivia.split('\n').collect();
    let mut out = String::with_capacity(trivia.len());
    // Segment 0 is the tail of the line the previous token sat on.
    out.push_str(segs[0].trim_end_matches([' ', '\t']));
    let mut blank_run = 0usize;
    for (i, seg) in segs.iter().enumerate().skip(1) {
        let is_indent = i == segs.len() - 1;
        let body = if is_indent { *seg } else { seg.trim_end_matches([' ', '\t']) };
        if !is_indent && body.is_empty() {
            blank_run += 1;
            if blank_run > 1 {
                continue;
            }
        } else {
            blank_run = 0;
        }
        out.push('\n');
        out.push_str(body);
    }
    out
}

/// The roles no [`TokKind`] determines, or `None` when the file does not parse —
/// every `<` and `-` then falls to [`Gap::Keep`] rather than being guessed at,
/// so an unparseable file is still formatted everywhere else.
fn token_role_map(src: &str, toks: &[Tok]) -> Option<HashMap<usize, TokenRole>> {
    let file = parse_file(src).ok()?;
    Some(token_roles(toks, &file))
}

/// Is this token an infix operator, and so spaced on both sides?
///
/// A classification of the lexer's own vocabulary, not a second table of
/// operator spellings: `<` and `-` are the kinds that need outside help, and
/// they get it from [`crate::roles`].
fn is_infix(tok: &Tok, roles: &HashMap<usize, TokenRole>) -> bool {
    match tok.kind {
        TokKind::Plus
        | TokKind::PlusPlus
        | TokKind::Star
        | TokKind::Caret
        | TokKind::LtEq
        | TokKind::Arrow
        | TokKind::FatArrow
        | TokKind::Eq
        | TokKind::Ne
        | TokKind::EqEq
        | TokKind::ColonEq
        | TokKind::Turnstile
        | TokKind::AmpAmp
        | TokKind::PipePipe
        | TokKind::Bullet
        | TokKind::Approx
        | TokKind::Join
        | TokKind::Meet
        | TokKind::Wedge
        | TokKind::Vee
        | TokKind::Iff
        // `let x <- e;`, and `(<- e)`, where the `(` keeps it tight on the left.
        | TokKind::LArrow => true,
        // Comparison `<`; an argument-list `<` is a delimiter instead. When the
        // file did not parse, `delims` is empty and every `<` reads as infix —
        // so `Lt` is excluded there too, by `role_known`.
        TokKind::Lt => !matches!(roles.get(&tok.span.start), Some(TokenRole::ArgumentDelimiter)),
        // Subtraction; every other `-` is a prefix negation or a declared name.
        TokKind::Minus => matches!(roles.get(&tok.span.start), Some(TokenRole::InfixMinus)),
        _ => false,
    }
}

fn gap_between(a: &Tok, b: &Tok, roles: Option<&HashMap<usize, TokenRole>>) -> Gap {
    use TokKind::*;

    let parsed = roles.is_some();
    let empty = HashMap::new();
    let roles = roles.unwrap_or(&empty);
    // Nothing may be decided about `<`/`>` spacing without a parse.
    let role_known = |t: &Tok| !matches!(t.kind, Lt | Gt) || parsed;
    let declared = |t: &Tok| matches!(roles.get(&t.span.start), Some(TokenRole::OperatorName));

    // Punctuation hugs what precedes it and is followed by one space.
    if matches!(b.kind, Comma | Semi | Colon | ColonColon) {
        return Gap::Tight;
    }
    if matches!(a.kind, Comma | Semi | Colon) {
        return Gap::Space;
    }
    if matches!(a.kind, ColonColon) {
        return Gap::Tight;
    }

    // Projection binds tighter than anything around it.
    if matches!(a.kind, Dot) || matches!(b.kind, Dot) {
        return Gap::Tight;
    }

    // Delimiters do not pad on the inside.
    if matches!(a.kind, LParen | LBracket | LAngle | LSemantic)
        || matches!(b.kind, RParen | RBracket | RAngle | RSemantic)
    {
        return Gap::Tight;
    }
    if matches!(a.kind, Lt)
        && matches!(roles.get(&a.span.start), Some(TokenRole::ArgumentDelimiter))
    {
        return Gap::Tight;
    }
    if matches!(b.kind, Gt) && role_known(b) {
        return Gap::Tight;
    }

    // Prefix operators are written tight — but only where they *are* prefix
    // operators. The `-` of `designation prefix - at Int := neg` is a symbol
    // being declared, with no operand to hug, and `-at` is not an improvement.
    // Nothing mechanical catches that: both spellings lex identically.
    //
    // `λ` is not on this list — the library writes `λ source begin =>` in every
    // occurrence — and a bare `?` must keep its gap, because `? p` and `?p` are
    // different programs.
    //
    // A `-` is the one of these with an infix reading too, and only the parse
    // tells `a - b` from `-b`: without one it keeps its gap either way.
    let infix_minus = |t: &Tok| matches!(roles.get(&t.span.start), Some(TokenRole::InfixMinus));
    if matches!(a.kind, Minus) && (!parsed || infix_minus(a)) {
        return if infix_minus(a) { Gap::Space } else { Gap::Keep };
    }
    if matches!(a.kind, Neg | Minus | Bang | Dollar | UpArrow) && !declared(a) {
        return Gap::Tight;
    }
    // The postfix `⁻¹` hugs its operand, on the same terms.
    if matches!(b.kind, SupInverse) && !declared(b) {
        return Gap::Tight;
    }

    if !role_known(a) || !role_known(b) {
        return Gap::Keep;
    }
    if (is_infix(a, roles) && !declared(a)) || (is_infix(b, roles) && !declared(b)) {
        return Gap::Space;
    }
    Gap::Keep
}
