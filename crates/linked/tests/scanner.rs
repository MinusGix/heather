//! The linked scanner against the Rust lexer.
//!
//! `heather_syntax::lex` is the oracle: on every Heather source in the
//! repository, on every line of the library with one character changed, and
//! on strings put together from the pieces tokens are made of, the scanner
//! (`heather_linked::scanner`, compiled from
//! `lib/lang/lexer/lexer_scan.hthr`) gives the lexer's kinds and spans where
//! the lexer gives tokens, and refuses where it refuses.
//!
//! The one seam is values. The lexer's tokens hold them and it refuses
//! three that do not fit (an exponent, a `\u{…}` escape, an argument-slot
//! index); the scanner returns spans. [`lex_linked`] closes it the way the
//! roadmap says the linked lexer will at first
//! (`docs/native-lexer-crypto-roadmap.md` §3): the scanner cuts the source,
//! and each token's value is read from its span alone. That function is a
//! whole lexer, and it is compared with the oracle token for token, values
//! included.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::path::{Path, PathBuf};

use heather_linked::scanner::{self, DEAD, END, FAIL, Kind, Refused, Scanner, Token, failed};
use heather_syntax::lexer::{
    SCAN_COMMENT, SCAN_SPACE, Scan, ScanRefusal, Tok, TokKind, lex, lex_rust, lex_scanned, lex_while, lex_while_scanned, scan_code, scanner_counts,
    scanner_installed,
};

/// The scanner's kind for a lexer token: the lexer's own `scan_code`, whose
/// numbering is the generated `kinds.rs` this crate's [`Kind`] also is.
fn kind_of(kind: &TokKind) -> Kind {
    Kind::of_code(scan_code(kind)).unwrap_or_else(|| panic!("{kind:?} has no scanner kind"))
}

/// The scanner's tokens up to the end or its refusal, and the refusal.
fn scan(source: &str) -> (Vec<Token>, Option<Refused>) {
    let mut tokens = Vec::new();
    for token in Scanner::new(source.as_bytes()) {
        match token {
            Ok(token) => tokens.push(token),
            Err(refused) => return (tokens, Some(refused)),
        }
    }
    (tokens, None)
}

/// The lexer's message for the scanner's refusal of a source.
fn refusal_error(source: &str, refused: Refused) -> Option<heather_syntax::lexer::LexError> {
    ScanRefusal::of_code(refused.reason)?.error(source, refused.start, refused.at)
}

/// A token's value, read from its span alone: the lexer on those bytes and
/// nothing around them. `None` is one of the refusals about a value, and
/// only those: a span the lexer refuses for its shape is a token the scanner
/// should not have cut, and that is a failure here, not a refusal.
fn value(source: &str, token: Token) -> Option<TokKind> {
    if token.kind == Kind::Eof {
        return Some(TokKind::Eof);
    }
    let alone = match lex(&source[token.start..token.end]) {
        Ok(alone) => alone,
        Err(error) => {
            let about_a_value = ["is out of range", "is a surrogate, not a Unicode scalar value", "is above the last Unicode scalar value"]
                .iter()
                .any(|what| error.msg.contains(what));
            assert!(about_a_value, "the scanner cut {token:?} from {source:?}, which the lexer refuses: {}", error.msg);
            return None;
        }
    };
    let [tok, eof] = alone.as_slice() else { panic!("{token:?} of {source:?} is not one token alone: {alone:?}") };
    assert!(matches!(eof.kind, TokKind::Eof));
    // `>>` is a shift by what stands before it, which a span alone does not
    // hold, and it has no value to read: the scanner's kind stands.
    if token.kind == Kind::Gt || token.kind == Kind::Shr {
        return Some(if token.kind == Kind::Gt { TokKind::Gt } else { TokKind::Shr });
    }
    assert_eq!(kind_of(&tok.kind), token.kind, "{token:?} of {source:?} alone");
    Some(tok.kind.clone())
}

/// The linked lexer: the scanner's cut of the source, with each token's
/// value read from its span. `None` where it refuses.
fn lex_linked(source: &str) -> Option<Vec<(TokKind, usize, usize)>> {
    let (tokens, refused) = scan(source);
    if refused.is_some() {
        return None;
    }
    tokens.into_iter().map(|token| Some((value(source, token)?, token.start, token.end))).collect()
}

fn plain(tokens: &[Tok]) -> Vec<(TokKind, usize, usize)> {
    tokens.iter().map(|tok| (tok.kind.clone(), tok.span.start, tok.span.end)).collect()
}

/// The two lexers on one source: the same tokens, or both refusing, with
/// the same message at the same place: the scanner's refusal's, or where a
/// value before it was refused first, that value's.
fn agree(source: &str) -> Result<(), String> {
    let theirs = lex(source);
    let ours = lex_linked(source);
    match (&theirs, &ours) {
        (Ok(theirs), Some(ours)) => {
            let theirs = plain(theirs);
            if &theirs == ours {
                return Ok(());
            }
            let at = theirs.iter().zip(ours).position(|(a, b)| a != b).unwrap_or(theirs.len().min(ours.len()));
            Err(format!("token {at}: the lexer has {:?}, the scanner {:?}", theirs.get(at), ours.get(at)))
        }
        (Err(_), None) => {
            let error = theirs.as_ref().unwrap_err();
            let (tokens, refused) = scan(source);
            if tokens.iter().any(|token| value(source, *token).is_none()) {
                return Ok(());
            }
            let refused = refused.expect("a refusal");
            match refusal_error(source, refused) {
                Some(ours) if (&ours.msg, ours.span.start, ours.span.end) == (&error.msg, error.span.start, error.span.end) => Ok(()),
                ours => Err(format!("the lexer refuses with {error:?}, the scanner with {refused:?}, which says {ours:?}")),
            }
        }
        (Ok(_), None) => Err(format!("the lexer accepts what the scanner refuses at {:?}", scan(source).1)),
        (Err(error), Some(_)) => Err(format!("the scanner accepts what the lexer refuses: {}", error.msg)),
    }
}

fn assert_agree(source: &str, what: &str) {
    if let Err(why) = agree(source) {
        panic!("{what}: {why}\n  source: {source:?}");
    }
}

fn kinds(source: &str) -> Vec<Kind> {
    let (tokens, refused) = scan(source);
    assert_eq!(refused, None, "{source:?} is refused");
    tokens.into_iter().map(|token| token.kind).collect()
}

fn spans(source: &str) -> Vec<(Kind, usize, usize)> {
    let (tokens, refused) = scan(source);
    assert_eq!(refused, None, "{source:?} is refused");
    tokens.into_iter().map(|token| (token.kind, token.start, token.end)).collect()
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("the repository")
}

fn sources_under(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries {
        let path = entry.expect("entry").path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "target") {
                continue;
            }
            sources_under(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "hthr") {
            out.push(path);
        }
    }
}

/// Every Heather source in the repository: the library, the examples, and
/// the fixtures under `crates/`.
fn corpus() -> Vec<(PathBuf, String)> {
    let root = root();
    let mut paths = Vec::new();
    for dir in ["lib", "examples", "crates"] {
        sources_under(&root.join(dir), &mut paths);
    }
    paths.sort();
    assert!(paths.len() > 300, "only {} sources found under {}", paths.len(), root.display());
    paths
        .into_iter()
        .filter_map(|path| {
            // A fixture that is not UTF-8 is not a `&str` the lexer takes.
            let text = String::from_utf8(std::fs::read(&path).expect("read")).ok()?;
            Some((path, text))
        })
        .collect()
}

/// The LCG of `tests/sha512.rs`.
struct Lcg(u64);

impl Lcg {
    fn word(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 32)
    }

    fn below(&mut self, n: usize) -> usize {
        ((self.word() >> 16) % n as u64) as usize
    }

    fn pick<'a>(&mut self, from: &[&'a str]) -> &'a str {
        from[self.below(from.len())]
    }
}

// ---------------------------------------------------------------------------
// The automaton's contract with the loop around it.

// `Kind` is generated from `TOKEN_KINDS` (`lib/lang/lexer/lexer_kinds.hthr`),
// which `heather_cli::linked::token_kinds` holds to the module's `KIND_*`
// constants; this holds `of_code` to `ALL`, and the automaton's other
// constants to the module.
#[test]
fn the_kinds_are_the_modules() {
    for (index, kind) in Kind::ALL.iter().enumerate() {
        assert_eq!(kind.code(), index as u64 + 1);
        assert_eq!(Kind::of_code(kind.code()), Some(*kind));
    }
    assert_eq!(Kind::of_code(0), None);
    assert_eq!(Kind::of_code(Kind::ALL.len() as u64 + 1), None);
    let module = include_str!("../../../lib/lang/lexer/lexer_scan.hthr");
    let constant = |name: &str| -> u64 {
        let line = module.lines().find(|line| line.starts_with(&format!("def {name}: u64 = "))).expect(name);
        let value = line.split_once(" = ").expect("a definition").1.trim_end_matches(';');
        match value.strip_prefix("0x") {
            Some(hex) => u64::from_str_radix(hex, 16).expect("hexadecimal"),
            None => value.parse().expect("decimal"),
        }
    };
    assert_eq!(constant("DEAD"), DEAD);
    assert_eq!(constant("FAIL"), FAIL);
    assert_eq!(constant("END"), END);
}

// The table's spellings are what both lexers cut: each, alone, is one
// token of its kind that runs to its end, to the Rust lexer and to the
// linked scanner. (The module proves the second of the evaluated scanner,
// `token_kinds_spelled_*`; this is the compiled one, and the Rust lexer the
// table is no theorem about.) The `>>` row holds at the start of a source,
// where it is a shift.
#[test]
fn the_spellings_are_both_lexers() {
    let mut spelled = 0;
    for kind in Kind::ALL {
        for spelling in kind.spellings() {
            let toks = lex(spelling).unwrap_or_else(|error| panic!("{spelling:?} of {kind:?} does not lex: {}", error.msg));
            let [tok, eof] = toks.as_slice() else { panic!("{spelling:?} of {kind:?} is not one token: {toks:?}") };
            assert!(matches!(eof.kind, TokKind::Eof));
            assert_eq!((kind_of(&tok.kind), tok.span.start, tok.span.end), (kind, 0, spelling.len()), "{spelling:?} to the Rust lexer");
            assert_eq!(scan(spelling), (vec![Token { kind, start: 0, end: spelling.len() }, Token { kind: Kind::Eof, start: spelling.len(), end: spelling.len() }], None),
                "{spelling:?} to the linked scanner");
            spelled += 1;
        }
    }
    // A control: a spelling the table does not have is not a token.
    assert!(lex("!=").is_err());
    assert!(spelled > 60, "{spelled}");
}

/// Every state the automaton can be in: the two starts and what stepping
/// reaches from them.
fn reachable() -> Vec<u64> {
    let mut states = vec![scanner::begin(0), scanner::begin(Kind::Ident.code())];
    let mut next = 0;
    while next < states.len() {
        for byte in 0..=END {
            let to = scanner::step(states[next], byte);
            if !states.contains(&to) {
                states.push(to);
            }
        }
        next += 1;
    }
    states
}

#[test]
fn every_state_stops_at_the_end() {
    // The loop feeds `END` once and then stops, so no state may ask for
    // more: at the end a state stops (its last accept is the token) or
    // refuses. The same holds for every word that is not a byte.
    let states = reachable();
    assert!(states.len() > 70, "{} states", states.len());
    for state in &states {
        for byte in [END, END + 1, 1 << 8 | 0x61, 1 << 32, u64::MAX] {
            let to = scanner::step(*state, byte);
            assert!(to == DEAD || failed(to), "state {state:#x} goes to {to:#x} on {byte:#x}");
        }
    }
}

#[test]
fn a_state_accepts_a_kind_or_nothing() {
    for state in reachable() {
        let code = scanner::accept(state);
        if failed(state) {
            // A state that refuses holds its reason where a kind would be.
            assert!(ScanRefusal::of_code(code).is_some_and(|reason| reason != ScanRefusal::Unexpected), "state {state:#x} refuses for {code}");
            continue;
        }
        assert!(code == 0 || Kind::of_code(code).is_some_and(|kind| kind != Kind::Eof), "state {state:#x} accepts {code}");
    }
    assert_eq!(scanner::accept(DEAD), 0);
    assert_eq!(scanner::accept(FAIL), 0);
    // The two stops stay where they are, a finished token has no way on, and
    // neither has a word that is no state: a number no family holds, or a
    // state's number under the wrong kind.
    let ident = state_after(scanner::begin(0), "a").expect("a state");
    let paren = scanner::step(scanner::begin(0), u64::from(b'('));
    assert_eq!(Kind::of_code(scanner::accept(ident)), Some(Kind::Ident));
    assert_eq!(Kind::of_code(scanner::accept(paren)), Some(Kind::LParen));
    for byte in [0x61, 0x3e, 0x5f, 0x30, 0x28, 0xe2, END] {
        assert_eq!(scanner::step(DEAD, byte), DEAD);
        assert_eq!(scanner::step(FAIL, byte), FAIL);
        assert_eq!(scanner::step(FAIL | 3 << 8, byte), FAIL | 3 << 8);
        assert_eq!(scanner::step(paren, byte), DEAD);
        assert_eq!(scanner::step(0xff, byte), DEAD);
        assert_eq!(scanner::step(u64::MAX, byte), DEAD);
        assert_eq!(scanner::step(ident & 0xff, byte), DEAD);
        assert_eq!(scanner::step(ident | 1 << 40, byte), DEAD);
    }
}

#[test]
fn the_automaton_is_one_export() {
    // `scan_step` is linked as one program, so the manifest names it and
    // none of the functions inside it: a family exported again beside the
    // program would be a second copy nothing calls.
    let manifest = include_str!("../generated/EXPORTS.tsv");
    for export in ["scan_step", "scan_accept", "scan_begin"] {
        assert!(manifest.contains(&format!("lib/lang/lexer/lexer_scan.hthr\t{export}\t")), "{export} is not in EXPORTS.tsv");
    }
    assert!(!manifest.contains("\tstep_"), "a family is exported apart from the program");
    // And every family the module writes is one `scan_choose` calls, once:
    // a family nothing chooses would be states nothing reaches.
    let module = include_str!("../../../lib/lang/lexer/lexer_scan.hthr");
    let from = module.find("runtime fn scan_choose(").expect("scan_choose");
    let choose = &module[from..from + module[from..].find("\n}\n").expect("its end")];
    let families: Vec<&str> = module
        .lines()
        .filter_map(|line| line.strip_prefix("runtime fn step_"))
        .map(|rest| &rest[..rest.find('(').expect("parameters")])
        .collect();
    assert_eq!(families.len(), 24);
    for family in families {
        assert_eq!(choose.matches(&format!("step_{family}(s, b)")).count(), 1, "step_{family} in scan_choose");
    }
}

#[test]
fn a_shift_may_begin_only_after_a_gap() {
    let shift = scanner::begin(0);
    let plain = scanner::begin(Kind::Ident.code());
    assert_ne!(shift, plain);
    for kind in Kind::ALL {
        let expected = if matches!(kind, Kind::Space | Kind::LParen | Kind::Comma) { shift } else { plain };
        assert_eq!(scanner::begin(kind.code()), expected, "{kind:?}");
    }
}

// ---------------------------------------------------------------------------
// Tokens, by hand: what the lexer's own documentation promises, stated here
// without the lexer.

#[test]
fn the_tokens_of_a_declaration() {
    use Kind::*;
    assert_eq!(
        spans("fn f(x: Nat) → Nat { x }"),
        [
            (Ident, 0, 2),
            (Ident, 3, 4),
            (LParen, 4, 5),
            (Ident, 5, 6),
            (Colon, 6, 7),
            (Ident, 8, 11),
            (RParen, 11, 12),
            (Arrow, 13, 16),
            (Ident, 17, 20),
            (LBrace, 21, 22),
            (Ident, 23, 24),
            (RBrace, 25, 26),
            (Eof, 26, 26),
        ]
    );
    assert_eq!(spans(""), [(Eof, 0, 0)]);
    assert_eq!(spans("  // only a comment"), [(Eof, 19, 19)]);
    assert_eq!(spans("a // b\nc"), [(Ident, 0, 1), (Ident, 7, 8), (Eof, 8, 8)]);
}

#[test]
fn the_longest_token_wins_and_a_dead_end_falls_back() {
    use Kind::*;
    // A qualified name is one identifier; `::` before anything else is not
    // part of it, and neither is a single `:`.
    assert_eq!(kinds("nat::Nat::sub"), [Ident, Eof]);
    assert_eq!(kinds("nat::{Le}"), [Ident, ColonColon, LBrace, Ident, RBrace, Eof]);
    assert_eq!(kinds("x:=1"), [Ident, ColonEq, Num, Eof]);
    assert_eq!(kinds("x:::y"), [Ident, ColonColon, Colon, Ident, Eof]);
    assert_eq!(spans("a::1"), [(Ident, 0, 1), (ColonColon, 1, 3), (Num, 3, 4), (Eof, 4, 4)]);
    // A point is a fraction only before a digit, and a hexadecimal one only
    // when an exponent follows: the scan runs to the end of `.fff` before
    // it knows, and comes back.
    assert_eq!(kinds("1.5"), [Scaled, Eof]);
    assert_eq!(kinds("1.method()"), [Num, Dot, Ident, LParen, RParen, Eof]);
    assert_eq!(kinds("1..2"), [Num, Dot, Dot, Num, Eof]);
    assert_eq!(kinds("0x1.8p3"), [Scaled, Eof]);
    assert_eq!(spans("0xff.fff()"), [(Num, 0, 4), (Dot, 4, 5), (Ident, 5, 8), (LParen, 8, 9), (RParen, 9, 10), (Eof, 10, 10)]);
    assert_eq!(kinds("0xff.f_p"), [Num, Dot, Ident, Eof]);
    assert_eq!(kinds("1e5 1e-5 1_e5 0x1p3 0x1_p+3"), [Scaled, Scaled, Scaled, Scaled, Scaled, Eof]);
    // A width suffix is part of its numeral, in every radix, and `u`/`i`
    // are never hexadecimal digits.
    assert_eq!(spans("42u64 0x1fi8"), [(Num, 0, 5), (Num, 6, 12), (Eof, 12, 12)]);
    assert_eq!(kinds("0u8 0b1u1 0o7i27 1_0u16 0u0"), [Num, Num, Num, Num, Num, Eof]);
    assert_eq!(spans("1u8.f"), [(Num, 0, 3), (Dot, 3, 4), (Ident, 4, 5), (Eof, 5, 5)]);
    // Operators.
    assert_eq!(kinds("<-> <- <= << < -> - ++ + => == = |- || | && & := :: :"), [
        Iff, LArrow, LtEq, Shl, Lt, Arrow, Minus, PlusPlus, Plus, FatArrow, EqEq, Eq, Turnstile, PipePipe, Pipe,
        AmpAmp, Amp, ColonEq, ColonColon, Colon, Eof
    ]);
    assert_eq!(kinds("<-->"), [LArrow, Arrow, Eof]);
    assert_eq!(kinds("?p ? p ?"), [Hole, Hole, Ident, Hole, Eof]);
    assert_eq!(spans("?p::q"), [(Hole, 0, 2), (ColonColon, 2, 4), (Ident, 4, 5), (Eof, 5, 5)]);
}

#[test]
fn a_shift_needs_a_gap_before_it() {
    use Kind::*;
    assert_eq!(kinds("a >> b"), [Ident, Shr, Ident, Eof]);
    assert_eq!(kinds("a>>b"), [Ident, Gt, Gt, Ident, Eof]);
    assert_eq!(kinds("List<List<A>>"), [Ident, Lt, Ident, Lt, Ident, Gt, Gt, Eof]);
    assert_eq!(kinds(">> (>> ,>> \n>>"), [Shr, LParen, Shr, Comma, Shr, Shr, Eof]);
    assert_eq!(kinds(")>> ]>> =>>"), [RParen, Gt, Gt, RBracket, Gt, Gt, FatArrow, Gt, Eof]);
    assert_eq!(kinds("a >>> b"), [Ident, Shr, Gt, Ident, Eof]);
}

#[test]
fn the_symbols_past_ascii() {
    use Kind::*;
    assert_eq!(kinds("λ ¬ ∙ ≈ ⊔ ⊓ ⊕ ∧ ∨ ↔ ← ∃ ∑ ∏ ↑ ∀ ≠ ⊢ → ∥ ⟨ ⟩ ⟦ ⟧ ~"), [
        Lambda, Neg, Bullet, Approx, Join, Meet, OPlus, Wedge, Vee, Iff, LArrow, Exists, BigSum, BigProd, UpArrow,
        Forall, Ne, Turnstile, Arrow, NormBar, LAngle, RAngle, LSemantic, RSemantic, Tilde, Eof
    ]);
    assert_eq!(spans("x⁻¹"), [(Ident, 0, 1), (SupInverse, 1, 6), (Eof, 6, 6)]);
    // An argument slot takes the subscript digits right behind it and
    // nothing else: an ordinary digit, or another symbol that begins with
    // the digits' first byte, is the next token.
    assert_eq!(spans("·"), [(ArgSlot, 0, 2), (Eof, 2, 2)]);
    assert_eq!(spans("·₁₂"), [(ArgSlot, 0, 8), (Eof, 8, 8)]);
    assert_eq!(spans("·12"), [(ArgSlot, 0, 2), (Num, 2, 4), (Eof, 4, 4)]);
    assert_eq!(spans("·₁→"), [(ArgSlot, 0, 5), (Arrow, 5, 8), (Eof, 8, 8)]);
    assert_eq!(spans("·→"), [(ArgSlot, 0, 2), (Arrow, 2, 5), (Eof, 5, 5)]);
}

#[test]
fn literals_end_at_their_quote() {
    use Kind::*;
    assert_eq!(spans(r#""a\"b" 'c' '\'' '\u{1F600}' "é\\""#), [
        (Str, 0, 6),
        (Char, 7, 10),
        (Char, 11, 15),
        (Char, 16, 27),
        (Str, 28, 34),
        (Eof, 34, 34)
    ]);
    assert_eq!(kinds("'é' '→' '😀' \"// not a comment\""), [Char, Char, Char, Str, Eof]);
    assert_eq!(kinds("f('x',\"y\")"), [Ident, LParen, Char, Comma, Str, RParen, Eof]);
}

#[test]
fn what_is_refused_and_where() {
    // (source, offset of the token the scanner refuses)
    let refused: &[(&str, usize)] = &[
        // No token begins so.
        ("a # b", 2),
        ("x δ", 2),
        ("a ⁻ b", 2),
        ("a ` b", 2),
        ("\u{b}", 0),
        // `!=` is not a spelling of `≠`.
        ("a != b", 2),
        // Numerals: a letter glued on, a misplaced `_`, a prefix with no
        // digit, an exponent that is not one.
        ("12abc", 0),
        ("x 1_", 2),
        ("1__0", 0),
        ("0x", 0),
        ("0x_1", 0),
        ("0xfg", 0),
        ("0b12", 0),
        ("0o78", 0),
        ("0X1", 0),
        ("1e", 0),
        ("1e+", 0),
        ("1.5e", 0),
        ("1.5e+", 0),
        ("x 0o", 2),
        ("1.5_", 0),
        ("1.5x", 0),
        ("1e5x", 0),
        ("1e5_", 0),
        // A width suffix: a letter with no width, a leading zero, a name
        // glued on, a separator before it, and after a point.
        ("42u", 0),
        ("x 7in", 2),
        ("42u08", 0),
        ("42u64x", 0),
        ("42u64_", 0),
        ("1_u8", 0),
        ("0x1_u8", 0),
        ("1.5u8", 0),
        ("0bu8", 0),
        ("0x1p", 0),
        ("0x1.8_p3", 0),
        ("0x1.8__1p3", 0),
        // Literals: unterminated, across a line, a bad escape, and a
        // character literal that is not one scalar value.
        ("\"abc", 0),
        ("f \"abc\nd\"", 2),
        ("\"\\q\"", 0),
        ("\"\\u41\"", 0),
        ("\"\\u{}\"", 0),
        ("\"\\u{4g}\"", 0),
        ("\"\\", 0),
        ("'a", 0),
        ("''", 0),
        ("'ab'", 0),
        ("'\n'", 0),
        ("'\\u{41}x'", 0),
    ];
    let mut reasons = std::collections::HashSet::new();
    for (source, at) in refused {
        let (_, where_) = scan(source);
        let where_ = where_.unwrap_or_else(|| panic!("{source:?} is not refused"));
        assert_eq!(where_.start, *at, "{source:?}");
        assert!(lex(source).is_err(), "the lexer takes {source:?}");
        assert_agree(source, "a refusal");
        reasons.insert(ScanRefusal::of_code(where_.reason).expect("a reason"));
    }
    // Every reason a source given as text can be refused for is among them.
    let missing: Vec<ScanRefusal> =
        ScanRefusal::ALL.iter().copied().filter(|reason| *reason != ScanRefusal::NotUtf8 && !reasons.contains(reason)).collect();
    assert_eq!(missing, []);
}

#[test]
fn the_reasons_are_the_modules() {
    // `def REFUSED_UNEXPECTED: u64 = 1;` and its fellows are the lexer's
    // `ScanRefusal` numbering, and each `FAIL_*` state refuses for the
    // reason its name says.
    let module = include_str!("../../../lib/lang/lexer/lexer_scan.hthr");
    let camel = |name: &str| name.split('_').map(|word| word[..1].to_string() + &word[1..].to_lowercase()).collect::<String>();
    let mut seen = 0;
    for line in module.lines() {
        if let Some(rest) = line.strip_prefix("def REFUSED_") {
            let (name, value) = rest.split_once(": u64 = ").expect("a reason's definition");
            let code: u64 = value.trim_end_matches(';').parse().expect("a reason's code");
            let reason = ScanRefusal::of_code(code).unwrap_or_else(|| panic!("REFUSED_{name} = {code} is no `ScanRefusal`"));
            let name = camel(name);
            assert_eq!(format!("{reason:?}").to_lowercase(), name.to_lowercase(), "REFUSED_{name} = {code}");
            seen += 1;
        }
        if let Some(rest) = line.strip_prefix("def FAIL_") {
            let (name, value) = rest.split_once(": u64 = ").expect("a refusing state's definition");
            let state = u64::from_str_radix(value.trim_end_matches(';').trim_start_matches("0x"), 16).expect("hexadecimal");
            assert!(failed(state), "FAIL_{name}");
            let reason = ScanRefusal::of_code(scanner::accept(state)).expect("a reason");
            assert_eq!(format!("{reason:?}").to_lowercase(), camel(name).to_lowercase(), "FAIL_{name}");
        }
    }
    assert_eq!(seen, ScanRefusal::ALL.len());
    for (index, reason) in ScanRefusal::ALL.iter().enumerate() {
        assert_eq!(*reason as u64, index as u64 + 1);
        assert_eq!(ScanRefusal::of_code(*reason as u64), Some(*reason));
    }
    assert_eq!(ScanRefusal::of_code(0), None);
}

#[test]
fn a_value_is_refused_by_what_reads_it() {
    // The three refusals about a value: each is a well-shaped token to the
    // scanner, and refused when its span is read.
    for source in ["1e99999999999", "\"\\u{D800}\"", "'\\u{110000}'", "·₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉₉"] {
        let (tokens, refused) = scan(source);
        assert_eq!(refused, None, "{source:?}");
        assert_eq!(tokens.len(), 2, "{source:?}");
        assert!(value(source, tokens[0]).is_none(), "{source:?} has a value");
        assert!(lex(source).is_err(), "the lexer takes {source:?}");
        assert_eq!(lex_linked(source), None);
    }
}

// ---------------------------------------------------------------------------
// The loop, which is linked too.

/// The loop of `scanner::token` in Rust, over the automaton's three linked
/// functions: the longest token from `at`, the last position accepted at
/// remembered. This is what `Scanner` ran before the loop was one linked
/// function, and it is the reference that function is held to here at
/// offsets no scan starts from.
fn munch(source: &[u8], at: usize, previous: u64) -> Result<(u64, usize), (u64, usize)> {
    let mut state = scanner::begin(previous);
    let mut last = Err((ScanRefusal::Unexpected as u64, at));
    let mut next = at;
    loop {
        let byte = source.get(next).map_or(END, |byte| u64::from(*byte));
        state = scanner::step(state, byte);
        if failed(state) {
            return Err((scanner::accept(state), next));
        }
        if state == DEAD || byte == END {
            return last;
        }
        next += 1;
        let kind = scanner::accept(state);
        if kind != 0 {
            last = Ok((kind, next));
        }
    }
}

/// What a token may come after: nothing, each kind a shift may begin
/// after, one it may not, and a word that is no kind.
const BEFORE: [u64; 6] = [0, Kind::Space as u64, Kind::LParen as u64, Kind::Comma as u64, Kind::Ident as u64, 1 << 40];

fn assert_token_is_the_loops(source: &[u8], at: usize, what: &str) {
    for previous in BEFORE {
        assert_eq!(scanner::token(source, at, previous), munch(source, at, previous), "{what}: from {at}, after {previous}");
    }
}

#[test]
fn the_linked_loop_is_the_loop_over_the_automaton() {
    // From every offset of every probe, the ones inside a token and inside
    // a multi-byte character among them, and from past the end, where
    // nothing is read and nothing is a token, as far as an offset can be
    // (below 2^47, where a span is lent).
    for source in PROBES.iter().chain(BEYOND).chain(PIECES) {
        let source = source.as_bytes();
        for at in (0..=source.len() + 2).chain([source.len() + 4096, (1 << 47) - 1]) {
            assert_token_is_the_loops(source, at, &String::from_utf8_lossy(source));
        }
    }
    // Bytes that are no text at all: the automaton takes any byte.
    let mut lcg = Lcg(0x70ce_17);
    for round in 0..2000 {
        let bytes: Vec<u8> = (0..lcg.below(40)).map(|_| if lcg.below(3) == 0 { lcg.word() as u8 } else { b"a1 \n\"'/.>:=-"[lcg.below(12)] }).collect();
        for at in 0..=bytes.len() {
            assert_token_is_the_loops(&bytes, at, &format!("round {round}"));
        }
    }
    // A token longer than any register of state could count by accident:
    // the end is a position, not a length.
    let long = format!("// {}\n{}", "c".repeat(70_000), "a".repeat(70_000));
    assert_eq!(scanner::token(long.as_bytes(), 0, 0), Ok((Kind::Comment as u64, 70_003)));
    assert_eq!(scanner::token(long.as_bytes(), 70_004, Kind::Space as u64), Ok((Kind::Ident as u64, 140_004)));
    assert_eq!(scanner::token(long.as_bytes(), 70_003, Kind::Comment as u64), Ok((Kind::Space as u64, 70_004)));
    // And so is a refusal's offset: an unterminated literal refused at the
    // end, past every register's worth.
    let open = format!("\"{}", "s".repeat(70_000));
    assert_eq!(scanner::token(open.as_bytes(), 0, 0), Err((ScanRefusal::Unterminated as u64, 70_001)));
}

// Every offset of the scanner's own sources, and every offset a scan of
// the repository's sources starts from (the oracle below walks those too,
// through `Scanner`; this is the word itself, kind and end).
#[test]
fn the_linked_loop_at_every_offset_of_the_lexer_sources() {
    let mut offsets = 0;
    for (path, text) in corpus() {
        let source = text.as_bytes();
        if path.components().any(|part| part.as_os_str() == "lexer") {
            for at in 0..=source.len() {
                assert_token_is_the_loops(source, at, &path.display().to_string());
            }
            offsets += source.len();
        }
    }
    assert!(offsets > 50_000, "only {offsets} offsets: the lexer's sources were not found");
}

// ---------------------------------------------------------------------------
// The oracle.

#[test]
fn every_source_in_the_repository_lexes_the_same() {
    let corpus = corpus();
    let mut tokens = 0;
    let mut seen = std::collections::HashSet::new();
    for (path, text) in &corpus {
        assert_agree(text, &path.display().to_string());
        if let Ok(theirs) = lex(text) {
            tokens += theirs.len();
            seen.extend(theirs.iter().map(|tok| kind_of(&tok.kind)));
        }
    }
    // The corpus is not vacuous: it is large, and it spells every kind of
    // token there is but four that no source file happens to use (the
    // hand-written tests above and the generated strings below hold those).
    assert!(tokens > 1_000_000, "{tokens} tokens in {} sources", corpus.len());
    let missing: Vec<Kind> =
        Kind::ALL.iter().copied().filter(|kind| !matches!(kind, Kind::Space | Kind::Comment) && !seen.contains(kind)).collect();
    assert_eq!(missing, [Kind::LSemantic, Kind::RSemantic, Kind::Dollar, Kind::EqEq]);
}

/// The pieces tokens are made of, and the pieces refusals are made of.
const PIECES: &[&str] = &[
    "a", "b", "e", "E", "f", "p", "P", "x", "o", "u", "n", "z", "G", "_", "0", "1", "7", "8", "9", "0x", "0o", "0b",
    "0X", ".", "+", "-", "e5", "p3", "1e", "0x1.", "::", ":", ":=", "=", "==", "=>", "<", "<=", "<-", "<->", "<<",
    ">", ">>", "|", "|-", "||", "&", "&&", "!", "!=", "++", "*", "/", "//", "%", "^", "@", "$", "?", ",", ";", "(",
    ")", "{", "}", "[", "]", " ", "  ", "\t", "\n", "\r", "\u{c}", "\u{b}", "\"", "'", "\\", "\\n", "\\u", "\\u{",
    "\\u{41}", "\\u{D800}", "\\u{110000}", "\\0", "\\'", "\\\"", "'a'", "\"s\"", "λ", "¬", "·", "₀", "₁", "₉", "⁻",
    "¹", "⁻¹", "∙", "≈", "⊔", "⊓", "∧", "∨", "↔", "←", "∃", "∑", "∏", "↑", "∀", "≠", "⊢", "→", "∥", "⟨", "⟩", "⟦",
    "⟧", "δ", "é", "²", "₊", "∘", "⟪", "😀", "#", "`", "~", "\u{0}", "\u{7f}", "\u{80}", "\u{2028}", "⊕", "i",
    "u8", "i64", "u0",
];

/// Narrower alphabets, so that a long numeral, a long literal or a run of
/// operator characters is common and not a one-in-a-million draw.
const THEMES: &[&[&str]] = &[
    &["0", "1", "7", "9", "a", "f", "e", "E", "p", "P", "x", "o", "b", "g", "_", ".", "+", "-", "0x", "0o", "0b", " "],
    &["0", "1", "9", "0x", "0b", "0o", "f", "u", "i", "u8", "i64", "u0", "_", ".", "e", "p3", "x", " "],
    &["0x", "1", "8", "a", "f", "_", ".", "p", "p3", "p+", "p-1", "P", "(", " "],
    &["\"", "'", "\\", "u", "{", "}", "4", "1", "D800", "n", "q", "a", "é", "→", "😀", "\n", " ", "//"],
    &["<", ">", "-", "=", "|", "&", ":", "+", "!", "/", "?", "a", "_", " ", "(", ",", "\n", "//", "0"],
    &["·", "₀", "₁", "₉", "⁻", "¹", "⁻¹", "→", "∀", "λ", "¬", "\u{e2}", "\u{2080}", "\u{2189}", "a", "1", " "],
];

#[test]
fn strings_of_token_pieces_lex_the_same() {
    let mut random = Lcg(0x5ca11e7);
    let mut refused = 0;
    let rounds = 600_000;
    for round in 0..rounds {
        let pieces = match random.below(2 * THEMES.len()) {
            theme if theme < THEMES.len() => THEMES[theme],
            _ => PIECES,
        };
        let mut source = String::new();
        for _ in 0..1 + random.below(9) {
            source.push_str(random.pick(pieces));
        }
        assert_agree(&source, &format!("round {round}"));
        refused += usize::from(lex(&source).is_err());
    }
    // Both verdicts are well represented, so neither side of `agree` is idle.
    assert!(refused > rounds / 10 && refused < rounds * 9 / 10, "{refused} of {rounds} refused");
}

/// Characters past ASCII: every one a token is spelled with, and for each
/// byte the automaton can be left waiting after, one that shares it and is
/// no token.
const BEYOND: &[&str] = &[
    "λ", "¬", "·", "₀", "₁", "₉", "⁻", "¹", "∙", "≈", "⊔", "⊓", "⊕", "∧", "∨", "↔", "←", "∃", "∑", "∏", "↑", "∀", "≠", "⊢",
    "→", "∥", "⟨", "⟩", "⟦", "⟧", "ε", "£", "²", "↓", "∂", "≤", "⊗", "⟪", "⁺", "₊", "€", "‖", "δ", "é", "\u{80}",
    "\u{7ff}", "\u{800}", "한", "\u{ffff}", "😀", "\u{10ffff}",
];

/// What follows the edge under test: enough to finish any token the edge
/// left open, or to show that it cannot be finished.
const AFTER: &[&str] = &[
    "", "0", "1", "8", "a", "e", "f", "p", "x", "g", "u", "n", "_", ".", "+", "-", ":", "=", ">", "<", "|", "&", "/",
    "\"", "'", "\\", "{", "}", " ", "\n", "(", "¹", "₁", "→", "é", "i",
];
const AFTER_TWICE: &[&str] = &["1", "a", "e", "p", "_", ".", "+", ":", ">", "'", "\"", "}", " "];

/// The automaton's state after a whole string from a start state, with the
/// loop's restarts left out: `None` once it has stopped or refused.
fn state_after(start: u64, text: &str) -> Option<u64> {
    let mut state = start;
    for byte in text.bytes() {
        state = scanner::step(state, u64::from(byte));
        if state == DEAD || failed(state) {
            return None;
        }
    }
    Some(state)
}

#[test]
fn every_edge_of_the_automaton_is_the_lexers() {
    // Random strings rarely walk deep into a numeral or an escape, so this
    // test walks there on purpose. For every state the automaton can rest
    // in between two characters, the shortest string that leads to it; then
    // every character after that string, each followed by every ending in
    // `AFTER`. Each such source is compared with the lexer, so a wrong edge
    // out of any state shows as a different token or a different verdict.
    let mut alphabet: Vec<String> = (0..128u8).map(|byte| char::from(byte).to_string()).collect();
    alphabet.extend(BEYOND.iter().map(|text| text.to_string()));
    // A token after `]` starts in the plain state, and one at the start of
    // the source in the state that lets `>>` be a shift.
    let mut resting: Vec<(u64, String)> =
        vec![(scanner::begin(0), String::new()), (scanner::begin(Kind::RBracket.code()), "]".to_string())];
    let mut next = 0;
    while next < resting.len() {
        let (state, path) = resting[next].clone();
        for symbol in &alphabet {
            let Some(to) = state_after(state, symbol) else { continue };
            if !resting.iter().any(|(seen, _)| *seen == to) {
                resting.push((to, format!("{path}{symbol}")));
            }
        }
        next += 1;
    }
    assert!(resting.len() > 60, "{} resting states", resting.len());
    let mut endings: Vec<String> = AFTER.iter().map(|text| text.to_string()).collect();
    for first in AFTER_TWICE {
        endings.extend(AFTER_TWICE.iter().map(|second| format!("{first}{second}")));
    }
    let mut sources = 0;
    let mut refused = 0;
    for (_, path) in &resting {
        for symbol in &alphabet {
            for ending in &endings {
                let source = format!("{path}{symbol}{ending}");
                assert_agree(&source, "an edge");
                sources += 1;
                refused += usize::from(scan(&source).1.is_some());
            }
        }
    }
    assert!(sources > 1_000_000 && refused > sources / 10, "{refused} of {sources} refused");
}

#[test]
fn every_line_of_the_library_lexes_the_same_with_one_character_changed() {
    let mut random = Lcg(0x11b);
    let mut lines = 0;
    let mut refused = 0;
    for (path, text) in corpus() {
        if !path.starts_with(root().join("lib")) {
            continue;
        }
        for (number, line) in text.lines().enumerate() {
            if line.is_empty() {
                continue;
            }
            let what = format!("{}:{}", path.display(), number + 1);
            // One line in eight is changed: a character dropped, doubled,
            // or replaced by a piece.
            if random.below(8) != 0 {
                continue;
            }
            assert_agree(line, &what);
            let starts: Vec<usize> = line.char_indices().map(|(at, _)| at).collect();
            let at = starts[random.below(starts.len())];
            let width = line[at..].chars().next().expect("a character").len_utf8();
            let changed = match random.below(3) {
                0 => format!("{}{}", &line[..at], &line[at + width..]),
                1 => format!("{}{}{}", &line[..at + width], &line[at..at + width], &line[at + width..]),
                _ => format!("{}{}{}", &line[..at], random.pick(PIECES), &line[at + width..]),
            };
            assert_agree(&changed, &format!("{what}, changed"));
            lines += 1;
            refused += usize::from(lex(&changed).is_err());
        }
    }
    assert!(lines > 10_000, "{lines} lines");
    assert!(refused > 100, "{refused} of {lines} changed lines refused");
}

// ---------------------------------------------------------------------------
// The specification, evaluated.

/// Short sources that between them hold every kind of token and every kind
/// of refusal. `lib/_tests/lang/lexer/lexer_tokens_tests.hthr` states, for
/// each, that the Heather loop over the Heather automaton (`Scanned::of`,
/// evaluated by the kernel) gives exactly what the linked code gave here.
/// Short, because the kernel evaluates a 64-bit comparison bit by bit and a
/// declaration has a fuel.
const PROBES: &[&str] = &[
    "",
    "  \t\n",
    "fn f(x: Nat) → Nat { x }",
    "let y := nat::Nat::sub(a, 1);",
    "// a comment\nx /y",
    "a >> b; List<List<A>>",
    "(>> ,>> x>>",
    "0x1f 0o17 0b101 1_000",
    "1.5 1e-3 0x1.8p3 1_e5",
    "1.max(2) 0xff.f() 1..2",
    "\"a\\\"b\" 'c' '\\n' '\\u{1F600}'",
    "'é' \"→ // s\"",
    "?p ? p x::{y} a:::b",
    "<-> <- <= << < -> - ++ +",
    "=> == = |- || | && & := :: :",
    "λ ¬ ∙ ≈ ⊔ ⊓ ∧ ∨ ↔ ←",
    "∃ ∑ ∏ ↑ ∀ ≠ ⊢ → ∥",
    "⟨a, b⟩ ⟦c⟧ x⁻¹ ·₁₂ ·",
    "@ . ; ! * ^ % $ / [ ] { }",
    "x 12abc",
    "a != b",
    "s \"abc",
    "'ab'",
    "0x",
    "1.5e",
    "x δ",
    "0x1.8_p3",
    "\"\\q\"",
    "a # b",
    "1__0",
    "a ⊕ ~b 42u64 0x1fi8 0u0",
    "x 42u",
    "x 1u08",
    "x 1.5e+",
    "0x_1 0o",
    "\"\\u41\"",
    "'a\\qb'",
];

/// A Heather string literal for a source.
fn heather_literal(source: &str) -> String {
    let mut out = String::from("\"");
    for ch in source.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn kind_constant(kind: Kind) -> String {
    let mut name = String::from("KIND");
    let debug = format!("{kind:?}");
    let letters: Vec<char> = debug.chars().collect();
    for (at, ch) in letters.iter().enumerate() {
        // `LParen` is `LPAREN` and `ArgSlot` is `ARG_SLOT`: a new word
        // begins at a capital that follows a small letter.
        if at == 0 || (ch.is_uppercase() && letters[at - 1].is_lowercase()) {
            name.push('_');
        }
        name.extend(ch.to_uppercase());
    }
    name
}

fn reason_constant(reason: ScanRefusal) -> String {
    let mut name = String::from("REFUSED");
    let debug = format!("{reason:?}");
    let letters: Vec<char> = debug.chars().collect();
    for (at, ch) in letters.iter().enumerate() {
        if at == 0 || (ch.is_uppercase() && letters[at - 1].is_lowercase()) {
            name.push('_');
        }
        name.extend(ch.to_uppercase());
    }
    name
}

fn probes_module() -> String {
    let module = include_str!("../../../lib/lang/lexer/lexer_scan.hthr");
    let mut out = String::from(
        "// GENERATED by `scripts/lexer-probes`; edit `PROBES` in\n\
         // `crates/linked/tests/scanner.rs`, not this file.\n\
         //\n\
         // The scanner's specification evaluated by the kernel\n\
         // (`lib/lang/lexer/lexer_tokens.hthr`): for each short source below,\n\
         // `Scanned::of_text` is the tokens, or the refusal, that the linked\n\
         // scanner gives for it, which `crates/linked/tests/scanner.rs` holds\n\
         // to the Rust lexer. So the three agree on these: the Rust lexer and\n\
         // the compiled automaton under Rust's loop by test, and the Heather\n\
         // loop over the Heather automaton by these theorems. Between them\n\
         // the sources hold every kind of token and every kind of refusal.\n\
         // Tests, not library (docs/test-value-audit.md §4.5).\n\
         import bitvec; import bool; import list; import logic; import nat; import option; import string; import utf8;\n\
         import lexer_scan; import lexer_tokens;\n\n",
    );
    // Every state, by the module's own definitions.
    let states: Vec<&str> = module
        .lines()
        .filter_map(|line| line.strip_prefix("def ")?.split_once(": u64 = "))
        .map(|(name, _)| name)
        .filter(|name| !name.starts_with("KIND_") && !name.starts_with("REFUSED_") && *name != "END")
        .collect();
    out.push_str("// Every state of the automaton: the stops, the starts, each family's, and a\n// finished token of each kind that has one.\n");
    out.push_str("fn lexer_states() → List<u64> {\n");
    let mut row = String::from("    [");
    for (at, state) in states.iter().enumerate() {
        let item = format!("{state}{}", if at + 1 < states.len() { "," } else { "]" });
        if row.len() + 1 + item.len() > 110 {
            out.push_str(row.trim_end());
            out.push('\n');
            row = String::from("        ");
        } else if !row.ends_with('[') {
            row.push(' ');
        }
        row.push_str(&item);
    }
    out.push_str(row.trim_end());
    out.push_str("\n}\n\n");
    out.push_str(
        "// After the last byte the loop gives `END` once, and no state asks for more:\n\
         // each stops there or refuses.\n\
         fn lexer_stops(states: List<u64>) → Bool {\n    match states {\n        Nil => True,\n        \
         Cons(s, rest) => (scan_step(s, END).eq_bit(DEAD) || scan_step(s, END).band(255).eq_bit(FAIL)) && lexer_stops(rest),\n    }\n}\n\n\
         theorem lexer_states_stop_at_the_end(): lexer_stops(lexer_states()) = True { refl }\n\n\
         // A state's kind is the one in its name: an identifier's, and a finished\n\
         // arrow's.\n\
         theorem lexer_accepts_by_state(): scan_accept(IDENT) = KIND_IDENT ∧ scan_accept(DONE_ARROW) = KIND_ARROW ∧ scan_accept(START) = 0 {\n    ⟨refl, ⟨refl, refl⟩⟩\n}\n\n",
    );
    for (number, source) in PROBES.iter().enumerate() {
        let (tokens, refused) = scan(source);
        let expected = match refused {
            Some(refused) => {
                let reason = ScanRefusal::of_code(refused.reason).expect("a reason");
                format!("Scanned::Refused({}, {}, {})", refused.start, reason_constant(reason), refused.at)
            }
            None => {
                let tokens: Vec<String> = tokens
                    .iter()
                    .map(|token| format!("Token({}, {}, {})", kind_constant(token.kind), token.start, token.end))
                    .collect();
                format!("Scanned::Tokens([{}])", tokens.join(", "))
            }
        };
        out.push_str(&format!(
            "theorem lexer_probe_{number}(): Scanned::of_text({}) =\n    {expected}\n{{ refl }}\n\n",
            heather_literal(source)
        ));
    }
    out.truncate(out.trim_end().len());
    out.push('\n');
    out
}

#[test]
fn the_evaluated_probes_are_what_the_scanner_gives() {
    // The probes agree with the lexer, and between them hold every kind.
    let mut seen = std::collections::HashSet::new();
    let mut refused = 0;
    for source in PROBES {
        assert!(source.len() <= 48, "{source:?} is {} bytes: too long to evaluate in one declaration", source.len());
        assert_agree(source, "a probe");
        let (tokens, at) = scan(source);
        seen.extend(tokens.iter().map(|token| token.kind));
        refused += usize::from(at.is_some());
    }
    let missing: Vec<Kind> =
        Kind::ALL.iter().copied().filter(|kind| !matches!(kind, Kind::Space | Kind::Comment) && !seen.contains(kind)).collect();
    assert!(missing.is_empty(), "no probe holds {missing:?}");
    assert!(refused >= 10);
    // The checked-in theorems state exactly what the linked scanner gives.
    let path = root().join("lib/_tests/lang/lexer/lexer_tokens_tests.hthr");
    let expected = probes_module();
    if std::env::var_os("HEATHER_WRITE_LEXER_PROBES").is_some() {
        std::fs::write(&path, &expected).expect("write the probes");
    }
    let found = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(found == expected, "{} is not what `PROBES` gives: run scripts/lexer-probes", path.display());
}

// ---------------------------------------------------------------------------
// The lexer run by the scanner: `heather_syntax::lexer::lex_scanned`, which
// is what `HEATHER_LEXER=linked` puts under `lex` (`install_scanner`,
// `issues/self-lexer-linked.md`). Nothing in this binary installs a scanner
// (that is the process's one choice, and `crates/cli/tests/check.rs` makes
// it in a process of its own), so `lex` and `lex_while` here are the Rust
// lexer and the oracle.

/// `lex_scanned` by the linked scanner on one source: the lexer's tokens
/// with every one of them the scanner's cut, or the lexer's refusal, message
/// and place. Answers whether the source lexed.
fn run_by_the_scanner(source: &str) -> Result<bool, String> {
    let theirs = lex_rust(source);
    let (ours, cut) = lex_scanned(scanner::token, source);
    match (theirs, ours) {
        (Ok(theirs), Ok(ours)) => {
            let (theirs, ours) = (plain(&theirs), plain(&ours));
            if theirs != ours {
                let at = theirs.iter().zip(&ours).position(|(a, b)| a != b).unwrap_or(theirs.len().min(ours.len()));
                return Err(format!("token {at}: the lexer has {:?}, the scanner's run {:?}", theirs.get(at), ours.get(at)));
            }
            if !cut {
                return Err("the tokens are the lexer's own: the scanner's cut was given up".to_string());
            }
            Ok(true)
        }
        (Err(theirs), Err(ours)) => {
            if (theirs.msg.as_str(), theirs.span.start, theirs.span.end) != (ours.msg.as_str(), ours.span.start, ours.span.end) {
                return Err(format!("the lexer refuses with {theirs:?}, the scanner's run with {ours:?}"));
            }
            if !cut {
                return Err("the refusal is the lexer's own: the scanner's was given up".to_string());
            }
            Ok(false)
        }
        (Ok(_), Err(ours)) => Err(format!("the lexer accepts what the scanner's run refuses: {}", ours.msg)),
        (Err(theirs), Ok(_)) => Err(format!("the scanner's run accepts what the lexer refuses: {}", theirs.msg)),
    }
}

fn assert_run_by_the_scanner(source: &str, what: &str) -> bool {
    match run_by_the_scanner(source) {
        Ok(lexed) => lexed,
        Err(why) => panic!("{what}: {why}\n  source: {source:?}"),
    }
}

#[test]
fn nothing_here_installs_a_scanner() {
    assert!(!scanner_installed());
    assert_eq!(scanner_counts(), (0, 0));
}

/// The numbering is written once, in `TOKEN_KINDS`, and both crates read
/// it from the generated `kinds.rs`; what is left to hold is the lexer's
/// naming (`TokKind::scan_kind`): every kind but the two a lexer drops is
/// some token's, which this finds on every source of the repository.
#[test]
fn the_lexers_codes_are_the_scanners() {
    assert_eq!(SCAN_SPACE, Kind::Space.code());
    assert_eq!(SCAN_COMMENT, Kind::Comment.code());
    let mut seen = std::collections::HashSet::new();
    let mut hold = |source: &str| {
        for tok in lex(source).expect("lexes") {
            seen.insert(kind_of(&tok.kind));
        }
    };
    for (_, text) in corpus() {
        if lex(&text).is_ok() {
            hold(&text);
        }
    }
    hold("⟦ ⟧ $ == ⊕ ~ 42u64");
    let missing: Vec<Kind> =
        Kind::ALL.iter().copied().filter(|kind| !matches!(kind, Kind::Space | Kind::Comment) && !seen.contains(kind)).collect();
    assert_eq!(missing, []);
}

#[test]
fn the_scanners_run_is_the_lexer_on_every_source_in_the_repository() {
    let corpus = corpus();
    let mut lexed = 0;
    for (path, text) in &corpus {
        lexed += usize::from(assert_run_by_the_scanner(text, &path.display().to_string()));
    }
    // All but the fixtures that are there to be refused.
    assert!(lexed > 300 && lexed + 40 > corpus.len(), "{lexed} of {} sources lexed", corpus.len());
}

#[test]
fn the_scanners_run_is_the_lexer_on_strings_of_token_pieces() {
    let mut random = Lcg(0x1e8ed);
    let mut refused = 0;
    let rounds = 300_000;
    for round in 0..rounds {
        let pieces = match random.below(2 * THEMES.len()) {
            theme if theme < THEMES.len() => THEMES[theme],
            _ => PIECES,
        };
        let mut source = String::new();
        for _ in 0..1 + random.below(9) {
            source.push_str(random.pick(pieces));
        }
        refused += usize::from(!assert_run_by_the_scanner(&source, &format!("round {round}")));
    }
    assert!(refused > rounds / 10 && refused < rounds * 9 / 10, "{refused} of {rounds} refused");
}

/// One line in sixteen of every source, as it is and with one character
/// changed, and at each: the whole line, and the line read only as far as
/// each of its tokens (`lex_while`, which is how an import list is read
/// without lexing the module under it). Stopping early holds where `Eof`
/// lands when a token is refused: at that token's start, whatever its kind.
#[test]
fn the_scanners_run_stops_where_the_lexer_stops() {
    let mut random = Lcg(0x57095);
    let (mut lines, mut stops, mut refused) = (0, 0, 0);
    for (path, text) in corpus() {
        for (number, line) in text.lines().enumerate() {
            if line.is_empty() || random.below(16) != 0 {
                continue;
            }
            let what = format!("{}:{}", path.display(), number + 1);
            let starts: Vec<usize> = line.char_indices().map(|(at, _)| at).collect();
            let at = starts[random.below(starts.len())];
            let width = line[at..].chars().next().expect("a character").len_utf8();
            let changed = format!("{}{}{}", &line[..at], random.pick(PIECES), &line[at + width..]);
            for source in [line, changed.as_str()] {
                refused += usize::from(!assert_run_by_the_scanner(source, &what));
                let whole = lex_while(source, |_| true);
                assert_eq!(plain(&whole), plain(&lex_while_scanned(scanner::token, source, |_| true)), "{what}: {source:?}");
                for stop in 0..whole.len() {
                    let mut asked = 0;
                    let theirs = lex_while(source, |_| {
                        asked += 1;
                        asked <= stop
                    });
                    let mut asked = 0;
                    let ours = lex_while_scanned(scanner::token, source, |_| {
                        asked += 1;
                        asked <= stop
                    });
                    assert_eq!(plain(&theirs), plain(&ours), "{what}: {source:?} stopped at token {stop}");
                    if stop + 1 < whole.len() {
                        let at = whole[stop].span.start;
                        assert_eq!(theirs.last().map(|tok| (tok.span.start, tok.span.end)), Some((at, at)), "{what}: {source:?} stopped at token {stop}");
                    }
                    stops += 1;
                }
            }
            lines += 1;
        }
    }
    assert!(lines > 5_000 && stops > 50_000, "{lines} lines, {stops} stops");
    assert!(refused > 100, "{refused} refused");
}

// Scanners that are wrong, for what the lexer does about each.

/// A refusal for no reason the lexer knows, everywhere.
fn refuses_everything(_: &[u8], at: usize, _: u64) -> Result<(u64, usize), (u64, usize)> {
    Err((0, at))
}

/// The linked scanner as far as byte 12, and a refusal for no reason from
/// there.
fn refuses_late(source: &[u8], at: usize, previous: u64) -> Result<(u64, usize), (u64, usize)> {
    if at >= 12 { Err((0, at)) } else { scanner::token(source, at, previous) }
}

/// A refusal for a reason that cannot be where it is said to be: a bad
/// escape at the start of every token, refused before it starts.
fn misplaces_refusals(_: &[u8], at: usize, _: u64) -> Result<(u64, usize), (u64, usize)> {
    Err((ScanRefusal::Escape as u64, at.wrapping_sub(1)))
}

/// Every identifier called a numeral.
fn mislabels(source: &[u8], at: usize, previous: u64) -> Result<(u64, usize), (u64, usize)> {
    let (code, end) = scanner::token(source, at, previous)?;
    Ok((if code == Kind::Ident.code() { Kind::Num.code() } else { code }, end))
}

fn ends_nowhere(_: &[u8], at: usize, _: u64) -> Result<(u64, usize), (u64, usize)> {
    Ok((Kind::Ident.code(), at))
}

fn ends_past_the_source(source: &[u8], _: usize, _: u64) -> Result<(u64, usize), (u64, usize)> {
    Ok((Kind::Ident.code(), source.len() + 8))
}

/// One byte at a time, which is inside a character where one is longer.
fn ends_inside_a_character(_: &[u8], at: usize, _: u64) -> Result<(u64, usize), (u64, usize)> {
    Ok((Kind::Forall.code(), at + 1))
}

/// Every identifier of two characters or more cut after its first.
fn cuts_identifiers_short(source: &[u8], at: usize, previous: u64) -> Result<(u64, usize), (u64, usize)> {
    let (code, end) = scanner::token(source, at, previous)?;
    Ok((code, if code == Kind::Ident.code() && end > at + 1 && source[at + 1].is_ascii_alphabetic() { at + 1 } else { end }))
}

const WRONGED: &[&str] = &[
    "theorem two(): 1 + 1 = 2 { refl }",
    "fn id<A: Type>(x: A) → A { x } // the identity\n",
    "∀ x, x ≤ y ∧ \"a\\n\" ++ 'c' → ?hole₁ 0x1f 2.5e3",
    "let s = \"unterminated",
    "a ` b",
    "",
];

/// A scanner that refuses for no reason the lexer knows or at no place the
/// reason can be, names a kind the bytes are not, or answers an end that is
/// no end leaves the whole source to the lexer: its tokens or its refusal,
/// and never a panic or a loop.
#[test]
fn a_scanner_that_is_wrong_about_a_token_is_not_listened_to() {
    let scanners: [(&str, Scan); 7] = [
        ("refuses everything", refuses_everything),
        ("refuses late", refuses_late),
        ("misplaces refusals", misplaces_refusals),
        ("mislabels", mislabels),
        ("ends nowhere", ends_nowhere),
        ("ends past the source", ends_past_the_source),
        ("ends inside a character", ends_inside_a_character),
    ];
    for source in WRONGED {
        let theirs = lex_rust(source);
        for (name, scan) in scanners {
            let (ours, cut) = lex_scanned(scan, source);
            match (&theirs, &ours) {
                (Ok(theirs), Ok(ours)) => assert_eq!(plain(theirs), plain(ours), "{name}: {source:?}"),
                (Err(theirs), Err(ours)) => assert_eq!((&theirs.msg, theirs.span.start), (&ours.msg, ours.span.start), "{name}: {source:?}"),
                _ => panic!("{name}: {source:?}: the lexer has {theirs:?}, the run {ours:?}"),
            }
            // The scanner's answer stood only where it was never wrong: the
            // empty source, and a source `refuses_late` or `mislabels` never
            // got to be wrong about (`refuses_late` is the linked scanner
            // where that refuses before byte 12).
            let untouched = source.is_empty()
                || (name == "refuses late" && (source.len() <= 12 || self::scan(source).1.is_some_and(|refused| refused.start < 12)))
                || (name == "mislabels" && theirs.as_ref().is_ok_and(|toks| !toks.iter().any(|tok| matches!(tok.kind, TokKind::Ident(_)))));
            assert_eq!(cut, untouched, "{name}: {source:?}");
        }
    }
}

/// Giving up part way asks `keep` about no token twice: the tokens it kept
/// from the scanner's cut are the lexer's first tokens, and it is asked
/// again only from there.
#[test]
fn giving_the_scanner_up_asks_about_each_token_once() {
    let source = "theorem two(): 1 + 1 = 2 { refl }";
    for stop in 0..12 {
        let mut theirs_asked = Vec::new();
        let theirs = lex_while(source, |tok| {
            theirs_asked.push(tok.span.start);
            theirs_asked.len() <= stop
        });
        let mut ours_asked = Vec::new();
        let ours = lex_while_scanned(refuses_late, source, |tok| {
            ours_asked.push(tok.span.start);
            ours_asked.len() <= stop
        });
        assert_eq!(plain(&theirs), plain(&ours), "stopped at token {stop}");
        assert_eq!(theirs_asked, ours_asked, "stopped at token {stop}");
    }
}

/// What the lexer does not catch, said as a test so that it is not thought
/// to: a cut that is wrong but whose every piece is a token of the kind
/// named. The lexer reads each span alone, so `ab` cut as `a` and `b` is two
/// identifiers to it. What holds the linked scanner's cuts is the tests
/// above this section, over every source in the repository.
#[test]
fn a_wrong_cut_made_of_right_tokens_is_the_scanners_to_answer_for() {
    let source = "ab + c";
    let (ours, cut) = lex_scanned(cuts_identifiers_short, source);
    let ours = plain(&ours.expect("lexes"));
    assert!(cut);
    assert_eq!(ours.len(), 5);
    assert_ne!(ours, plain(&lex_rust(source).expect("lexes")));
}
