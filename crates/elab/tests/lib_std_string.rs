//! `lib/std/char.hthr` and `lib/std/string.hthr` — Unicode scalar values and
//! sequences of them as *specification* types (docs/string-char-design.md).
//!
//! The acceptance shape is `docs/testing-generated-terms.md`'s: every law is
//! exercised at a literal **and** at a neutral string, from a checking
//! position, with a negative control beside it. A closed scrutinee alone hid
//! three of the five defects that document was written about.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const CHAR: &str = include_str!("../../../lib/std/char.hthr");
const STRING: &str = include_str!("../../../lib/std/string.hthr");

const PREAMBLE: &str = "import logic;\nimport nat;\nimport list;\nimport char;\nimport string;\n";

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("char", CHAR),
        ("string", STRING),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
    e
}

fn check(body: &str) {
    let src = format!("{PREAMBLE}{body}");
    let mut e = elaborated();
    if let Err(error) = e.elab_module_source("probe", &src) {
        panic!("{}", error.render(&src));
    }
}

fn refused(body: &str) -> String {
    let src = format!("{PREAMBLE}{body}");
    let mut e = elaborated();
    match e.elab_module_source("probe", &src) {
        Ok(()) => panic!("accepted: {body}"),
        Err(error) => error.render(&src),
    }
}

#[test]
fn the_char_and_string_modules_check() {
    elaborated();
}

#[test]
fn a_char_is_its_code_and_nothing_else() {
    check(
        r#"
theorem code_decides(a, b: Char, p: a.code = b.code): a = b { code_injective(a, b, p) }
theorem round_trip(code: Nat, p: scalar(code)): ofNat(code, p).toNat() = code { refl }
// The witness is not part of the value: two proofs of the same code build
// the same character. At an OPEN code that is `scalar_unique` through
// `code_injective` rather than a conversion — the witness is relevant now
// (docs/string-char-design.md §5.1) — while at a closed one the two proofs
// inhabit `Unit` and are definitionally equal.
theorem witness_irrelevant(code: Nat, p, q: scalar(code)): ofNat(code, p) = ofNat(code, q) {
    code_injective(ofNat(code, p), ofNat(code, q), refl)
}
theorem witness_irrelevant_closed(p, q: scalar(97)): ofNat(97, p) = ofNat(97, q) {}
theorem surrogates_excluded(p: scalar(55296)): False { p }
// The witness is relevant and Bool-reflected, so its arithmetic reading is a
// lemma rather than a projection (docs/string-char-design.md §5.1).
theorem sound(code: Nat, p: scalar(code)): code < 0x110000 { scalar_sound(code, p).left }
theorem sound_surrogate(p: scalar(0xD800)): False {
    scalar_sound(0xD800, p).right(And(le_refl(0xD800), lt_succ_self(0xD800)))
}
"#,
    );
    // The negative control: the surrogate block really is outside `scalar`,
    // so no `decide` can build a character in it.
    let msg = refused("theorem bad(): scalar(55296) { decide }\n");
    assert!(msg.contains("decide") || msg.contains("NotConvertible"), "{msg}");
    let msg = refused("theorem bad(): scalar(1114112) { decide }\n");
    assert!(msg.contains("decide") || msg.contains("NotConvertible"), "{msg}");
    check("theorem boundaries(): scalar(55295) ∧ scalar(57344) ∧ scalar(1114111) { decide }\n");
}

#[test]
fn nth_reads_at_a_literal_and_at_an_open_string() {
    check(
        r#"
theorem literal_first(): "abc".nth(FZ) = 'a' { refl }
theorem literal_second(): "abc".nth(FS(FZ)) = 'b' { refl }
theorem literal_third(): "abc".nth(FS(FS(FZ))) = 'c' { refl }
// A read into an open tail reduces step by step: the length is a `Succ`
// at every `Cons`, so the `Fin` motive instantiates without the tail.
theorem open_tail(c: Char, rest: List<Char>):
    String(chars := Cons(c, rest)).nth(FZ) = c
{}
theorem open_tail_second(c, d: Char, rest: List<Char>):
    String(chars := Cons(c, Cons(d, rest))).nth(FS(FZ)) = d
{}
theorem open_tail_step(c: Char, rest: List<Char>, i: Fin(rest.len())):
    String(chars := Cons(c, rest)).nth(FS(i)) = String(chars := rest).nth(i)
{}
"#,
    );
    let msg = refused("theorem bad(): \"abc\".nth(FZ) = 'b' { refl }\n");
    assert!(!msg.is_empty(), "the wrong character must be refused");
    // Out of range is unwritable rather than wrong: there is no third index
    // into a two-character string.
    let msg = refused("theorem bad(): \"ab\".nth(FS(FS(FZ))) = 'a' { refl }\n");
    assert!(!msg.is_empty(), "an out-of-range index must be refused");
}

#[test]
fn take_and_drop_rebuild_the_string_at_a_literal_and_at_an_open_one() {
    check(
        r#"
theorem literal(): string::take("abc", 1) ++ string::drop("abc", 1) = "abc" {
    take_drop("abc", 1)
}
theorem literal_computes(): string::take("abc", 1) = "a" {}
theorem literal_drop_computes(): string::drop("abc", 1) = "bc" {}
theorem neutral(s: String, n: Nat): string::take(s, n) ++ string::drop(s, n) = s {
    take_drop(s, n)
}
theorem neutral_index(n: Nat): string::take("abc", n) ++ string::drop("abc", n) = "abc" {
    take_drop("abc", n)
}
"#,
    );
    let msg = refused("theorem bad(): string::take(\"abc\", 1) = \"ab\" { refl }\n");
    assert!(!msg.is_empty(), "a wrong split must be refused");
}

#[test]
fn appending_adds_the_lengths_at_a_literal_and_at_an_open_string() {
    check(
        r#"
theorem literal(): ("ab" ++ "cde").len() = 5 {}
theorem literal_value(): "ab" ++ "cde" = "abcde" { refl }
theorem neutral(s, t: String): (s ++ t).len() = s.len() + t.len() { string::len_append(s, t) }
theorem half_open(s: String): (s ++ "ab").len() = s.len() + 2 { string::len_append(s, "ab") }
"#,
    );
    let msg = refused("theorem bad(): (\"ab\" ++ \"cde\").len() = 6 { refl }\n");
    assert!(!msg.is_empty(), "a wrong length must be refused");
}

#[test]
fn equality_decides_at_literals_and_resolves_at_open_endpoints() {
    check(
        r#"
theorem literals_agree(): "hi" = "hi" { decide }
theorem literals_differ(): ¬("hi" = "ho") { decide }
theorem lengths_differ(): ¬("hi" = "h") { decide }
theorem empty_differs(): ¬("" = "h") { decide }
theorem chars_agree(): 'a' = 'a' { decide }
theorem chars_differ(): ¬('a' = 'b') { decide }
// The instance resolves at *neutral* endpoints too, and is the declared
// decider — resolution here is what a literal-only test would not see.
theorem neutral_instance(s, t: String, a, b: Char):
    decide_pick<s = t, Char>(a, b) = or_pick(string_eq_dec(s, t), a, b)
{ refl }
theorem neutral_char_instance(a, b: Char, x, y: Char):
    decide_pick<a = b, Char>(x, y) = or_pick(char_eq_dec(a, b), x, y)
{ refl }
theorem neutral_sound(s, t: String, p: s.chars = t.chars): s = t { chars_injective(s, t, p) }
"#,
    );
    // The negative controls: `decide` cannot prove a false equation, and
    // cannot prove a true-looking one it has no closed decision for.
    let msg = refused("theorem bad(): \"hi\" = \"ho\" { decide }\n");
    assert!(msg.contains("decide") || msg.contains("NotConvertible"), "{msg}");
    let msg = refused("theorem bad(s: String): s = \"hi\" { decide }\n");
    assert!(msg.contains("decide") || msg.contains("NotConvertible"), "{msg}");
}
