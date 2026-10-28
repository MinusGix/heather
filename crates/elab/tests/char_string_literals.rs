//! `'x'` and `"…"` (docs/string-char-design.md §3), on the numeral's ladder:
//! the spec type's introduction form at `Char`/`String`, and the
//! `CharLiteral`/`StringLiteral` classes at any other carrier.
//!
//! Shaped on `carrier_numerals.rs`. The five cases the design's §4 asks for
//! are one test each: a character at `Char`, a string at `String`, each at a
//! user carrier through its class, a literal at a carrier with no instance,
//! and a literal in inference position.

use crate::support;
use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const CHAR: &str = include_str!("../../../lib/std/text/char.hthr");
const STRING: &str = include_str!("../../../lib/std/text/string.hthr");

const PREAMBLE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport char;\nimport string;\n";

fn library() -> Elaborator {
    let mut e = support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("char", CHAR),
        ("string", STRING),
    ]);
    e
}

fn check(body: &str) {
    let src = format!("{PREAMBLE}{body}");
    let mut e = library();
    if let Err(error) = e.elab_module_source("probe", &src) {
        panic!("{}", error.render(&src));
    }
}

/// The negative half of every generated-term test
/// (docs/testing-generated-terms.md): the same shape, said wrongly.
fn refused(body: &str) -> String {
    let src = format!("{PREAMBLE}{body}");
    let mut e = library();
    match e.elab_module_source("probe", &src) {
        Ok(()) => panic!("accepted: {body}"),
        Err(error) => error.render(&src),
    }
}

#[test]
fn a_character_literal_at_char_is_its_code_with_a_decided_witness() {
    check(
        r#"
fn plain() -> Char { 'x' }
fn escaped() -> Char { '\n' }
fn unicode() -> Char { '\u{1F600}' }
fn argument(c: Char) -> Char { c }
fn through_a_call() -> Char { argument('x') }
fn in_a_list() -> List<Char> { ['a', 'b'] }
theorem plain_code(): plain().toNat() = 120 { refl }
theorem escaped_code(): escaped().toNat() = 10 { refl }
theorem unicode_code(): unicode().toNat() = 128512 { refl }
theorem literal_is_intro(): plain() = ofNat(120, decide) { refl }
theorem distinct(): ¬('a' = 'b') { decide }
theorem same(): 'a' = 'a' { decide }
"#,
    );
}

#[test]
fn a_string_literal_at_string_is_the_record_over_its_character_list() {
    check(
        r#"
fn empty() -> String { "" }
fn hello() -> String { "hi" }
fn escaped() -> String { "a\tb\\c\"d" }
theorem hello_chars(): hello().chars = Cons('h', Cons('i', Nil<Char>)) { refl }
theorem empty_chars(): empty().chars = Nil<Char> { refl }
theorem hello_len(): hello().len() = 2 {}
theorem escaped_len(): escaped().len() = 7 {}
theorem same(): "hi" = "hi" { decide }
theorem differ(): ¬("hi" = "ho") { decide }
"#,
    );
}

#[test]
fn another_carrier_goes_through_the_literal_classes() {
    check(
        r#"
inductive Tag { Mk(c: Char) }
instance CharLiteral<Tag> { ofChar := Mk }
inductive Note { Text(s: String) }
instance StringLiteral<Note> { ofString := Text }

fn tagged() -> Tag { 'x' }
fn noted() -> Note { "hi" }
fn tagged_argument(t: Tag) -> Tag { t }
fn through_a_call() -> Tag { tagged_argument('x') }
theorem tagged_value(): tagged() = Mk(ofNat(120, decide)) { refl }
theorem noted_value(): noted() = Text(String(chars := Cons('h', Cons('i', Nil<Char>)))) { refl }
theorem call_value(): through_a_call() = Mk('x') { refl }
"#,
    );
}

#[test]
fn a_carrier_with_no_instance_names_the_class_it_lacks() {
    let msg = refused("fn bad() -> Nat { 'x' }\n");
    assert!(msg.contains("CharLiteral<Nat>"), "{msg}");
    let msg = refused("fn bad() -> Nat { \"hi\" }\n");
    assert!(msg.contains("StringLiteral<Nat>"), "{msg}");
    // A carrier that has one class and not the other is not offered the
    // wrong one.
    let msg = refused(
        r#"
inductive Tag { Mk(c: Char) }
instance CharLiteral<Tag> { ofChar := Mk }
fn bad() -> Tag { "hi" }
"#,
    );
    assert!(msg.contains("StringLiteral<Tag>"), "{msg}");
}

#[test]
fn a_literal_without_its_module_says_which_import_is_missing() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn bad() -> Nat { 'x' }\n";
    let msg = match e.elab_module_source("probe", src) {
        Ok(()) => panic!("accepted a character literal with no `char` module"),
        Err(error) => error.render(src),
    };
    assert!(msg.contains("import char;"), "{msg}");

    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn bad() -> Nat { \"hi\" }\n";
    let msg = match e.elab_module_source("probe", src) {
        Ok(()) => panic!("accepted a string literal with no `string` module"),
        Err(error) => error.render(src),
    };
    assert!(msg.contains("import string;"), "{msg}");
}

/// A literal's generated call names what the module declaring its type can
/// see, not what the client imports: `char::ofNat`'s witness is
/// `bool::decide_yes(refl)` and a string's characters are `char` literals, so
/// a client that imports only `string` (or `char`) still builds them
/// (issues/literal-needs-module-names-wrong-module.md). Each position the
/// literal elaborates in, and a wrong literal refused for its value, not for
/// an import.
#[test]
fn a_literal_needs_only_its_own_types_module() {
    let only = |imports: &str, body: &str| -> Result<(), String> {
        let src = format!("{imports}{body}");
        let mut e = library();
        e.elab_module_source("probe", &src).map_err(|error| error.render(&src))
    };
    let char_body = r#"
fn plain() -> Char { 'x' }
fn inferred() -> Nat { let c = 'x'; c.toNat() }
fn in_a_list() -> List<Char> { ['a', 'b'] }
"#;
    let string_body = r#"
fn hello() -> String { "hi" }
fn inferred() -> Nat { let s = "hi"; s.len() }
fn empty() -> String { "" }
"#;
    for (imports, body) in [
        ("import nat;\nimport list;\nimport char;\n", char_body),
        ("import nat;\nimport char;\nimport string;\n", string_body),
        ("import nat;\nimport string;\n", string_body),
    ] {
        if let Err(msg) = only(imports, body) {
            panic!("refused with {imports:?}:\n{msg}");
        }
    }
    let mut e = library();
    support::assert_refused(
        &mut e,
        "probe",
        "import nat;\nimport string;\ntheorem wrong(): \"hi\" = \"ho\" { refl }\n",
        support::Refusal::Kernel,
    );
}

#[test]
fn an_inference_position_literal_names_its_own_spec_type() {
    check(
        r#"
fn inferred_char() -> Char { let c = 'x'; c }
fn inferred_string() -> String { let s = "hi"; s }
fn inferred_char_field() -> Nat { let c = 'x'; c.toNat() }
fn inferred_string_field() -> Nat { let s = "hi"; s.len() }
theorem inferred_char_value(): inferred_char().toNat() = 120 { refl }
theorem inferred_string_value(): inferred_string_field() = 2 {}
"#,
    );
    // Inference gives `Char`/`String` and not the user carrier: an annotated
    // binding at the carrier is a *checking* position and still works, but the
    // unannotated one does not silently become a `Tag`.
    let msg = refused(
        r#"
inductive Tag { Mk(c: Char) }
instance CharLiteral<Tag> { ofChar := Mk }
fn inferred() -> Tag { let c = 'x'; c }
"#,
    );
    assert!(msg.contains("Char") && msg.contains("Tag"), "{msg}");
}

#[test]
fn decide_answers_a_list_equation_at_any_decidable_element_type() {
    // `instance<A: DecEq>(xs, ys: List<A>) Decide<xs = ys>`: `A` is in no
    // written class argument, only in the elaborated equation's endpoint type
    // (issues/instance-binder-occurrence-through-binder-types.md). The goal's
    // endpoint type is inferred from constructor values, so it arrives as the
    // inline lowering and the instance's `List<A>` as the declaration's
    // reference; resolution meets them through the re-spelling. `Nat` (the
    // one instance there was before), `Char`, a nested list, and a refuted
    // equation.
    check(
        r#"
theorem nats(): Cons(1, Cons(2, Nil)) = Cons(1, Cons(2, Nil)) { decide }
theorem chars(): Cons('a', Cons('b', Nil)) = Cons('a', Cons('b', Nil)) { decide }
theorem nested(): Cons(Cons(1, Nil), Nil) = Cons(Cons(1, Nil), Nil) { decide }
theorem differ(): ¬(Cons('a', Nil) = Cons('b', Nil)) { decide }
"#,
    );
}
