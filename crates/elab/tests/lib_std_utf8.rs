//! `lib/std/utf8.hthr` — UTF-8 as the first *representation* of `String`, and
//! the `Utf8` byte-level spec type beside it (docs/string-char-design.md §5).
//!
//! The acceptance shape is `docs/testing-generated-terms.md`'s: the encoder is
//! exercised at a literal of every byte width, the decoder at closed byte
//! lists including each rejection Rust's `from_utf8` makes, and every law at a
//! literal **and** at a neutral string, with a negative control beside each.
//! The rejection cases are the point of the strict decoder: an overlong form,
//! a surrogate, a truncated sequence, a stray continuation byte and a lead
//! byte above the scalar range all have to come back `None`.

use heather_elab::{ElabError, Elaborator, SemanticImage};
use std::cell::OnceCell;
use std::sync::Mutex;

mod support;

static ELAB_LOCK: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

/// The first nine entries are `semantic_x86_warmup.rs`'s list in its order,
/// so this target reads the images that warmup wrote instead of elaborating
/// `bitvec` again per case.
const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec.hthr")),
    ("char", include_str!("../../../lib/std/char.hthr")),
    ("string", include_str!("../../../lib/std/string.hthr")),
    ("utf8", include_str!("../../../lib/std/utf8.hthr")),
];

const PREAMBLE: &str = concat!(
    "import logic;\nimport nat;\nimport option;\nimport pair;\n",
    "import list;\nimport bitvec;\nimport char;\nimport string;\nimport utf8;\n",
);

fn probe(body: &str) -> Result<(), String> {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    if body.is_empty() {
        // The ungated front-to-back check of the module itself, source only,
        // so the full suite checks this exact prefix against the real kernel.
        let mut e = Elaborator::with_prelude().expect("prelude");
        for &(name, src) in MODULES {
            if let Err(err) = e.elab_module_source(name, src) {
                return Err(format!("{name}: {}", err.render(src)));
            }
        }
        return Ok(());
    }
    let mut e = BASE.with(|base| {
        base.get_or_init(|| support::semantic_test_base(MODULES).semantic_image())
            .elaborator()
    });
    let src = format!("{PREAMBLE}{body}");
    match e.elab_module_source("probe", &src) {
        Ok(()) => Ok(()),
        Err(error) => Err(match error {
            ElabError::Elab { .. } => error.render(&src),
            other => format!("{other}"),
        }),
    }
}

fn check(body: &str) {
    if let Err(msg) = probe(body) {
        panic!("{msg}");
    }
}

/// The negative half of every generated-term test: the same shape, wrong.
fn refused(body: &str) -> String {
    match probe(body) {
        Ok(()) => panic!("accepted: {body}"),
        Err(msg) => msg,
    }
}

#[test]
fn the_utf8_module_checks() {
    check("");
}

#[test]
fn encoding_a_literal_writes_the_bytes_of_its_class() {
    check(
        r#"
// One byte per class boundary: ASCII, Latin-1, the BMP, and an astral plane.
theorem one_byte(): utf8::encode("a") = [bitvec::ofNat(8, 0x61)] { refl }
theorem two_bytes(): utf8::encode("\u{E9}")
    = [bitvec::ofNat(8, 0xC3), bitvec::ofNat(8, 0xA9)] { refl }
theorem three_bytes(): utf8::encode("\u{20AC}")
    = [bitvec::ofNat(8, 0xE2), bitvec::ofNat(8, 0x82), bitvec::ofNat(8, 0xAC)] { refl }
theorem four_bytes(): utf8::encode("\u{1F600}")
    = [bitvec::ofNat(8, 0xF0), bitvec::ofNat(8, 0x9F), bitvec::ofNat(8, 0x98),
       bitvec::ofNat(8, 0x80)] { refl }
// A mixed string is the concatenation of its characters' bytes.
theorem mixed(): utf8::encode("a\u{E9}")
    = [bitvec::ofNat(8, 0x61), bitvec::ofNat(8, 0xC3), bitvec::ofNat(8, 0xA9)] { refl }
theorem empty(): utf8::encode("") = Nil<BitVec(8)> { refl }
"#,
    );
    let msg = refused("theorem bad(): utf8::encode(\"a\") = [bitvec::ofNat(8, 0x62)] { refl }\n");
    assert!(msg.contains("NotConvertible"), "{msg}");
    // The class boundary is the encoder's own range test: `0x80` is two
    // bytes, not one.
    let msg = refused("theorem bad(): utf8::encode(\"\\u{80}\") = [bitvec::ofNat(8, 0x80)] { refl }\n");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn decoding_those_bytes_gives_the_string_back() {
    check(
        r#"
theorem one_byte(): utf8::decode([bitvec::ofNat(8, 0x61)]) = Some("a") { refl }
theorem two_bytes(): utf8::decode([bitvec::ofNat(8, 0xC3), bitvec::ofNat(8, 0xA9)])
    = Some("\u{E9}") { refl }
theorem three_bytes(): utf8::decode([bitvec::ofNat(8, 0xE2), bitvec::ofNat(8, 0x82),
    bitvec::ofNat(8, 0xAC)]) = Some("\u{20AC}") { refl }
theorem four_bytes(): utf8::decode([bitvec::ofNat(8, 0xF0), bitvec::ofNat(8, 0x9F),
    bitvec::ofNat(8, 0x98), bitvec::ofNat(8, 0x80)]) = Some("\u{1F600}") { refl }
theorem empty(): utf8::decode(Nil<BitVec(8)>) = Some("") { refl }
"#,
    );
    let msg = refused(
        "theorem bad(): utf8::decode([bitvec::ofNat(8, 0x61)]) = Some(\"b\") { refl }\n",
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn the_decoder_is_strict_at_every_rejection() {
    check(
        r#"
// An overlong two-byte form of `0x00`: the payload is below the class's
// least legal value.
theorem overlong(): utf8::decode([bitvec::ofNat(8, 0xC0), bitvec::ofNat(8, 0x80)]) = None { refl }
// A lone surrogate, `U+D800` spelled in three bytes: not a scalar value.
theorem surrogate(): utf8::decode([bitvec::ofNat(8, 0xED), bitvec::ofNat(8, 0xA0),
    bitvec::ofNat(8, 0x80)]) = None { refl }
// A three-byte sequence with only two bytes present.
theorem truncated(): utf8::decode([bitvec::ofNat(8, 0xE2), bitvec::ofNat(8, 0x82)]) = None { refl }
// A continuation byte where a lead byte belongs.
theorem stray_continuation(): utf8::decode([bitvec::ofNat(8, 0x80)]) = None { refl }
// `0xF5` starts a sequence above `0x10FFFF`.
theorem above_range(): utf8::decode([bitvec::ofNat(8, 0xF5), bitvec::ofNat(8, 0x80),
    bitvec::ofNat(8, 0x80), bitvec::ofNat(8, 0x80)]) = None { refl }
// A lead byte with no continuation marker after it.
theorem bad_continuation(): utf8::decode([bitvec::ofNat(8, 0xC3), bitvec::ofNat(8, 0x41)])
    = None { refl }
// `0xF8` is no lead byte at all.
theorem no_class(): utf8::decode([bitvec::ofNat(8, 0xF8)]) = None { refl }
// A rejection anywhere rejects the whole list, not just its tail.
theorem rejection_propagates(): utf8::decode([bitvec::ofNat(8, 0x61), bitvec::ofNat(8, 0x80)])
    = None { refl }
"#,
    );
    // The negative controls: a rejected list decodes to nothing at all, so no
    // string is its image.
    let msg = refused(
        "theorem bad(): utf8::decode([bitvec::ofNat(8, 0xC0), bitvec::ofNat(8, 0x80)]) = Some(\"\") { refl }\n",
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
    let msg = refused(
        "theorem bad(): utf8::decode([bitvec::ofNat(8, 0x80)]) = Some(\"\") { refl }\n",
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
    // And a valid list is not rejected: the strictness is not vacuous.
    let msg = refused("theorem bad(): utf8::decode([bitvec::ofNat(8, 0x61)]) = None { refl }\n");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn the_round_trip_holds_at_a_literal_and_at_a_neutral_string() {
    check(
        r#"
theorem literal(): utf8::decode(utf8::encode("h\u{E9}\u{20AC}\u{1F600}"))
    = Some("h\u{E9}\u{20AC}\u{1F600}") { utf8::decode_encode("h\u{E9}\u{20AC}\u{1F600}") }
// The literal's round trip also computes, with no lemma at all.
theorem literal_computes(): utf8::decode(utf8::encode("h\u{E9}")) = Some("h\u{E9}") { refl }
theorem neutral(s: String): utf8::decode(utf8::encode(s)) = Some(s) { utf8::decode_encode(s) }
theorem half_open(s: String): utf8::decode(utf8::encode("a" ++ s)) = Some("a" ++ s) {
    utf8::decode_encode("a" ++ s)
}
// One character at an OPEN code, which is the case a closed literal hides:
// the decoder's rejections are refuted by the character's own witness and by
// its class's range test, not by computation.
theorem one_char(c: Char, rest: List<BitVec(8)>):
    utf8::decode_char(utf8::encode_char(c) ++ rest) = Some(Pair(c, rest))
{ utf8::decode_char_encode_char(c, rest) }
"#,
    );
    // The negative control: the round trip is not `refl` at an open string,
    // so the lemma is doing the work.
    let msg = refused("theorem bad(s: String): utf8::decode(utf8::encode(s)) = Some(s) { refl }\n");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn encoding_is_injective_and_additive_at_both_kinds_of_argument() {
    check(
        r#"
theorem neutral_injective(s, t: String, p: utf8::encode(s) = utf8::encode(t)): s = t {
    utf8::encode_injective(s, t, p)
}
theorem literal_injective(t: String, p: utf8::encode("hi") = utf8::encode(t)): "hi" = t {
    utf8::encode_injective("hi", t, p)
}
theorem neutral_append(s, t: String):
    utf8::encode(s ++ t) = utf8::encode(s) ++ utf8::encode(t) { utf8::encode_append(s, t) }
theorem half_open_append(s: String):
    utf8::encode(s ++ "a") = utf8::encode(s) ++ [bitvec::ofNat(8, 0x61)] {
    utf8::encode_append(s, "a")
}
theorem literal_append(): utf8::encode("a" ++ "\u{E9}")
    = utf8::encode("a") ++ utf8::encode("\u{E9}") { refl }
"#,
    );
    // The negative control: injectivity needs a real premise; two arbitrary
    // strings have no common encoding.
    let msg = refused("theorem bad(s, t: String): s = t { utf8::encode_injective(s, t, refl) }\n");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn the_utf8_record_carries_its_bytes_and_reads_back_the_string() {
    check(
        r#"
theorem neutral(s: String): utf8::ofString(s).toString() = s { utf8::toString_ofString(s) }
theorem literal(): utf8::ofString("h\u{E9}").toString() = "h\u{E9}" {
    utf8::toString_ofString("h\u{E9}")
}
// The byte length and the character length are different measurements, which
// is why this type exists at all.
theorem byte_length(): utf8::ofString("h\u{E9}\u{20AC}").len() = 6 {}
theorem char_length(): "h\u{E9}\u{20AC}".len() = 3 {}
theorem ascii_lengths_agree(): utf8::ofString("hi").len() = "hi".len() { refl }
// The witness is the decision, so an encoded string is valid by construction
// at an open argument too.
theorem valid_of_encode(s: String): utf8::utf8_valid(utf8::encode(s)) { utf8::ofString(s).valid }
theorem bytes_of_ofString(s: String): utf8::ofString(s).bytes = utf8::encode(s) { refl }
"#,
    );
    let msg = refused("theorem bad(): utf8::ofString(\"h\\u{E9}\").len() = 2 {}\n");
    assert!(!msg.is_empty(), "a wrong byte length must be refused");
    // A byte list that does not decode has no witness, so no `Utf8` value.
    let msg = refused(
        "theorem bad(): utf8::utf8_valid([bitvec::ofNat(8, 0x80)]) { trivial }\n",
    );
    assert!(!msg.is_empty(), "an invalid byte list must have no witness");
}

/// The whole-list decoder is the per-sequence decoder pushed onto the tail,
/// by computation, at every width and at an open payload — the statement
/// `utf8::decode_step` makes per width. The three- and four-byte rows once
/// died in the kernel: the two sides' first shared δ-head is `bit7`, under
/// *different* matches (`class_of`'s against `cont_of`'s), and a failed meet
/// there used to normalize both sides through `nat::leb(0x800, code)` at a
/// stuck `code` — a 2048-deep closure chain no comparison can descend
/// (`issues/utf8-decode-conversion-blowup.md`). The two-byte row is the
/// control that was always green. The negative control is a wrong tail; a
/// wrong *class* is refused too, but by exhaustion rather than mismatch,
/// which is `issues/run-elimination-meet.md`.
#[test]
fn decoding_a_list_is_decoding_its_head_then_its_tail_by_computation() {
    check(
        r#"
theorem uf1(b: BitVec(7), t: List<BitVec(8)>):
        decode(Cons(ascii_byte(b), t)) = push_char(decode_seq(C1, ascii_byte(b), t), decode(t))
{ refl }
theorem uf2(q: BitVec(5), r: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead2_byte(q), Cons(cont_byte(r), t)))
        = push_char(decode_seq(C2, lead2_byte(q), Cons(cont_byte(r), t)), decode(t))
{ refl }
theorem uf3(q: BitVec(4), r, s: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t))))
        = push_char(decode_seq(C3, lead3_byte(q),
              Cons(cont_byte(r), Cons(cont_byte(s), t))), decode(t))
{ refl }
theorem uf4(q: BitVec(3), r, s, u: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead4_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), Cons(cont_byte(u), t)))))
        = push_char(decode_seq(C4, lead4_byte(q),
              Cons(cont_byte(r), Cons(cont_byte(s), Cons(cont_byte(u), t)))), decode(t))
{ refl }
// The one-character decoder is the same call.
theorem uf3c(q: BitVec(4), r, s: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t))))
        = push_char(decode_char(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t)))),
              decode(t))
{ refl }
// The library's statement, at an open width and code.
theorem step(w: Width, code: Nat, rest: List<BitVec(8)>):
        decode(encode_width(w, code) ++ rest)
            = push_char(decode_char(encode_width(w, code) ++ rest), decode(rest))
{ utf8::decode_step(w, code, rest) }
"#,
    );
    let msg = refused(
        r#"
theorem bad(q: BitVec(4), r, s, u: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t))))
        = push_char(decode_seq(C3, lead3_byte(q),
              Cons(cont_byte(r), Cons(cont_byte(s), t))), decode(Cons(cont_byte(u), t)))
{ refl }
"#,
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}
