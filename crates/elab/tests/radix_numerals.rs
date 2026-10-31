//! Radix numerals (`0x48`, `0b0100_1000`, `0o110`, with `_` separators) are
//! spellings of the ordinary numeral, so they must reach every carrier by
//! exactly the route decimal takes: `Nat` and `Fin` by the built-in rules,
//! `Int` (and any other `Numeral<A>`) through `ofNat`, and a bitvector
//! through the same explicit `ofNat(width, n)` a decimal byte goes through.
//! The malformed-input grammar is pinned in the lexer's own tests; the
//! controls here are the ones that need a carrier: computation, a checking
//! position, an equality that must *fail*, and the full-width literal.

use heather_elab::{ElabError, Elaborator};
use std::sync::Mutex;

use crate::support;

static ELAB_LOCK: Mutex<()> = Mutex::new(());

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec/bitvec.hthr");

fn run(extra: &str) -> Result<(), String> {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = Elaborator::with_prelude().expect("prelude");
    let mut prefix_error = None;
    let load = |e: &mut Elaborator| {
        for (name, src) in [
            ("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION),
            ("pair", PAIR), ("list", LIST), ("algebra", ALGEBRA), ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")), ("int", INT),
            ("bitvec", BITVEC),
        ] {
            if let Err(err) = e.elab_module_source(name, src) {
                prefix_error = Some(format!("{name}: {}", err.render(src)));
                break;
            }
        }
    };
    support::with_decl_cache(&mut e, load);
    if let Some(err) = prefix_error {
        return Err(err);
    }
    let src = format!("import bitvec;\nimport bool;\nimport logic;\nimport int;\nimport algebra;\n{extra}");
    if let Err(err) = e.elab_module_source("probe", &src) {
        return Err(match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        });
    }
    Ok(())
}

fn ok(src: &str) { run(src).unwrap_or_else(|e| panic!("expected this to check: {e}")); }

fn bad(src: &str) -> String {
    match run(src) {
        Ok(()) => panic!("expected this to be refused:\n{src}"),
        Err(e) => e,
    }
}

/// No library at all: the numeral is a `Nat` by the core rule, and a radix
/// spelling elaborates to the very same term as the decimal.
#[test]
fn radix_spellings_are_the_decimal_numeral_at_nat() {
    let source = r#"
theorem hex(): 0x48 = 72 { refl }
theorem bin(): 0b0100_1000 = 72 { refl }
theorem oct(): 0o110 = 72 { refl }
theorem sep(): 1_000_000 = 1000000 { refl }
theorem zero(): 0x0 = 0 { refl }
fn rex_w() -> Nat { 0x48 }
theorem rex_w_is_rex_w(): rex_w() = 72 { refl }
theorem full_width(): 0xFFFF_FFFF_FFFF_FFFF = 18446744073709551615 { refl }
"#;
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    if let Err(error) = elaborator.elab_source(source) {
        panic!("did not check: {}", error.render(source));
    }
}

/// The negative control: a radix numeral is not accepted *because* it is
/// exotic — a wrong value is refused exactly as a wrong decimal is.
#[test]
fn a_wrong_radix_value_is_refused() {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    assert!(elaborator.elab_source("theorem off(): 0x48 = 73 { refl }").is_err());
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    assert!(elaborator.elab_source("theorem off(): 0b1001000 = 0x49 { refl }").is_err());
}

/// A lexer refusal reaches the elaborator's diagnostic with the numeral's
/// own words, not a parser complaint about an unexpected identifier.
#[test]
fn malformed_radix_numerals_render_the_lexer_message() {
    for (source, needle) in [
        ("fn f() -> Nat { 0x }", "`0x` needs at least one hexadecimal digit"),
        ("fn f() -> Nat { 0b102 }", "invalid digit `2` in a binary numeral"),
        ("fn f() -> Nat { 0x1_ }", "must sit between two digits"),
    ] {
        let mut elaborator = Elaborator::with_prelude().expect("prelude");
        let error = elaborator.elab_source(source).expect_err(source);
        let rendered = error.render(source);
        assert!(rendered.contains(needle), "{source}\n{rendered}");
    }
}

/// Checking position at `Int` goes through `Numeral<Int>`'s `ofNat`, and at
/// `Fin` through the index rule — the same two routes decimal takes.
#[test]
fn radix_numerals_take_the_carrier_directed_route() {
    ok(r#"
fn opcode() -> Int { 0x89 }
theorem opcode_is_ofnat(): opcode() = OfNat(137) { refl }
theorem negated(): -0x89 = NegSucc(136) { refl }
theorem generic_int(): int::Int::add(0x1, 0b1) = OfNat(2) { refl }
fn slot() -> Fin(0x10) { 0xf }
fn dec_slot() -> Fin(16) { 15 }
theorem same_slot(): slot() = dec_slot() { refl }
"#);
    let msg = bad("fn slot() -> Fin(0x10) { 0x10 }");
    assert!(msg.contains("Fin") || msg.contains("index") || msg.contains("bound"), "{msg}");
}

/// x86 bytes and masks: REX.W, the MOV r/m64 opcode and a ModRM byte, at
/// `BitVec(8)` via the same `ofNat(8, ·)` a decimal byte uses, with the
/// register field masked out by a binary mask.
#[test]
fn x86_bytes_and_bit_masks_compute_at_bitvec() {
    ok(r#"
fn equal_byte(a, b: BitVec(8)) -> Bool {
    match @bitvec::BitVec::eq_dec(8, a, b) { Inl(_) => True, Inr(_) => False }
}
theorem rex_w(): equal_byte(@BitVec::ofNat(8, 0x48), @BitVec::ofNat(8, 72)) = True { refl }
theorem mov_rm64(): equal_byte(@BitVec::ofNat(8, 0x89), @BitVec::ofNat(8, 137)) = True { refl }
theorem modrm(): equal_byte(@BitVec::ofNat(8, 0b11_011_000), @BitVec::ofNat(8, 216)) = True { refl }
theorem modrm_reg_field():
    @bitvec::BitVec::toNat(8, @BitVec::band(8, @BitVec::ofNat(8, 0xd8), @BitVec::ofNat(8, 0b0011_1000))) = 0b0001_1000 { refl }
theorem modrm_mod_field():
    @bitvec::BitVec::toNat(8, @BitVec::band(8, @BitVec::ofNat(8, 0xd8), @BitVec::ofNat(8, 0b1100_0000))) = 0xc0 { refl }
theorem wraps_like_decimal(): @bitvec::BitVec::toNat(8, @BitVec::ofNat(8, 0x12c)) = 44 { refl }
theorem not_the_other_opcode(): equal_byte(@BitVec::ofNat(8, 0x89), @BitVec::ofNat(8, 0x8b)) = False { refl }
"#);
    bad("theorem wrong(): @bitvec::BitVec::toNat(8, @BitVec::band(8, @BitVec::ofNat(8, 0xd8), @BitVec::ofNat(8, 0b0011_1000))) = 0x19 { refl }");
}
