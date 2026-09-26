//! Closed numeral production must be proportional to its representation, not
//! to the depth of the unary value it denotes.

use heather_elab::Elaborator;

#[test]
fn maximum_u64_literal_checks_under_a_small_memory_cap() {
    let source = r#"
fn predecessor(n: Nat) -> Nat {
    match n { Zero => Zero, Succ(k) => k }
}

fn maximum() -> Nat { 18446744073709551615 }

theorem maximum_literal_is_reflexive():
    18446744073709551615 = 18446744073709551615
{
    refl
}

"#;
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    if let Err(error) = elaborator.elab_source(source) {
        panic!("maximum literal did not check: {}", error.render(source));
    }
}

/// Numerals have no bound (docs/wide-numerals-design.md): past a machine word
/// a literal is still the number it spells — to evaluation, to conversion
/// against its successor spelling and a computed value, and in every radix —
/// and a neighbouring literal is still a different number.
#[test]
fn numerals_past_a_machine_word_are_the_numbers_they_spell() {
    let source = r#"
fn predecessor(n: Nat) -> Nat {
    match n { Zero => Zero, Succ(k) => k }
}

fn twice(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(twice(k))) } }

theorem one_past_the_word(): Succ(18446744073709551615) = 18446744073709551616 { refl }
theorem in_hex(): 0x1_0000_0000_0000_0000 = 18446744073709551616 { refl }
theorem its_predecessor(): predecessor(18446744073709551616) = 18446744073709551615 { refl }
theorem doubled(): twice(18446744073709551616) = 36893488147419103232 { refl }
theorem past_two_words(): predecessor(340282366920938463463374607431768211457) = 340282366920938463463374607431768211456 { refl }
"#;
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    if let Err(error) = elaborator.elab_source(source) {
        panic!("wide literals did not check: {}", error.render(source));
    }
    for (wrong, what) in [
        ("theorem w1(): 18446744073709551616 = 18446744073709551617 { refl }", "neighbouring wide literals"),
        ("theorem w2(): Succ(18446744073709551616) = 18446744073709551616 { refl }", "a wide literal and its successor"),
        ("theorem w3(): 340282366920938463463374607431768211456 = 18446744073709551616 { refl }", "literals a word apart"),
    ] {
        assert!(elaborator.elab_source(wrong).is_err(), "{what} were accepted as equal");
    }
}
