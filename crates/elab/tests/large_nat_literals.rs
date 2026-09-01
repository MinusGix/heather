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
