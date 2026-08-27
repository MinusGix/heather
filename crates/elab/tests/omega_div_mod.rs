//! End-to-end acceptance for Omega's certified division/modulus frontend.
//!
//! This is a separate target from `omega.rs`: both targets elaborate the full
//! arithmetic library, and keeping independent process budgets prevents the
//! solver's core acceptance matrix from exhausting the test harness CPU cap.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

fn elaborator() -> Elaborator {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    for (name, source) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("algebra", ALGEBRA),
        ("int", INT),
        ("omega", OMEGA),
    ] {
        elab.elab_module_source(name, source)
            .unwrap_or_else(|error| panic!("{name} did not check: {error}"));
    }
    elab
}

fn message(error: ElabError) -> String {
    match error {
        ElabError::Elab { msg, .. } => msg,
        other => other.to_string(),
    }
}

#[test]
fn reflects_literal_division_modulus_and_divisibility() {
    let source = r#"
import int;
import logic;
import nat;
import omega;

theorem quotient_too_large(x: Int,
    x_upper: x <= OfNat(8),
    quotient_lower: OfNat(3) <= int::div(x, OfNat(3))):
    False
{ omega }

theorem quotient_too_small(x: Int,
    x_lower: OfNat(8) <= x,
    quotient_upper: int::div(x, OfNat(3)) <= OfNat(1)):
    False
{ omega }

theorem remainder_nonnegative(x: Int):
    OfNat(0) <= int::mod(x, OfNat(3))
{ omega }

theorem remainder_bounded(x: Int): int::mod(x, OfNat(3)) < OfNat(3)
{ omega }

theorem negative_quotient_too_large(x: Int,
    x_lower: OfNat(8) <= x,
    too_large: NegSucc(0) <= int::div(x, NegSucc(2))):
    False
{ omega }

theorem negative_remainder_nonnegative(x: Int):
    OfNat(0) <= int::mod(x, NegSucc(2))
{ omega }

theorem negative_remainder_bounded(x: Int):
    int::mod(x, NegSucc(2)) < OfNat(3)
{ omega }

theorem open_div_zero(x: Int): int::div(x, OfNat(0)) = OfNat(0)
{ omega }

theorem open_mod_zero(x: Int): int::mod(x, OfNat(0)) = x
{ omega }

theorem nat_quotient_too_large(n: Nat,
    n_upper: n <= 8,
    quotient_lower: 3 <= nat::div(n, 3)):
    False
{ omega }

theorem nat_remainder_bounded(n: Nat): nat::mod(n, 3) < 3
{ omega }

theorem open_nat_mod_zero(n: Nat): nat::mod(n, 0) = n
{ omega }

theorem nat_divides_six(): nat::Divides(3, 6)
{ omega }

theorem negated_int_divisibility(x: Int,
    value: x = OfNat(6),
    not_divisible: ¬int::Divides(OfNat(3), x)):
    False
{ omega }
"#;

    let mut elab = elaborator();
    elab.elab_module_source("divmod", source)
        .unwrap_or_else(|error| panic!("division/modulus did not check: {}", message(error)));
    let reports = elab
        .take_omega_reports()
        .into_iter()
        .filter(|report| report.atoms > 0)
        .collect::<Vec<_>>();
    assert!(reports.len() >= 11);
    let [large, small, nonnegative, bounded, ..] = reports.as_slice() else {
        unreachable!()
    };
    assert_eq!(large.atoms, 2);
    assert_eq!(large.assumptions, 4);
    assert!(large.used_lemmas.contains(&"omega::div_lower_nonzero"));
    assert_eq!(small.atoms, 2);
    assert_eq!(small.assumptions, 4);
    assert!(small.used_lemmas.contains(&"omega::div_upper_nonzero"));
    for report in [nonnegative, bounded] {
        assert_eq!(report.atoms, 2, "{report:?}");
        assert!(report.used_lemmas.contains(&"omega::normalize_mod"));
    }
    assert!(
        nonnegative
            .used_lemmas
            .contains(&"omega::div_lower_nonzero")
    );
    assert!(bounded.used_lemmas.contains(&"omega::div_upper_nonzero"));
    for lemma in [
        "omega::normalize_div_zero",
        "omega::normalize_mod_zero",
        "omega::nat_div_lower",
        "omega::nat_div_upper",
        "omega::normalize_nat_mod",
    ] {
        assert!(
            reports
                .iter()
                .any(|report| report.used_lemmas.contains(&lemma)),
            "missing {lemma}: {reports:#?}"
        );
    }

    let remainder_mutation = r#"
import int;
import logic;
import omega;

theorem false_remainder_bound(x: Int,
    value: x = OfNat(2)):
    int::mod(x, OfNat(3)) < OfNat(2)
{ omega }
"#;
    let error = elab
        .elab_module_source("remainder_mutation", remainder_mutation)
        .expect_err("the false remainder mutation must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));

    let divisibility_mutation = r#"
import int;
import logic;
import omega;

theorem five_is_not_divisible_by_three():
    int::Divides(OfNat(3), OfNat(5))
{ omega }
"#;
    let error = elab
        .elab_module_source("divisibility_mutation", divisibility_mutation)
        .expect_err("false divisibility must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));
}
