//! Scaling rail for Omega's literal division frontend.
//!
//! Heather's kernel `Nat` is unary, so this target intentionally carries a
//! substantial literal while checking that Omega's reflected problem and
//! proof search remain the same size as for a small divisor. It has an
//! independent process budget because checking the literal itself is real
//! unary work even though division is never evaluated.

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
fn large_literal_divisors_keep_a_constant_reflection_shape() {
    let source = r#"
import int;
import logic;
import nat;
import omega;

theorem small_int_divisor(x: Int,
    upper: x <= OfNat(15),
    positive_quotient: OfNat(1) <= int::div(x, OfNat(16))):
    False
{ omega }

theorem large_int_divisor(x: Int,
    upper: x <= OfNat(511),
    positive_quotient: OfNat(1) <= int::div(x, OfNat(512))):
    False
{ omega }

theorem small_nat_divisor(n: Nat,
    upper: n <= 15,
    positive_quotient: 1 <= nat::div(n, 16)):
    False
{ omega }

theorem large_nat_divisor(n: Nat,
    upper: n <= 511,
    positive_quotient: 1 <= nat::div(n, 512)):
    False
{ omega }
"#;

    let mut elab = elaborator();
    elab.elab_module_source("divmod_scaling", source)
        .unwrap_or_else(|error| panic!("large-literal rail did not check: {}", message(error)));
    let reports = elab
        .take_omega_reports()
        .into_iter()
        .filter(|report| report.atoms > 0)
        .collect::<Vec<_>>();
    let [small_int, large_int, small_nat, large_nat] = reports.as_slice() else {
        panic!("expected four scaling reports, got {reports:#?}")
    };
    for (small, large) in [(small_int, large_int), (small_nat, large_nat)] {
        assert_eq!(large.atoms, small.atoms);
        assert_eq!(large.assumptions, small.assumptions);
        assert_eq!(large.reachable_derivations, small.reachable_derivations);
        assert_eq!(large.stats, small.stats);
        assert_eq!(large.used_lemmas, small.used_lemmas);
    }

    let mutation = r#"
import int;
import logic;
import omega;

theorem false_large_remainder(x: Int,
    value: x = OfNat(511)):
    int::mod(x, OfNat(512)) < OfNat(511)
{ omega }
"#;
    let error = elab
        .elab_module_source("scaling_mutation", mutation)
        .expect_err("the false large-literal mutation must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));
}
