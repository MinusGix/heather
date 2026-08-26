//! Acceptance for the first certifying arithmetic fragment. Every positive
//! reaches the ordinary declaration kernel gate; `arith` contributes only a
//! generated proof expression.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");

fn loaded() -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().map_err(|e| e.to_string())?;
    for (name, src) in [("logic", LOGIC), ("bool", BOOL), ("nat", NAT)] {
        e.elab_module_source(name, src)
            .map_err(|error| format!("{name}: {}", error.render(src)))?;
    }
    Ok(e)
}

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = loaded()?;
    let src = format!("import logic;\nimport bool;\nimport nat;\n{extra}");
    e.elab_module_source("probe", &src).map_err(|error| match error {
        ElabError::Elab { msg, .. } => msg,
        other => other.to_string(),
    })?;
    Ok(e)
}

fn ok(extra: &str) {
    run(extra).unwrap_or_else(|e| panic!("expected arithmetic certificate to check: {e}"));
}

fn bad(extra: &str) -> String {
    match run(extra) {
        Err(e) => e,
        Ok(_) => panic!("expected arithmetic reconstruction to refuse:\n{extra}"),
    }
}

#[test]
fn additive_associativity_and_permutation_are_certified() {
    ok(r#"
theorem reassociate_and_permute(a, b, c, d: Nat):
    (a + b) + (c + d) = d + (b + (a + c))
{ arith }
"#);
}

#[test]
fn carry_sum_shape_is_certified_without_reducing_opaque_atoms() {
    let e = run(r#"
theorem carry_sum_shape(x, y, z, a, b: Nat):
    (x + twice(a)) + (y + twice(b)) + z =
    twice(a + b) + ((x + y) + z)
{ arith }

theorem opaque_power(n, x: Nat):
    twice(pow(2, n)) + x = x + (pow(2, n) + pow(2, n))
{ arith }
"#).unwrap_or_else(|error| panic!("expected arithmetic certificates to check: {error}"));
    let reports = e.take_arith_reports();
    assert_eq!(reports.len(), 2);
    assert_eq!(
        reports[0].used_lemmas,
        ["nat::add_assoc", "nat::cong_nat", "nat::twice_add", "nat::add_comm"]
    );
    assert_eq!((reports[0].atoms, reports[0].adjacent_swaps), (5, 3));
    assert!(!reports[0].used_lemmas.contains(&"nat::twice_add_self"));
    assert!(reports[1].used_lemmas.contains(&"nat::twice_add_self"));
}

#[test]
fn unequal_coefficients_are_refused_with_both_normal_forms() {
    let msg = bad(r#"
theorem mutated(a: Nat): twice(a) = a { arith }
"#);
    assert!(msg.contains("UnequalNormalForms"), "{msg}");
    assert!(msg.contains("normalized lhs:"), "{msg}");
    assert!(msg.contains("normalized rhs:"), "{msg}");
    assert!(msg.contains("different opaque atoms or coefficients"), "{msg}");
}

#[test]
fn unsupported_goals_report_the_fragment_boundary() {
    let msg = bad(r#"
theorem order_is_not_in_the_first_fragment(n: Nat): n <= n { arith }
"#);
    assert!(msg.contains("UnsupportedGoal"), "{msg}");
    assert!(msg.contains("solves only equality goals"), "{msg}");
}

#[test]
fn written_arith_bindings_and_declarations_win_over_the_checking_form() {
    ok(r#"
theorem shadowed(n: Nat, arith: n = n): n = n { arith }
theorem arith(n: Nat): n = n { refl }
theorem global_shadowed(n: Nat): n = n { arith(n) }
"#);
}

#[test]
fn three_boolean_inputs_are_split_and_structural_order_lemmas_close_carry() {
    let e = run(r#"
fn bit_value(b: Bool) -> Nat { match b { False => 0, True => 1 } }
fn majority(a, b, carry: Bool) -> Bool {
    (a && b) || ((a && carry) || (b && carry))
}
fn weight(a, b, carry: Bool) -> Nat {
    (bit_value(a) + bit_value(b)) + bit_value(carry)
}

theorem majority_commutes(a, b, carry: Bool):
    majority(a, b, carry) = majority(b, a, carry)
{ arith }

theorem carry_threshold(a, b, carry: Bool, power, tail_sum: Nat):
    (twice(power) <= twice(tail_sum) + weight(a, b, carry)) ↔
    (power <= tail_sum + bit_value(majority(a, b, carry)))
{ arith }
"#).unwrap_or_else(|error| panic!("expected Boolean arithmetic certificates: {error}"));
    let reports = e.take_arith_reports();
    assert_eq!(reports.len(), 2);
    assert_eq!((reports[0].boolean_splits, reports[0].branches), (3, 8));
    assert!(reports[0].used_lemmas.is_empty());
    assert_eq!((reports[1].boolean_splits, reports[1].branches), (3, 8));
    assert_eq!(
        reports[1].used_lemmas,
        ["nat::twice_le_twice_iff", "nat::twice_le_succ_twice_iff"]
    );
}

#[test]
fn boolean_mutations_and_oversized_split_contexts_are_refused() {
    let mutation = bad(r#"
fn majority(a, b, carry: Bool) -> Bool {
    (a && b) || ((a && carry) || (b && carry))
}
theorem mutated(a, b, carry: Bool): majority(a, b, carry) = (a && b) { arith }
"#);
    assert!(mutation.contains("exhausted its Boolean leaf candidates"), "{mutation}");

    let bounded = bad(r#"
fn majority(a, b, carry: Bool) -> Bool {
    (a && b) || ((a && carry) || (b && carry))
}
theorem four_inputs(a, b, carry, unrelated: Bool):
    majority(a, b, carry) = majority(b, a, carry)
{ arith }
"#);
    assert!(bounded.contains("bounded at 3 inputs"), "{bounded}");
}

#[test]
fn conversion_precedes_the_boolean_split_bound() {
    let e = run(r#"
theorem four_irrelevant_booleans(a, b, c, d: Bool): a = a { arith }
"#).expect("conversion should not inspect unrelated Boolean locals");
    let reports = e.take_arith_reports();
    assert_eq!(reports.len(), 1);
    assert_eq!((reports[0].boolean_splits, reports[0].branches), (0, 1));
}

#[cfg(feature = "value-metrics")]
#[test]
fn carry_shaped_certificate_has_a_bounded_kernel_gate() {
    let mut e = loaded().expect("library prefix");
    e.enable_value_metrics();
    e.reset_value_metrics();
    let src = r#"
import logic;
import bool;
import nat;
theorem measured(x, y, z, a, b: Nat):
    (x + twice(a)) + (y + twice(b)) + z =
    twice(a + b) + ((x + y) + z)
{ arith }
"#;
    e.elab_module_source("measured", src).expect("generated certificate checks");
    let metrics = e.value_metrics().expect("collector enabled");

    let mut handwritten = loaded().expect("library prefix");
    handwritten.enable_value_metrics();
    handwritten.reset_value_metrics();
    let handwritten_src = r#"
import logic;
import bool;
import nat;
theorem measured(x, y, z, a, b: Nat):
    (x + twice(a)) + (y + twice(b)) + z =
    twice(a + b) + ((x + y) + z)
{
    calc {
        (x + twice(a)) + (y + twice(b)) + z
            = ((x + y) + (twice(a) + twice(b))) + z :=
                cong_nat(fun (q: Nat) => q + z,
                    nat::add_swap_middle(x, twice(a), y, twice(b))),
            = ((twice(a) + twice(b)) + (x + y)) + z :=
                cong_nat(fun (q: Nat) => q + z,
                    nat::add_comm(x + y, twice(a) + twice(b))),
            = (twice(a) + twice(b)) + ((x + y) + z) :=
                nat::add_assoc(twice(a) + twice(b), x + y, z),
            = twice(a + b) + ((x + y) + z) :=
                cong_nat(fun (q: Nat) => q + ((x + y) + z),
                    sym(nat::twice_add(a, b))),
    }
}

"#;
    handwritten
        .elab_module_source("handwritten", handwritten_src)
        .expect("handwritten comparison checks");
    let handwritten_metrics = handwritten.value_metrics().expect("collector enabled");
    assert!(metrics.term_cache_evictions == 0, "certificate should not churn: {metrics:?}");
    assert!(metrics.term_closures < 75_000, "unexpected certificate size: {metrics:?}");
    assert!(
        metrics.term_closures < handwritten_metrics.term_closures.saturating_mul(5),
        "generated certificate is disproportionate: generated {metrics:?}; handwritten {handwritten_metrics:?}"
    );
}

#[cfg(feature = "value-metrics")]
#[test]
fn boolean_carry_certificate_search_and_gate_are_bounded() {
    let helpers = r#"
import logic;
import bool;
import nat;
fn bit_value(b: Bool) -> Nat { match b { False => 0, True => 1 } }
fn majority(a, b, carry: Bool) -> Bool {
    (a && b) || ((a && carry) || (b && carry))
}
fn weight(a, b, carry: Bool) -> Nat {
    (bit_value(a) + bit_value(b)) + bit_value(carry)
}
"#;
    let statement = r#"
theorem measured(a, b, carry: Bool, power, tail_sum: Nat):
    (twice(power) <= twice(tail_sum) + weight(a, b, carry)) ↔
    (power <= tail_sum + bit_value(majority(a, b, carry)))
"#;

    let mut generated = loaded().expect("library prefix");
    generated.elab_module_source("generated", helpers).expect("helpers");
    generated.enable_value_metrics();
    generated.reset_value_metrics();
    generated
        .elab_module_source("generated", &format!("{statement}{{ arith }}"))
        .expect("generated Boolean carry certificate checks");
    let metrics = generated.value_metrics().expect("collector enabled");

    let mut handwritten = loaded().expect("library prefix");
    handwritten.elab_module_source("handwritten", helpers).expect("helpers");
    handwritten.enable_value_metrics();
    handwritten.reset_value_metrics();
    let proof = r#"
{
    match a {
        False => match b {
            False => match carry {
                False => twice_le_twice_iff(power, tail_sum),
                True => twice_le_succ_twice_iff(power, tail_sum),
            },
            True => match carry {
                False => twice_le_succ_twice_iff(power, tail_sum),
                True => twice_le_twice_iff(power, Succ(tail_sum)),
            },
        },
        True => match b {
            False => match carry {
                False => twice_le_succ_twice_iff(power, tail_sum),
                True => twice_le_twice_iff(power, Succ(tail_sum)),
            },
            True => match carry {
                False => twice_le_twice_iff(power, Succ(tail_sum)),
                True => twice_le_succ_twice_iff(power, Succ(tail_sum)),
            },
        },
    }
}
"#;
    handwritten
        .elab_module_source("handwritten", &format!("{statement}{proof}"))
        .expect("handwritten Boolean carry proof checks");
    let handwritten_metrics = handwritten.value_metrics().expect("collector enabled");
    assert_eq!(metrics.term_cache_evictions, 0, "search should not churn: {metrics:?}");
    assert!(metrics.term_closures < 50_000, "unexpected Boolean certificate cost: {metrics:?}");
    assert!(
        metrics.term_closures < handwritten_metrics.term_closures.saturating_mul(3),
        "Boolean reconstruction is disproportionate: generated {metrics:?}; handwritten {handwritten_metrics:?}"
    );
}
