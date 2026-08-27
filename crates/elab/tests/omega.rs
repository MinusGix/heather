//! End-to-end acceptance for the kernel-certified Omega vertical slice,
//! including the low-level `omega::dot` boundary and ordinary affine syntax.

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

const PREFIX: &str = r#"
import int;
import list;
import logic;
import omega;

fn atoms(x, y: Int) → List<Int> { Cons(x, Cons(y, Nil)) }
"#;

#[test]
fn fourier_motzkin_certificate_reaches_the_kernel_gate() {
    let source = format!(
        r#"{PREFIX}
theorem eliminated(x, y: Int,
    lower: OfNat(3) <= omega::dot(Cons(OfNat(3), Cons(OfNat(1), Nil)), atoms(x, y)),
    upper: omega::dot(Cons(OfNat(2), Cons(OfNat(1), Nil)), atoms(x, y)) <= OfNat(2),
    final_upper: omega::dot(Cons(OfNat(1), Cons(OfNat(0), Nil)), atoms(x, y)) <= OfNat(0)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("Omega certificate did not check: {}", message(error)));
}

#[test]
fn ordinary_affine_syntax_reaches_the_kernel_gate() {
    let source = format!(
        r#"{PREFIX}
theorem eliminated_affine(x, y: Int,
    lower: OfNat(3) <= x * OfNat(3) + y,
    upper: x * OfNat(2) + y <= OfNat(2),
    final_upper: x <= OfNat(0)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| {
            panic!("affine Omega certificate did not check: {}", message(error))
        });
}

#[test]
fn repeated_nonlinear_subterms_are_shared_opaque_atoms() {
    let source = format!(
        r#"{PREFIX}
theorem opaque_nonlinear(x: Int,
    lower: OfNat(1) <= x * x,
    upper: x * x <= OfNat(0)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| {
            panic!("opaque atom certificate did not check: {}", message(error))
        });
}

#[test]
fn closes_an_integer_le_goal_via_its_strict_negation() {
    let source = format!(
        r#"{PREFIX}
theorem direct_goal(x, y: Int, h: x + OfNat(1) <= y): x <= y {{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("direct Omega goal did not check: {}", message(error)));
}

#[test]
fn refuses_an_unprovable_integer_le_goal() {
    let source = format!(
        r#"{PREFIX}
theorem unprovable_goal(x, y: Int): x <= y {{ omega }}
"#
    );
    let error = elaborator()
        .elab_module_source("probe", &source)
        .expect_err("an unconstrained order goal must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));
}

#[test]
fn closes_an_integer_lt_goal_via_its_negation() {
    let source = format!(
        r#"{PREFIX}
theorem direct_strict_goal(x, y: Int, h: x + OfNat(1) < y): x < y {{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("strict Omega goal did not check: {}", message(error)));
}

#[test]
fn normalizes_negation_and_subtraction() {
    let source = format!(
        r#"{PREFIX}
theorem negated_difference(x, y: Int,
    upper: int::sub(x, y) <= OfNat(0),
    lower: OfNat(1) <= x + int::neg(y)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("negation/subtraction did not check: {}", message(error)));
}

#[test]
fn reflects_integer_equality_as_an_exact_interval() {
    let source = format!(
        r#"{PREFIX}
theorem exact_interval(x, y: Int, eq: x = y, bad: x + OfNat(1) <= y): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("equality certificate did not check: {}", message(error)));
}

#[test]
fn positivizes_a_reversed_exact_equality() {
    let source = format!(
        r#"{PREFIX}
theorem reversed_exact(x: Int, eq: OfNat(1) = x, bad: x <= OfNat(0)): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("reversed equality did not check: {}", message(error)));
}

#[test]
fn reconstructs_easy_equality_elimination() {
    let source = format!(
        r#"{PREFIX}
theorem substituted_bound(x, y: Int,
    eq: y = x + OfNat(1),
    lower: OfNat(3) <= y,
    upper: x <= OfNat(1)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("equality elimination did not check: {}", message(error)));
}

#[test]
fn reconstructs_equality_elimination_into_an_upper_bound() {
    let source = format!(
        r#"{PREFIX}
theorem substituted_upper(x, y: Int,
    eq: y = x + OfNat(1),
    upper: y <= OfNat(2),
    lower: OfNat(2) <= x):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| {
            panic!(
                "upper equality elimination did not check: {}",
                message(error)
            )
        });
}

#[test]
fn closes_an_integer_equality_goal_by_antisymmetry() {
    let source = format!(
        r#"{PREFIX}
theorem direct_equality(x, y: Int, forward: x <= y, backward: y <= x): x = y
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("direct equality did not check: {}", message(error)));
}

#[test]
fn proves_an_affine_equality_consequence() {
    let source = format!(
        r#"{PREFIX}
theorem affine_equality_goal(x, y: Int, eq: y = x + OfNat(1)):
    int::sub(y, OfNat(1)) = x
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("affine equality goal did not check: {}", message(error)));
}

#[test]
fn satisfiable_mutation_is_refused_as_no_contradiction() {
    let source = format!(
        r#"{PREFIX}
theorem satisfiable(x, y: Int,
    lower: OfNat(3) <= omega::dot(Cons(OfNat(3), Cons(OfNat(1), Nil)), atoms(x, y)),
    upper: omega::dot(Cons(OfNat(2), Cons(OfNat(1), Nil)), atoms(x, y)) <= OfNat(20),
    final_upper: omega::dot(Cons(OfNat(1), Cons(OfNat(0), Nil)), atoms(x, y)) <= OfNat(10)):
    False
{{ omega }}
"#
    );
    let error = elaborator()
        .elab_module_source("probe", &source)
        .expect_err("a satisfiable system must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));
}

#[test]
fn a_written_omega_binding_wins_over_the_checking_form() {
    let source = format!(
        r#"{PREFIX}
theorem shadowed(omega: False): False {{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("the local binding should win: {}", message(error)));
}
