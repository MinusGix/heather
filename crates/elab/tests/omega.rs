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
import nat;
import bool;
import list;
import logic;
import omega;

fn atoms(x, y: Int) → List<Int> { Cons(x, Cons(y, Nil)) }
"#;

#[test]
fn dot_and_affine_fourier_motzkin_certificates_reach_the_kernel_gate() {
    let source = format!(
        r#"{PREFIX}
theorem eliminated(x, y: Int,
    lower: OfNat(3) <= omega::dot(Cons(OfNat(3), Cons(OfNat(1), Nil)), atoms(x, y)),
    upper: omega::dot(Cons(OfNat(2), Cons(OfNat(1), Nil)), atoms(x, y)) <= OfNat(2),
    final_upper: omega::dot(Cons(OfNat(1), Cons(OfNat(0), Nil)), atoms(x, y)) <= OfNat(0)):
    False
{{ omega }}

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
        .unwrap_or_else(|error| panic!("Omega certificate did not check: {}", message(error)));
}

#[test]
fn exposes_a_structured_omega_audit_report() {
    let source = format!(
        r#"{PREFIX}
theorem audited(x, y: Int,
    lower: OfNat(3) <= x * OfNat(3) + y,
    upper: x * OfNat(2) + y <= OfNat(2),
    final_upper: x <= OfNat(0)):
    False
{{ omega }}
"#
    );
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("audited Omega did not check: {}", message(error)));
    let reports = elab.take_omega_reports();
    let report = reports.last().expect("one solver report");
    assert_eq!(report.atoms, 2);
    assert_eq!(report.assumptions, 3);
    assert!(report.reachable_derivations >= 3);
    assert_eq!(
        report.discarded_derivations,
        report.total_derivations - report.reachable_derivations
    );
    assert!(report.residual.is_empty());
    assert!(report.stats.fourier_motzkin_eliminations >= 1);
    assert!(report.used_lemmas.contains(&"omega::lower_upper_combo"));
}

#[test]
fn shares_nonlinear_atoms_and_normalizes_integer_negation() {
    let source = format!(
        r#"{PREFIX}
theorem opaque_nonlinear(x: Int,
    lower: OfNat(1) <= x * x,
    upper: x * x <= OfNat(0)):
    False
{{ omega }}

theorem negated_difference(x, y: Int,
    upper: int::sub(x, y) <= OfNat(0),
    lower: OfNat(1) <= x + int::neg(y)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| {
            panic!(
                "nonlinear sharing/negation did not check: {}",
                message(error)
            )
        });
}

#[test]
fn proves_and_refuses_direct_integer_order_goals() {
    let source = format!(
        r#"{PREFIX}
theorem direct_goal(x, y: Int, h: x + OfNat(1) <= y): x <= y {{ omega }}

theorem direct_strict_goal(x, y: Int, h: x + OfNat(1) < y): x < y {{ omega }}
"#
    );
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("direct Omega goals did not check: {}", message(error)));

    let unprovable = format!(
        r#"{PREFIX}
theorem unprovable_goal(x, y: Int): x <= y {{ omega }}
"#
    );
    let error = elab
        .elab_module_source("unprovable", &unprovable)
        .expect_err("an unconstrained order goal must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));
}

#[test]
fn reflects_exact_equalities_in_both_orientations() {
    let source = format!(
        r#"{PREFIX}
theorem exact_interval(x, y: Int, eq: x = y, bad: x + OfNat(1) <= y): False
{{ omega }}

theorem reversed_exact(x: Int, eq: OfNat(1) = x, bad: x <= OfNat(0)): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("exact equalities did not check: {}", message(error)));
}

#[test]
fn reconstructs_nonprimitive_rows_with_gcd_rounding() {
    let source = format!(
        r#"{PREFIX}
theorem nonprimitive(x: Int,
    lower: OfNat(3) <= OfNat(2) * x,
    upper: OfNat(2) * x <= OfNat(2)):
    False
{{ omega }}
"#
    );
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("nonprimitive row did not check: {}", message(error)));
    let reports = elab.take_omega_reports();
    let report = reports.last().expect("Omega report");
    assert!(report.stats.gcd_divisions >= 1);
    assert!(report.used_lemmas.contains(&"omega::divide_lower"));
    assert!(report.used_lemmas.contains(&"omega::divide_upper"));
}

#[test]
fn reconstructs_a_balanced_hard_equality() {
    let source = format!(
        r#"{PREFIX}
theorem hard_equality(x, y: Int,
    equation: OfNat(2) * x + OfNat(3) * y = NegSucc(0),
    x_nonnegative: OfNat(0) <= x,
    y_nonnegative: OfNat(0) <= y):
    False
{{ omega }}
"#
    );
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("hard equality did not check: {}", message(error)));
    let reports = elab.take_omega_reports();
    let report = reports.last().expect("Omega report");
    assert_eq!(
        report.atoms, 2,
        "search-only variables stay out of reflection"
    );
    assert_eq!(report.stats.hard_equality_splits, 1);
    assert_eq!(report.stats.fresh_variables, 1);
    assert!(report.stats.equality_eliminations >= 1);
    assert!(report.used_lemmas.contains(&"omega::exact_combo"));

    let mutation = format!(
        r#"{PREFIX}
theorem satisfiable_hard(x, y: Int,
    equation: OfNat(2) * x + OfNat(3) * y = OfNat(1)):
    False
{{ omega }}
"#
    );
    let error = elab
        .elab_module_source("mutation", &mutation)
        .expect_err("a satisfiable hard equality must not produce a certificate");
    assert!(message(error).contains("real shadow found no contradiction"));
}

#[test]
fn reflects_negated_integer_relations() {
    let source = format!(
        r#"{PREFIX}
theorem negated_relation(x, y: Int, negated: ¬(x <= y), bad: x <= y): False
{{ omega }}

theorem negated_strict(x, y: Int, negated: ¬(x < y), bad: x < y): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("negated relations did not check: {}", message(error)));
}

#[test]
fn splits_integer_disequality_by_trichotomy() {
    let source = format!(
        r#"{PREFIX}
theorem disequality(x, y: Int,
    different: x ≠ y,
    forward: x <= y,
    backward: y <= x):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("disequality split did not check: {}", message(error)));
}

#[test]
fn expands_a_conjunctive_hypothesis() {
    let source = format!(
        r#"{PREFIX}
theorem conjunction(x: Int,
    bounds: (OfNat(1) <= x) ∧ (x <= OfNat(0))): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("conjunction did not check: {}", message(error)));
}

#[test]
fn splits_a_disjunctive_hypothesis() {
    let source = format!(
        r#"{PREFIX}
theorem disjunction(x: Int,
    cases: (x <= OfNat(0)) ∨ (OfNat(2) <= x),
    lower: OfNat(1) <= x,
    upper: x <= OfNat(1)):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("disjunction did not check: {}", message(error)));
}

#[test]
fn constructs_a_conjunctive_goal() {
    let source = format!(
        r#"{PREFIX}
theorem conjunction_goal(x, y: Int, equal: x = y): (x <= y) ∧ (y <= x)
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("conjunction goal did not check: {}", message(error)));
}

#[test]
fn embeds_nat_atoms_with_nonnegativity() {
    let source = format!(
        r#"{PREFIX}
theorem nat_nonnegative(n: Nat, bad: n < Zero): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("Nat nonnegativity did not check: {}", message(error)));
}

#[test]
fn embeds_affine_nat_constraints() {
    let source = format!(
        r#"{PREFIX}
theorem nat_nonprimitive(n: Nat,
    lower: 3 <= 2 * n,
    upper: 2 * n <= 2):
    False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("affine Nat did not check: {}", message(error)));
}

#[test]
fn proves_nat_order_goals() {
    let source = format!(
        r#"{PREFIX}
theorem nat_le_goal(n: Nat, lower: 3 <= n): 2 <= n
{{ omega }}

theorem nat_lt_goal(n: Nat, lower: 3 <= n): 2 < n
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("Nat order goals did not check: {}", message(error)));
}

#[test]
fn proves_a_nat_equality_goal() {
    let source = format!(
        r#"{PREFIX}
theorem nat_equality_goal(n, m: Nat, forward: n <= m, backward: m <= n): n = m
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("Nat equality goal did not check: {}", message(error)));
}

#[test]
fn proves_an_affine_nat_identity() {
    let source = format!(
        r#"{PREFIX}
theorem reassociate_and_permute(a, b, c, d: Nat):
    (a + b) + (c + d) = d + (b + (a + c))
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("affine Nat identity did not check: {}", message(error)));
}

#[test]
fn reflects_negated_nat_relations() {
    let source = format!(
        r#"{PREFIX}
theorem negated_nat_le(n, m: Nat, denied: ¬(n <= m), forward: n <= m): False
{{ omega }}

theorem negated_nat_lt(n, m: Nat, denied: ¬(n < m), forward: n < m): False
{{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("negated Nat relations did not check: {}", message(error)));
}

#[test]
fn split_all_applies_omega_to_every_boolean_goal() {
    let source = format!(
        r#"{PREFIX}
theorem every_boolean_branch_is_impossible(a, b: Bool, n: Nat,
    lower: 2 <= n, upper: n <= 1): False
{{
    split_all;
    all_goals {{ omega }}
}}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("split Omega goals did not check: {}", message(error)));
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
    let mut elab = elaborator();
    let error = elab
        .elab_module_source("probe", &source)
        .expect_err("a satisfiable system must not produce a certificate");
    let message = message(error);
    assert!(message.contains("real shadow found no contradiction"));
    assert!(message.contains(
        "OmegaResidualConstraint { coefficients: [1], lower: Some(-17), upper: Some(10) }"
    ));
    let reports = elab.take_omega_failure_reports();
    let [report] = reports.as_slice() else {
        panic!("expected one failed-search report, got {reports:#?}")
    };
    assert_eq!(report.atoms, 2);
    assert_eq!(report.assumptions, 3);
    assert_eq!(report.reachable_derivations, 0);
    assert_eq!(report.discarded_derivations, report.total_derivations);
    assert!(report.total_derivations >= report.assumptions);
    assert!(report.used_lemmas.is_empty());
    assert_eq!(
        report.residual,
        [heather_elab::OmegaResidualConstraint {
            coefficients: vec![1],
            lower: Some(-17),
            upper: Some(10),
        }]
    );
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
