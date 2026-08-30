//! End-to-end acceptance for the kernel-certified Omega vertical slice,
//! including the low-level `omega::dot` boundary and ordinary affine syntax.

// Each integration-test binary selects one rail-sized suite below, so the
// other two suites are intentionally dormant in that binary.
#![allow(dead_code)]

use std::cell::OnceCell;
use std::sync::Mutex;
use std::time::Instant;

use heather_elab::{ElabError, Elaborator, SemanticImage, stats};

use super::support;

const LOGIC: &str = include_str!("../../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../../lib/std/omega.hthr");

const OMEGA_MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("omega", OMEGA),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn load_image() -> SemanticImage {
    // Two libtest workers otherwise miss the cold declaration cache together
    // and each spends the process's CPU rail checking the same arithmetic
    // prefix. The first worker fills it; the second waits and replays it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let report_phases = std::env::var_os("HEATHER_OMEGA_PREFIX_PHASES").is_some();
    if !report_phases {
        let elab = support::semantic_test_base(OMEGA_MODULES);
        elab.take_omega_reports();
        return elab.semantic_image();
    }

    // Profiling asks what fresh prefix elaboration costs. Keep its historical
    // declaration-gated source path rather than timing semantic replay.
    let mut elab = Elaborator::with_prelude().expect("prelude");
    if report_phases {
        elab.enable_item_timings();
    }
    support::with_decl_cache(&mut elab, |elab| {
        for &(name, source) in OMEGA_MODULES {
            if report_phases {
                stats::reset_kernel_ns();
            }
            let started = Instant::now();
            elab.elab_module_source(name, source)
                .unwrap_or_else(|error| panic!("{name} did not check: {error}"));
            if report_phases {
                let total_ns = started.elapsed().as_nanos() as u64;
                let kernel_ns = stats::kernel_ns();
                eprintln!(
                    "omega prefix {name}: total={:.3}s kernel={:.3}s frontend={:.3}s",
                    total_ns as f64 / 1e9,
                    kernel_ns as f64 / 1e9,
                    total_ns.saturating_sub(kernel_ns) as f64 / 1e9,
                );
            }
        }
    });
    if report_phases {
        let mut timings = elab.take_item_timings();
        timings.sort_by(|left, right| right.total_ns.cmp(&left.total_ns));
        eprintln!("omega prefix slowest surface items:");
        for timing in timings.iter().take(20) {
            eprintln!(
                "  {}::{} total={:.3}s kernel={:.3}s frontend={:.3}s",
                timing.module,
                timing.item,
                timing.total_ns as f64 / 1e9,
                timing.kernel_ns as f64 / 1e9,
                timing.total_ns.saturating_sub(timing.kernel_ns) as f64 / 1e9,
            );
        }
    }
    elab.take_omega_reports();
    elab.semantic_image()
}

fn elaborator() -> Elaborator {
    // The semantic image is the explicit committed-state boundary: reports,
    // attempts, policy and the cache gate do not cross it. Stored module
    // images are kernel-checked before this process-local image is captured.
    // `omega_div_mod.rs` deliberately remains source-only so the full suite
    // still checks this exact library prefix front to back once.
    BASE.with(|base| base.get_or_init(load_image).elaborator())
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

fn cutsat_certificate_closes_the_minimal_real_shadow_integrality_gap() {
    let source = format!(
        r#"{PREFIX}
theorem seed_680(x, y: Int,
    first: NegSucc(1) <= x * OfNat(2) + y * OfNat(3),
    second: x * OfNat(2) + y * OfNat(5) <= OfNat(0),
    y_lower: OfNat(1) <= y): False
{{ omega }}
"#
    );
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("CutSat certificate did not check: {}", message(error)));
    let reports = elab.take_omega_reports();
    assert_eq!(
        reports
            .iter()
            .filter(|report| report.cutsat.is_some())
            .count(),
        1,
        "{reports:#?}"
    );
    let cutsat = reports
        .iter()
        .find_map(|report| report.cutsat.as_ref())
        .unwrap();
    assert!(cutsat.reachable_derivations > 0);
    assert!(cutsat.stats.derived_constraints > 0);
    assert!(
        reports
            .iter()
            .any(|report| { report.used_lemmas.contains(&"omega::cutsat_with_le") })
    );
}

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
    assert_eq!(report.atom_labels, ["x", "y"]);
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
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| {
            panic!(
                "nonlinear sharing/negation did not check: {}",
                message(error)
            )
        });
    let reports = elab.take_omega_reports();
    assert_eq!(reports.len(), 2);
    assert_eq!(reports[0].atoms, 1);
    assert_eq!(reports[0].atom_labels, ["int::mul(x, x)"]);
    assert_eq!(reports[1].atom_labels, ["x", "y"]);
}

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
    assert!(message.contains("atoms [atom[0], atom[1]]"));
    assert!(message.contains("residual [-17 <= atom[0] <= 10]"));
    let reports = elab.take_omega_failure_reports();
    let [report] = reports.as_slice() else {
        panic!("expected one failed-search report, got {reports:#?}")
    };
    assert_eq!(report.atoms, 2);
    assert_eq!(report.atom_labels, ["atom[0]", "atom[1]"]);
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
            rendered: "-17 <= atom[0] <= 10".into(),
        }]
    );
}

fn stuck_diagnostics_use_source_level_atom_names() {
    let source = format!(
        r#"{PREFIX}
theorem satisfiable_affine(x, y: Int,
    lower: OfNat(3) <= int::sub(x, y * OfNat(2)),
    upper: int::sub(x, y * OfNat(2)) <= OfNat(9)):
    False
{{ omega }}
"#
    );
    let mut elab = elaborator();
    let error = elab
        .elab_module_source("probe", &source)
        .expect_err("a satisfiable affine interval must remain stuck");
    let message = message(error);
    assert!(message.contains("atoms [x, y]"), "{message}");
    assert!(
        message.contains("residual [3 <= x - 2 * y <= 9]"),
        "{message}"
    );
    let reports = elab.take_omega_failure_reports();
    let [report] = reports.as_slice() else {
        panic!("expected one failed-search report, got {reports:#?}")
    };
    assert_eq!(report.atom_labels, ["x", "y"]);
    assert_eq!(report.residual[0].rendered, "3 <= x - 2 * y <= 9");
}

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

pub fn omega_core_suite() {
    dot_and_affine_fourier_motzkin_certificates_reach_the_kernel_gate();
    cutsat_certificate_closes_the_minimal_real_shadow_integrality_gap();
    exposes_a_structured_omega_audit_report();
    shares_nonlinear_atoms_and_normalizes_integer_negation();
    proves_and_refuses_direct_integer_order_goals();
    reflects_exact_equalities_in_both_orientations();
    reconstructs_nonprimitive_rows_with_gcd_rounding();
    reconstructs_a_balanced_hard_equality();
    reflects_negated_integer_relations();
}

pub fn omega_logic_suite() {
    splits_integer_disequality_by_trichotomy();
    expands_a_conjunctive_hypothesis();
    splits_a_disjunctive_hypothesis();
    constructs_a_conjunctive_goal();
    embeds_nat_atoms_with_nonnegativity();
    embeds_affine_nat_constraints();
    proves_nat_order_goals();
    proves_a_nat_equality_goal();
    proves_an_affine_nat_identity();
}

pub fn omega_reconstruction_suite() {
    reflects_negated_nat_relations();
    split_all_applies_omega_to_every_boolean_goal();
    reconstructs_easy_equality_elimination();
    reconstructs_equality_elimination_into_an_upper_bound();
    closes_an_integer_equality_goal_by_antisymmetry();
    proves_an_affine_equality_consequence();
    satisfiable_mutation_is_refused_as_no_contradiction();
    stuck_diagnostics_use_source_level_atom_names();
    a_written_omega_binding_wins_over_the_checking_form();
}
