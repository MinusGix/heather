//! End-to-end acceptance for the kernel-certified Omega vertical slice,
//! including the low-level `omega::dot` boundary and ordinary affine syntax.

// Each member file (omega.rs, omega_logic.rs, omega_reconstruction.rs,
// omega_wide_constants.rs, omega_relevance.rs) runs one rail-sized suite
// below, in a process of its own; a binary that mounts fewer than all five
// leaves the others dormant.
#![allow(dead_code)]

use std::cell::OnceCell;
use std::sync::Mutex;

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
    let timings = stats::Dest::from_env();
    let report_phases = timings.is_some();
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
            // One module scope per module, so the dump's module rows say what
            // each of the prefix's modules cost
            // (`docs/instrumentation-design.md` §3).
            let _module = stats::scope(stats::ScopeKind::Module, name, "");
            elab.elab_module_source(name, source)
                .unwrap_or_else(|error| panic!("{name} did not check: {error}"));
        }
    });
    if let Some(dest) = &timings {
        let _ = stats::dump(dest, &elab.take_item_timings());
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
    // The same probe doubles as the instrumentation layer's omega case
    // (`docs/instrumentation-design.md` §5): reconstruction, search, render
    // and the certificate's own check are named columns attributed to the
    // declaration that asked for them, which is what the four environment
    // switches this replaced could never say.
    stats::enable();
    let _ = stats::take_rows();
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("Omega certificate did not check: {}", message(error)));
    let rows = stats::take_rows();
    stats::disable();
    let eliminated = rows
        .iter()
        .find(|row| row.item == "eliminated")
        .expect("a declaration row for the omega theorem");
    // `omega_render` and `omega_cutsat` belong to the cut-satisfaction route,
    // which this Fourier-Motzkin probe does not take.
    for timer in [
        stats::Timer::OmegaReflect,
        stats::Timer::OmegaSearch,
        stats::Timer::OmegaParse,
        stats::Timer::OmegaReconstruct,
        stats::Timer::OmegaCheck,
    ] {
        assert!(
            eliminated.timers[timer as usize] > 0,
            "{timer:?} must be attributed to `eliminated`: {:?}",
            eliminated.timers,
        );
    }
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
    // Phase attribution (issues/omega-per-goal-elaboration-cost.md): the
    // report says where its own wall time went. A `False` goal is a depth-0
    // invocation whose reconstruction searched and parsed something, and
    // whose certificate check is timed inclusively.
    let phases = report.phases;
    assert_eq!(phases.depth, 0);
    assert!(phases.source_len > 0);
    assert!(phases.parse_ns > 0);
    assert!(phases.reconstruct_ns >= phases.parse_ns + phases.omega_search_ns);
    assert!(phases.check_ns > 0);
    assert_eq!(phases.cutsat_search_ns, 0);
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
    upper: int::Int::sub(x, y) <= OfNat(0),
    lower: OfNat(1) <= x + int::Int::neg(y)):
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
    assert_eq!(reports[0].atom_labels, ["int::Int::mul(x, x)"]);
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

/// A certificate is parsed from generated text, so its expression spans
/// index that text and not the user's file. Its `Cons`/`Nil` spines used to
/// raise the manual-list lint against the probe module, where the borrowed
/// offsets landed on arbitrary bytes (a `→` in `omega.hthr`, which made the
/// CLI's snippet renderer panic). The only manual spine reported is the one
/// the user actually wrote, and every surviving span indexes the probe.
fn generated_certificate_lints_are_not_reported_against_user_source() {
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
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("equality elimination did not check: {}", message(error)));
    let warnings = elab.take_warnings();
    let manual: Vec<_> = warnings
        .iter()
        .filter(|w| w.lint == heather_elab::Lint::ManualListConstruction)
        .collect();
    let atoms = source.find("Cons(x, Cons(y, Nil))").expect("the probe's own spine");
    assert_eq!(
        manual.iter().map(|w| w.span.start).collect::<Vec<_>>(),
        vec![atoms],
        "only the user-written spine may be reported: {:?}",
        manual.iter().map(|w| (&w.msg, w.span)).collect::<Vec<_>>()
    );
    for w in &warnings {
        assert!(
            w.span.end <= source.len()
                && source.is_char_boundary(w.span.start)
                && source.is_char_boundary(w.span.end),
            "warning span {:?} does not index the probe source: {}",
            w.span,
            w.msg
        );
    }
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
    int::Int::sub(y, OfNat(1)) = x
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
    lower: OfNat(3) <= int::Int::sub(x, y * OfNat(2)),
    upper: int::Int::sub(x, y * OfNat(2)) <= OfNat(9)):
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

/// issues/omega-renders-member-by-base-name.md: a goal over `xs.len()`
/// reconstructs a certificate that names the atom, and the atom's global is a
/// **member** — whose base name (`len`) resolves to nothing outside `list`.
/// The renderer whose output is re-parsed therefore spells a global qualified
/// wherever the base name does not come back to it.
fn reconstructs_over_a_member_atom_spelled_qualified() {
    let source = format!(
        r#"{PREFIX}
theorem member_atom(xs: List<Int>, h: nat::Nat::Lt(0, xs.len())):
    nat::Nat::Lt(0, nat::Nat::add(xs.len(), 1)) {{ omega }}
theorem member_atom_dotted(xs: List<Int>, h: nat::Nat::Lt(0, xs.len())):
    nat::Nat::Lt(0, nat::Nat::add(xs.len(), 1)) {{ omega }}
theorem member_atoms_two(xs, ys: List<Int>, h: nat::Nat::Le(xs.len(), ys.len())):
    nat::Nat::Le(xs.len(), nat::Nat::add(ys.len(), 3)) {{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| {
            panic!("a certificate over a member atom did not check: {}", message(error))
        });
}

/// issues/omega-constants-beyond-u64.md: a numeral token is a `u64`, but a
/// word's arithmetic reaches 2^64 — as a bound, a carry, or a step of the
/// search nobody wrote. Each goal below needs a constant past the token
/// somewhere in its certificate, and a closed power is read as its value.
fn spells_constants_past_a_numeral_token() {
    let source = format!(
        r#"{PREFIX}
theorem intermediate(x: Nat, h: x < 1152921504606846976): x + 1 <= 18446744073709551615 {{ omega }}
theorem combined(x, y: Nat, hx: x < 18446744073709551615, hy: y < 18446744073709551615):
    x + y < 18446744073709551615 + 18446744073709551615 {{ omega }}
theorem split(v, r, h: Nat, value: v = 1099511627776 * r + h, low: h < 1099511627776,
    fits: v < 18446744073709551615): r < 16777216 {{ omega }}
theorem as_sum(x: Nat, h: x < 1152921504606846976): x < nat::Nat::add(18446744073709551615, 1) {{ omega }}
theorem wide_scale(v, r: Nat, value: v = 18446744073709551615 * r,
    fits: v < 18446744073709551615 + 18446744073709551615): r <= 1 {{ omega }}
theorem power(x: Nat, h: x < 1152921504606846976): x < nat::Nat::pow(2, 64) {{ omega }}
theorem carry(a, b, s: Nat, ha: a < nat::Nat::pow(2, 64), hb: b < nat::Nat::pow(2, 64),
    sum: a + b = s + nat::Nat::pow(2, 64)): nat::Nat::pow(2, 64) <= a + b {{ omega }}
theorem small_powers(x: Nat, h: x < 5): x < nat::Nat::pow(10, 18) + nat::Nat::pow(0, 0) {{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("a constant past the numeral token did not check: {}", message(error)));
}

/// The controls for the above, one module each: false at the word bound
/// itself, and a power past the evaluation budget stays an atom.
fn refuses_at_the_word_bound() {
    for goal in [
        "theorem edge(x: Nat, h: x < nat::Nat::pow(2, 64)): x + 1 < nat::Nat::pow(2, 64)",
        "theorem edge_literal(x: Nat, h: x <= 18446744073709551615): x + 1 <= 18446744073709551615",
        "theorem no_carry(a, b, s: Nat, ha: a < nat::Nat::pow(2, 64), hb: b < nat::Nat::pow(2, 64), sum: a + b = s): nat::Nat::pow(2, 64) <= a + b",
    ] {
        let source = format!("{PREFIX}\n{goal} {{ omega }}\n");
        let error = elaborator()
            .elab_module_source("probe", &source)
            .expect_err(goal);
        let message = message(error);
        assert!(message.contains("real shadow found no contradiction"), "{goal}: {message}");
    }
    let source = format!("{PREFIX}\ntheorem costly_power(x: Nat, h: x < 5): x < nat::Nat::pow(1099511627776, 3) {{ omega }}\n");
    let message = message(elaborator().elab_module_source("probe", &source).expect_err("costly power"));
    assert!(message.contains("atoms [x, nat::Nat::pow(1099511627776, 3)]"), "{message}");
}

/// issues/omega-relevant-facts-only.md: `omega` refutes a goal with the
/// facts over the goal's own atoms first, widening one hop at a time, and
/// only then with every fact. A fact that shares an atom with the goal is not
/// thereby needed: here `wide` mentions `x` and the goal needs `h` alone.
fn reflects_only_the_facts_near_the_goal() {
    let source = format!(
        r#"{PREFIX}
theorem near(x, y, z: Nat, h: x < 3, wide: y = x + z, far: z <= y + 7): x < 5 {{ omega }}
"#
    );
    let mut elab = elaborator();
    elab.elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("a goal near its facts did not check: {}", message(error)));
    let reports = elab.take_omega_reports();
    let labels: Vec<_> = reports.iter().filter(|report| report.atoms > 0).map(|report| report.atom_labels.clone()).collect();
    assert_eq!(labels, [["x"]], "{reports:#?}");
}

/// A goal whose facts reach it only through others widens until they do,
/// and a contradiction among facts away from the goal is still found by the
/// last attempt over every fact.
fn widens_and_falls_back() {
    let source = format!(
        r#"{PREFIX}
theorem chain(a, b, c, d, e: Nat, ab: a <= b, bc: b <= c, cd: c <= d, de: d < e): a < e {{ omega }}
theorem apart(x, y, z: Nat, bad: y + 1 <= y, h: x < 5): x < z {{ omega }}
"#
    );
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("widening or the fallback did not check: {}", message(error)));
}

/// A goal no attempt refutes reports one failure, from the attempt over
/// every fact, not one per layer.
fn a_stuck_goal_reports_one_failure() {
    let source = format!("{PREFIX}\ntheorem stuck(x, y, z: Nat, h: x < 5, other: y <= 3): x < z {{ omega }}\n");
    let mut elab = elaborator();
    let error = elab.elab_module_source("probe", &source).expect_err("x < z does not follow");
    assert!(message(error).contains("real shadow found no contradiction"));
    let failures = elab.take_omega_failure_reports();
    let [failure] = failures.as_slice() else {
        panic!("expected one failed-search report, got {failures:#?}")
    };
    assert_eq!(failure.atom_labels, ["x", "y", "z"]);
}

pub fn omega_relevance_suite() {
    reflects_only_the_facts_near_the_goal();
    widens_and_falls_back();
    a_stuck_goal_reports_one_failure();
}

pub fn omega_wide_constants_suite() {
    spells_constants_past_a_numeral_token();
    refuses_at_the_word_bound();
}

pub fn omega_reconstruction_suite() {
    reconstructs_over_a_member_atom_spelled_qualified();
    reflects_negated_nat_relations();
    split_all_applies_omega_to_every_boolean_goal();
    reconstructs_easy_equality_elimination();
    generated_certificate_lints_are_not_reported_against_user_source();
    reconstructs_equality_elimination_into_an_upper_bound();
    closes_an_integer_equality_goal_by_antisymmetry();
    proves_an_affine_equality_consequence();
    satisfiable_mutation_is_refused_as_no_contradiction();
    stuck_diagnostics_use_source_level_atom_names();
    a_written_omega_binding_wins_over_the_checking_form();
}
