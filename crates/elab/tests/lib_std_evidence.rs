//! `:= infer` at a proposition goal: computation, then `evidence theorem`
//! rules, with `lib/std/num/nat.hthr`'s positivity rules as the customer
//! (`issues/infer-proposition-evidence.md`,
//! `docs/library/positivity-evidence-design.md` §6 A): the refusals and their
//! diagnostics. What resolves is `lib/_tests/std/num/nat_evidence_tests.hthr`,
//! which the whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4).
//!
//! The prefix is a semantic image, so `nat`'s rules reach these modules the
//! way they reach any importer: replayed from the image's events.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const HEAD: &str = "import logic; import nat;
theorem uses(n: Nat, h: 0 < n := infer): 0 < n { h }
";

fn bad(src: &str, says: &str) -> String {
    support::assert_refused(&mut base(), "client", &format!("{HEAD}{src}"), Refusal::Says(says))
}

// -- computation ------------------------------------------------------------

#[test]
fn a_goal_that_computes_to_false_is_not() {
    // The goal is shown as this call instantiated it, not as the callee's
    // written `0 < n`, and not decoded to `False`.
    let e = bad("theorem zero(): 0 < 0 { uses(0) }\n", "no instance for `0 < 0`");
    assert!(e.contains("no-rule"), "{e}");
}

// -- rules ------------------------------------------------------------------

#[test]
fn a_rule_whose_premise_fails_is_not_taken() {
    let e = bad("theorem half(a, b: Nat, pa: 0 < a): 0 < a * b { uses(a * b) }\n", "no instance for `0 < a * b`");
    assert!(e.contains("candidate: nat::Nat::mul_pos"), "{e}");
}

// -- what a rule may be -----------------------------------------------------

#[test]
fn an_explicit_parameter_is_refused() {
    bad("evidence theorem r(n: Nat, p: 0 < n := infer): 0 < n + 0 { p }\n", "`n` is an explicit parameter");
}

#[test]
fn a_premise_no_smaller_than_the_conclusion_is_refused() {
    // Provable, and a search through it would grow the goal forever.
    bad(
        "evidence theorem grows({n: Nat}, p: 0 < Succ(Succ(n)) := infer): 0 < Succ(n) { trivial }\n",
        "not smaller than its conclusion",
    );
}

#[test]
fn a_conclusion_that_is_not_a_relation_is_refused() {
    bad("evidence theorem r({n: Nat}): n = n { refl }\n", "not a relation applied to arguments");
}

#[test]
fn evidence_marks_only_a_theorem() {
    bad("evidence fn f(n: Nat) -> Nat { n }\n", "parse error: `evidence` marks a `theorem`");
}
