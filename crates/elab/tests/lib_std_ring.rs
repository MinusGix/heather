//! The `ring` tactic (`lib/std/tactic/ring.hthr`,
//! `docs/ring-normalization-design.md`): its refusals. What it proves is
//! `lib/_tests/std/tactic/ring_tests.hthr`, which the whole-library gate
//! checks (`crates/cli/tests/library.rs`; docs/test-value-audit.md §5): the
//! identities at `Int` and `Nat`, the checking positions, `ring(h, …)` with
//! found multipliers, defined propositions, a fact handed to `omega`, and a
//! local named `ring`.
//!
//! What is left: a non-identity refused with its residual, a combination
//! that does not exist, a hypothesis that is not an equation or is at
//! another carrier, a goal that is not an equation at `Int` or `Nat`, a
//! missing import, and a wrong hypothesis the combination does not use,
//! which still faces the kernel.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("ring", include_str!("../../../lib/std/tactic/ring.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn refused(name: &str, src: &str, why: Refusal) {
    support::assert_refused(&mut base(), name, src, why);
}

const IMPORTS: &str = "import logic; import nat; import int; import ring;\n";

#[test]
fn an_unused_hypothesis_still_faces_the_kernel() {
    let record = "record Q { a: Int, h: a = OfNat(3) }\n";
    refused(
        "ring_unused_wrong",
        &format!("{IMPORTS}{record} theorem t(a, b: Int): a * b = b * a {{ ring(Q(OfNat(2), refl).h) }}"),
        Refusal::Kernel,
    );
}

#[test]
fn a_non_identity_is_refused_with_its_residual() {
    refused(
        "ring_not_identity",
        &format!("{IMPORTS} theorem bad(a, b: Int): (a + b) * (a + b) = a * a + b * b {{ ring }}"),
        Refusal::Says("differ by `2 * a * b`"),
    );
    refused(
        "ring_nat_not_identity",
        &format!("{IMPORTS} theorem bad(x: Nat): Succ(x) * x = x * x {{ ring }}"),
        Refusal::Says("differ by `x`"),
    );
}

#[test]
fn a_missing_combination_is_refused() {
    refused(
        "ring_no_combination",
        &format!("{IMPORTS} theorem bad(a, b: Int, h: a = b): a * a = b {{ ring(h) }}"),
        Refusal::Says("no combination"),
    );
    // Hypotheses are equations: a proof of something else is named.
    refused(
        "ring_hypothesis_not_equation",
        &format!("{IMPORTS} theorem bad(a, b: Int, h: a <= b): a = b {{ ring(h) }}"),
        Refusal::Says("`ring` combines equations; `h` is"),
    );
    refused(
        "ring_carrier_mismatch",
        &format!("{IMPORTS} theorem bad(a: Int, x, y: Nat, h: x = y): a = a {{ ring(h) }}"),
        Refusal::Says("is an equation at `Nat`"),
    );
}

#[test]
fn only_equations_at_int_or_nat() {
    refused(
        "ring_order_goal",
        &format!("{IMPORTS} theorem bad(a: Int): a <= a {{ ring }}"),
        Refusal::Says("`ring` proves an equation at `Int` or `Nat`"),
    );
    refused(
        "ring_bool_goal",
        &format!("import bool; {IMPORTS} theorem bad(b: Bool): b = b {{ ring }}"),
        Refusal::Says("`ring` proves an equation at `Int` or `Nat`"),
    );
}

#[test]
fn ring_needs_its_library() {
    refused(
        "ring_no_import",
        "import logic; import nat; import int; theorem bad(a: Int): a * a = a * a { ring }",
        Refusal::Says("add `import ring;`"),
    );
}
