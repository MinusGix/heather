//! `lib/std/data/list.hthr`: the tests that need the checker. The module's
//! laws are its own theorems, which the whole-library gate checks
//! (`crates/cli/tests/library.rs`), and what the language can state about it
//! is `lib/_tests/std/data/list_tests.hthr`: the API computing at closed
//! arguments, `Mem` and its negative control, decidable equality at literals
//! and at open endpoints, and closed lengths by `refl` past the conversion
//! depth budget (docs/test-value-audit.md §3.4).
//!
//! What is left: how literals lower (structural), a wrong elimination
//! obligation, `decide` at a goal it cannot close, and an incompleteness pin
//! for a length at a neutral list.

use crate::support::{self, Refusal};
use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");

fn elaborated() -> Elaborator {
    support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
    ])
}

#[test]
fn its_literal_instance_uses_the_compact_protocol_lowering() {
    let mut e = elaborated();
    let before = e.psi().bindings.len();
    e.elab_module_source("list_literal_probe", "import list; fn xs() -> List<Nat> { [1, 2] }")
        .expect("literal checks");
    assert_eq!(e.psi().bindings.len(), before + 1);
}

#[test]
fn a_large_bracket_literal_avoids_constructor_elaboration_recursion() {
    let mut e = elaborated();
    let elements = vec!["0"; 1000].join(", ");
    let source = format!("import list; fn xs() -> List<Nat> {{ [{elements}] }}");
    e.elab_module_source("large_list_literal", &source)
        .expect("a flat literal does not consume one elaboration frame per element");
}

#[test]
fn a_deep_manual_list_spine_kernel_checks() {
    let mut e = elaborated();
    let source = format!(
        "import list; fn xs() -> List<Nat> {{ {}list::Nil{} }}",
        "list::Cons(0, ".repeat(1000), ")".repeat(1000),
    );
    e.elab_module_source("deep_manual_list", &source).expect("iterative constructors");
    let warnings = e.take_warnings();
    assert_eq!(warnings.iter().filter(|w| w.lint == heather_elab::Lint::ManualListConstruction).count(), 1);
}

/// The `cons` obligation is the property at `Cons(head, tail)`; `ih` proves
/// it at `tail`.
#[test]
fn a_wrong_list_obligation_is_rejected() {
    support::assert_refused(
        &mut elaborated(),
        "bad",
        "import list;
        fn bad_append_nil<A>() -> ListElim<A>(λ (xs: List<A>) => xs.append(Nil) = xs) {
            ListElim { nil: refl, cons: λ (head: A) (tail: List<A>) ih => ih }
        }",
        Refusal::Mismatch,
    );
}

/// `decide` has no closed decision at an open endpoint; the false closed
/// equation is `one_not_two` in the probes.
#[test]
fn decide_needs_closed_endpoints() {
    support::assert_refused(
        &mut elaborated(),
        "neutral_decide",
        "import list; import nat; import logic; import bool;
        theorem bad(xs: List<Nat>): xs = Cons(1, Nil) { decide }",
        Refusal::Says("whose decision here is not `Inl`"),
    );
}

/// A list literal in a refused goal is spelled as the literal: it elaborates
/// to its `Cons` spine, not to the protocol's fold over its vector, which
/// printed as the kernel encoding
/// (issues/decide-refusal-spells-string-literal-encoding.md). An open
/// element and an open tail spell too, the tail as the call it is.
#[test]
fn a_refused_goal_spells_its_list_literal() {
    for (goal, shown) in [
        ("xs = [1, 2]", "`Decide<xs = [1, 2]>`"),
        ("xs = []", "`Decide<xs = []>`"),
        ("xs = [x, 1]", "`Decide<xs = [x, 1]>`"),
        ("xs = Cons(1, xs)", "`Decide<xs = Cons(1, xs)>`"),
    ] {
        support::assert_refused(
            &mut elaborated(),
            "literal_decide",
            &format!("import list; import nat; import logic; import bool;
            theorem bad(x: Nat, xs: List<Nat>): {goal} {{ decide }}"),
            Refusal::Says(shown),
        );
    }
}

/// Incompleteness pin (§4.6): a length at a neutral list does not compute,
/// so the closed size fact is not `refl` there.
#[test]
fn a_neutral_length_is_not_a_size() {
    support::assert_refused(
        &mut elaborated(),
        "neutral_size",
        "import list; import nat;
        fn size16(lo: Nat, hi: Nat) -> Nat { lo + 256 * hi }
        theorem bad(xs: List<Nat>): 232 + xs.len() = size16(8, 79) { refl }",
        Refusal::Kernel,
    );
}
