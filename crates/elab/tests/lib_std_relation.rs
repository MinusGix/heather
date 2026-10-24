//! `lib/std/relation/relation.hthr` — finitary relational semantics and
//! refinement: the refusals that need the checker. What the language can
//! state is `lib/_tests/std/relation/relation_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4): properties composing at concrete and open
//! carriers, the relational algebra, deterministic and nondeterministic
//! customers, and the coverage model.

use crate::support::{self, Refusal};
use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const RELATION: &str = include_str!("../../../lib/std/relation/relation.hthr");
const RELATION_PROPS: &str = include_str!("../../../lib/std/relation/relation_props.hthr");

fn elaborated() -> Elaborator {
    support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("relation", RELATION),
        ("relation_props", RELATION_PROPS),
    ])
}

/// An instance of one property is not an instance of another, even where the
/// relation happens to have both: `Always` is symmetric by instance and
/// reflexive by computation, and only the instance counts.
#[test]
fn an_unrelated_property_is_not_reflexivity() {
    support::assert_refused(
        &mut elaborated(),
        "unrelated_property",
        "import relation; import relation_props;
        inductive Point { Pt }
        fn Always(x, y: Point) → Type { True }
        instance Symmetric<Point>(Always) { rel_sym := λ x y h => trivial }
        fn needs_reflexive<A: Reflexive(R)>(R: A → A → Type, x: A) → R(x, x) { A.rel_refl(x) }
        theorem bad(x: Point): Always(x, x) { needs_reflexive(Always, x) }",
        Refusal::Says("no instance for `Reflexive<A>(R)`"),
    );
}

/// `Unsupported` is coverage, not an outcome: an unsupported instruction is
/// never a fault.
#[test]
fn unsupported_is_not_a_semantic_outcome() {
    support::assert_refused(
        &mut elaborated(),
        "bad_coverage",
        "import relation;
        inductive ToyFault { DivisionByZero }
        fn unsupported_is_not_a_fault() → SemanticOutcome<Nat, ToyFault> { Unsupported }",
        Refusal::Says("`Unsupported` is a constructor of `Coverage`"),
    );
}
