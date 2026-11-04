//! `lib/std/num/int.hthr` (`issues/std-int-encoding.md`,
//! `issues/std-int-order-completion.md`): the one check the language cannot
//! state. Everything it can is a theorem: the API computing in every sign
//! quadrant, the operators and `Decide` instances resolving at `Int` beside
//! `nat` and `bool`, Euclidean division, and the `¬` theorem for
//! monotonicity at a negative factor are `lib/_tests/std/num/int_tests.hthr`,
//! which the whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4, §3.5).
//!
//! What is left is a review-lint assertion over the module's own source.

use heather_elab::{ElabError, Elaborator, Lint};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");

/// The prefix elaborated from source with review lints on, so the module's
/// own warnings are visible (a replayed image carries none).
fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.set_review_lints(true);
    for (name, src) in [
        ("logic", LOGIC), ("bool", BOOL), ("nat", NAT),
        ("option", OPTION), ("pair", PAIR), ("list", LIST),
        ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
        ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
        ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
        ("algebra", ALGEBRA), ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")), ("int", INT),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
    e
}

#[test]
fn the_kernel_required_motives_are_retained() {
    let mut e = elaborated();
    assert!(
        INT.contains("decide_bit_split<a <= b>(λ c => a <= match c { True => b, False => a }")
            && INT.contains("decide_bit_split<a <= b>(λ c => b <= match c { True => b, False => a }")
            && INT.contains("decide_bit_split<a <= b>(λ x => c <= match x { True => a, False => b }"),
        "the three kernel-required motives remain explicit (over the bit an evidence-free `if` matches on)"
    );
    assert!(
        e.take_warnings().iter().all(|w| w.lint != Lint::RedundantMatchMotive),
        "a motive whose omission elaborates but fails the local kernel check is retained"
    );
}
