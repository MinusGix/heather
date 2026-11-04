//! Populate or safely replay the shared Omega semantic test prefix in its own
//! resource-bounded process before expensive acceptance suffixes are run.

mod support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
];

#[test]
fn omega_semantic_prefix_is_ready() {
    support::semantic_test_base(MODULES);
}
