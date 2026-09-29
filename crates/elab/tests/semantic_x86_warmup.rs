//! Populate or safely replay the shared x86 semantic test prefix in its own
//! resource-bounded process before expensive acceptance suffixes are run.

mod support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec.hthr")),
    ("relation", include_str!("../../../lib/std/relation.hthr")),
    ("location", include_str!("../../../lib/std/location.hthr")),
    (
        "certified_lookup",
        include_str!("../../../lib/std/certified_lookup.hthr"),
    ),
    ("x86_64", include_str!("../../../lib/std/arch/x86_64/x86_64.hthr")),
];

#[test]
fn x86_semantic_prefix_is_ready() {
    support::semantic_test_base(MODULES);
}
