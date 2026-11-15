//! `lib/std/machine/memory.hthr` — byte-addressed memory with explicit access
//! outcomes (`issues/byte-memory-access-model.md`,
//! `docs/native/byte-memory-design.md`): the refusal that needs the checker. The
//! model's choices at a literal and at an open memory, and the `¬` theorems
//! that a self-overlapping span does not read back, a refused write has no
//! `Ok` and the two packings differ, are
//! `lib/_tests/std/machine/memory_tests.hthr`, which the whole-library gate
//! checks (`crates/cli/tests/library.rs`); the client showcase is a CLI-tier
//! row of `docs/showcase/showcases.tsv` (docs/test-value-audit.md §3.4, §3.5).

use crate::support::{self, Refusal};

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
    ("result", include_str!("../../../lib/std/core/result.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec/bitvec.hthr")),
    (
        "bitvec_nat",
        include_str!("../../../lib/std/bitvec/bitvec_nat.hthr"),
    ),
    ("bitvec_resize", include_str!("../../../lib/std/bitvec/bitvec_resize.hthr")),
    ("vector", include_str!("../../../lib/std/data/vector.hthr")),
    (
        "bitvec_bytes",
        include_str!("../../../lib/std/bitvec/bitvec_bytes.hthr"),
    ),
    ("dec_set", include_str!("../../../lib/std/data/set/dec_set.hthr")),
    ("span_set", include_str!("../../../lib/std/data/set/span_set.hthr")),
    ("memory", include_str!("../../../lib/std/machine/memory.hthr")),
];

/// The read-back theorem takes a `Distinct` premise (a span longer than the
/// space overlaps itself, `overlap_does_not_read_back` in the probes), so a
/// citation without it is short an argument.
#[test]
fn read_back_needs_its_distinct_premise() {
    let mut e = support::semantic_test_base(MODULES);
    support::assert_refused(
        &mut e,
        "memory_read_back_unpremised",
        "import logic; import algebra; import nat; import omega; import option; import result;
        import bitvec; import bitvec_bytes; import vector; import memory;
        theorem wrong<A, C>(m: Memory<A, C>, laws: SpaceLaws<A>(m.space), a: A, cs: [C; 2]):
            m.set_span(a, cs).get_span(a, 2) = cs { m.get_set_span(laws, a, cs) }\n",
        Refusal::Says("too few arguments"),
    );
}
