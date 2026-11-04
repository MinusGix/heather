//! `lib/std/algebra/algebra.hthr`'s derived-instance table, which Heather
//! cannot state about itself (`docs/traits-layer2-design.md` §7.1, §8).
//!
//! The library's classes and instances are probed in Heather, in
//! `lib/_tests/std/algebra/algebra_tests.hthr`: which instance is registered
//! at each carrier, the extends chain, the generic instance at an open element
//! type, and the policy's refusals as `// expect-error` declarations, all
//! checked by the whole-library gate (`crates/cli/tests/library.rs`). What
//! stays here is structure: how many canonical derived instances the
//! library's own goals mint, read off `Elaborator::derived_instances`.

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");

/// The closure in dependency order — the order the CLI's loader would pick.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", ALGEBRA),
];

/// The closure (checked once per process), with `extra` checked on top as a
/// module that imports it, as a user file would.
fn ok(extra: &str) -> heather_elab::Elaborator {
    let mut e = support::library(MODULES);
    let src = format!("import bool;\nimport nat;\nimport option;\nimport list;\nimport algebra;\n{extra}");
    if let Err(err) = e.elab_module_source("probe", &src) {
        panic!("expected this to check, got: {}", err.render(&src));
    }
    e
}

/// The canonical derived table does **not** fire for a goal with a value
/// index, and this pins the fact rather than hiding it: the index is a *term*
/// in the goal type, and a term elaborated at a use site carries that site's
/// identity substitution, so the table's closedness test — asked in the empty
/// context, which is where a minted global has to live — says no. Two use
/// sites therefore each inline their own derivation. Sharing, never
/// correctness, which is the table's standing bargain; recorded as a residue
/// by the round that found it.
#[test]
fn a_derived_list_monoid_is_not_shared_between_use_sites() {
    let e = ok("
fn f(xss: List<List<Nat>>) -> List<Nat> { xss.mconcat(List::append) }
fn g(xss: List<List<Nat>>) -> List<Nat> { xss.mconcat(List::append) }
theorem same(xss: List<List<Nat>>): f(xss) = g(xss) { refl }
");
    assert!(e.derived_instances().is_empty(), "{:?}", e.derived_instances());
    // …and the unindexed classes still canonicalize, unchanged: `Default` has
    // a generic instance at `List<A>` and one goal mints one global.
    let e = ok("
fn p(o: Option<List<Nat>>) -> List<Nat> { or_default(o) }
fn q(o: Option<List<Nat>>) -> List<Nat> { or_default(o) }
theorem same2(o: Option<List<Nat>>): p(o) = q(o) { refl }
");
    assert_eq!(e.derived_instances().len(), 1, "{:?}", e.derived_instances());
}

/// The negative control for the table, and a fact about the library worth
/// knowing: calling `concat` derives **nothing**. Its resolution happened once,
/// inside `concat`'s own body, at an open carrier — which is not a closed goal
/// and so is never minted. A caller only instantiates the type argument.
#[test]
fn calling_concat_derives_nothing() {
    let e = ok("
fn f(xss: List<List<Nat>>) -> List<Nat> { concat(xss) }
fn g(xss: List<List<Bool>>) -> List<Bool> { concat(xss) }
");
    assert!(e.derived_instances().is_empty(), "{:?}", e.derived_instances());
}
