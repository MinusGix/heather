//! Checked representation and composition prototype for the parser library.
use heather_elab::Elaborator;
mod support;
fn base() -> Elaborator {
    support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/logic.hthr")),
        ("bool", include_str!("../../../lib/std/bool.hthr")),
        ("nat", include_str!("../../../lib/std/nat.hthr")),
        ("option", include_str!("../../../lib/std/option.hthr")),
        ("pair", include_str!("../../../lib/std/pair.hthr")),
        ("list", include_str!("../../../lib/std/list.hthr")),
        ("algebra", include_str!("../../../lib/std/algebra.hthr")),
        ("int", include_str!("../../../lib/std/int.hthr")),
        ("omega", include_str!("../../../lib/std/omega.hthr")),
        ("result", include_str!("../../../lib/std/result.hthr")),
    ])
}

#[test]
fn checked_parser_core() {
    let source = include_str!("../../../docs/showcase/parser_core.hthr");
    base().elab_module_source("parser_core", source).unwrap_or_else(|e| panic!("{}",e.render(source)));
}

#[test]
fn invalid_cursors_progress_and_dependent_values_are_refused() {
    let mut e = base();
    let source = include_str!("../../../docs/showcase/parser_core.hthr");
    e.elab_module_source("parser_core", source).unwrap_or_else(|err| panic!("{}",err.render(source)));
    for (i, source) in [
        "fn bad() -> Cursor<Nat>([1]) { Cursor(refl,2,refl) }",
        "fn bad() -> CachedCursor<Nat>([1]) { CachedCursor(start([1]),[2],refl) }",
        "fn bad() -> Cursor<Nat>([1]) { start([2]) }",
        "fn bad() -> Success<Nat,Nat>([1],Cursor(refl,1,refl)) { Success(0,start([1]),refl) }",
        "fn bad(source: List<Nat>, begin: Cursor<Nat>(source), recur: (later: Cursor<Nat>(source)) -> nat::Lt(begin.offset,later.offset) -> Reply<Nat,Nat>(source,later)) -> Reply<Nat,Nat>(source,begin) { recur(begin,nat::le_refl(begin.offset)) }",
        "fn bad() -> Dep<Nat>(witness) { Dep(0,nat::lt_succ_self(0)) }",
        "theorem bad(): observe([1,2],start([1,2]),count([1,2])) = Ok<Pair<Nat,Nat>,Nat>(Pair(1,2)) { refl }",
    ].iter().enumerate() {
        let source = format!("import parser_core; import logic; import nat; import list; import result; import pair; {source}");
        let error = e.elab_module_source(&format!("bad{i}"), &source).expect_err(source.as_str());
        assert!(!error.render(&source).contains("panicked"));
    }
    e.elab_module_source("after", "theorem clean(n: Nat): n = n { refl }").unwrap();
}
