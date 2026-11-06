//! Dependency-ordered parser modules, shared by library and calculator checks.
use heather_elab::Elaborator;

/// The standard-library prefix the parser library is checked over, in
/// dependency order. Its first thirteen modules are the omega prefix
/// (`semantic_omega_warmup`); the rest are grind's closure, which
/// `parser_diagnostics::commit_chain` is proved by.
pub const STD: &[(&str, &str)] = &[
    ("logic", include_str!("../../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../../lib/std/tactic/omega.hthr")),
    ("result", include_str!("../../../../lib/std/core/result.hthr")),
    ("char", include_str!("../../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../../lib/std/text/string.hthr")),
    ("tactic", include_str!("../../../../lib/std/tactic/tactic.hthr")),
    ("derive", include_str!("../../../../lib/std/tactic/derive.hthr")),
    ("egraph", include_str!("../../../../lib/std/data/egraph.hthr")),
    ("grind", include_str!("../../../../lib/std/tactic/grind.hthr")),
];

/// The checked showcase modules, the manifest's `suite` tier
/// (`showcase_calculator`'s first test holds the two lists equal).
pub const SHOWCASE: &[(&str, &str)] = &[
    ("calc", include_str!("../../../../docs/showcase/calc.hthr")),
    ("calc_parser", include_str!("../../../../docs/showcase/calc_parser.hthr")),
];

/// The parser library's dependency-first closure, in the order a test used to
/// elaborate it by hand. Targets that replay it as checked semantic images
/// append it to their standard-library list for `support::semantic_test_base`
/// (issues/integration-test-prefix-reelaboration.md: until 2026-09-17 the
/// showcase and parser-library binaries re-elaborated these eight modules from
/// source under the debug profile on every run — 19 s of the parser library's
/// 19 s alone at width one, 10 s of the showcase's 22 s).
pub const MODULES: &[(&str, &str)] = &[
    ("parser_core", include_str!("../../../../lib/std/parser/parser_core.hthr")),
    ("parser_contracts", include_str!("../../../../lib/std/parser/parser_contracts.hthr")),
    ("parser_diagnostics", include_str!("../../../../lib/std/parser/parser_diagnostics.hthr")),
    ("parser_combinators", include_str!("../../../../lib/std/parser/parser_combinators.hthr")),
    ("parser_primitives", include_str!("../../../../lib/std/parser/parser_primitives.hthr")),
    ("parser_recursion", include_str!("../../../../lib/std/parser/parser_recursion.hthr")),
    ("parser_repetition", include_str!("../../../../lib/std/parser/parser_repetition.hthr")),
    ("parser", include_str!("../../../../lib/std/parser/parser.hthr")),
];

pub fn load(e: &mut Elaborator) {
    for &(name, source) in MODULES {
        e.elab_module_source(name, source).unwrap_or_else(|err| panic!("{}", err.render(source)));
    }
}

/// `STD` up to and including `last`.
pub fn std_through(last: &str) -> &'static [(&'static str, &'static str)] {
    let end = STD.iter().position(|(name, _)| *name == last).expect("a module of STD");
    &STD[..=end]
}

/// What `parser_library` replays: `STD`, then the parser library.
pub fn library_prefix() -> Vec<(&'static str, &'static str)> {
    STD.iter().chain(MODULES).copied().collect()
}

/// What `showcase_calculator` replays: the library prefix, then `SHOWCASE`.
pub fn showcase_prefix() -> Vec<(&'static str, &'static str)> {
    STD.iter().chain(MODULES).chain(SHOWCASE).copied().collect()
}
