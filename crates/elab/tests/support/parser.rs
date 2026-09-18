//! Dependency-ordered parser modules, shared by library and calculator checks.
use heather_elab::Elaborator;

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
    ("parser", include_str!("../../../../lib/std/parser.hthr")),
];

pub fn load(e: &mut Elaborator) {
    for &(name, source) in MODULES {
        e.elab_module_source(name, source).unwrap_or_else(|err| panic!("{}", err.render(source)));
    }
}
