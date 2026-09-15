//! Dependency-ordered parser modules, shared by library and calculator checks.
use heather_elab::Elaborator;

pub fn load(e: &mut Elaborator) {
    for (name, source) in [
        ("parser_core", include_str!("../../../../lib/std/parser/parser_core.hthr")),
        ("parser_contracts", include_str!("../../../../lib/std/parser/parser_contracts.hthr")),
        ("parser_diagnostics", include_str!("../../../../lib/std/parser/parser_diagnostics.hthr")),
        ("parser_combinators", include_str!("../../../../lib/std/parser/parser_combinators.hthr")),
        ("parser_primitives", include_str!("../../../../lib/std/parser/parser_primitives.hthr")),
        ("parser_recursion", include_str!("../../../../lib/std/parser/parser_recursion.hthr")),
        ("parser_repetition", include_str!("../../../../lib/std/parser/parser_repetition.hthr")),
        ("parser", include_str!("../../../../lib/std/parser.hthr")),
    ] {
        e.elab_module_source(name, source).unwrap_or_else(|err| panic!("{}", err.render(source)));
    }
}
