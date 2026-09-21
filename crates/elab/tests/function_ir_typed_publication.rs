#[path = "function_ir_x86.rs"]
mod common;

use heather_elab::function_ir_x86_lower::{Gpr, Placements};


fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    elab
}

#[test]
fn typed_search_publication_checks() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let mut elab = checker();
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let emission = generate_elaborated_typed_x86(&elab, "search", "readonly_loops::search_body",
        &Placements::from([(0, Gpr::Rdi), (2, Gpr::Rsi), (3, Gpr::R8)]),
        &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::R9, Gpr::R10],
        &Placements::from([(4, Gpr::Rax), (5, Gpr::Rdx)])).unwrap();
    let text = emission.text;
    elab.elab_module_source("typed_search", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));

}

