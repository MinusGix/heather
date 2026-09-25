use crate::common;

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

const COMPOSED: &str = r#"
import bitvec; import bool;
fn below(a, b: BitVec(64)) → Bool { @bitvec::BitVec::unsigned_lt_bit(64, a, b) }
fn step(state, limit: BitVec(64)) → BitVec(64) {
    match below(state, limit) { False => @bitvec::BitVec::sub(64, state, limit), True => state }
}
fn chain(x: BitVec(64)) → BitVec(64) { step(step(step(x, @bitvec::BitVec::ofNat(64, 40)), @bitvec::BitVec::ofNat(64, 20)), @bitvec::BitVec::ofNat(64, 10)) }
"#;

// Word- and Bool-valued helpers compose, each crossing at its source call
// (cert::SourceValue). A certificate generated against one helper body is
// refused under another: the body meets the machine code at a `_link`, or in
// the expansion when the call is the function's own result.
#[test]
fn composed_helpers_cross_at_the_call() {
    use heather_elab::function_ir_source::generate_elaborated_typed_x86;
    let mut elab = checker();
    elab.elab_module_source("composed", COMPOSED).unwrap_or_else(|e| panic!("{}", e.render(COMPOSED)));
    let emission = generate_elaborated_typed_x86(&elab, "chain", "composed::chain",
        &Placements::from([(0, Gpr::Rdi)]), &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::R9, Gpr::R10], &Placements::from([(1, Gpr::Rax)])).unwrap();
    let text = emission.text;
    assert!(text.contains("_link(") && text.contains("_source(values)"), "compositions must cross at the call");
    elab.semantic_image().elaborator().elab_module_source("typed_chain", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
    let changed = COMPOSED.replace("@bitvec::BitVec::sub(64, state, limit)", "@bitvec::BitVec::sub(64, limit, state)");
    assert_ne!(changed, COMPOSED);
    let mut stale = checker();
    stale.elab_module_source("composed", &changed).unwrap_or_else(|e| panic!("{}", e.render(&changed)));
    let error = stale.semantic_image().elaborator().elab_module_source("typed_chain", &text).expect_err("a stale helper body must be refused").render(&text);
    assert!(error.contains("kernel rejected") && !error.contains("unbound"), "{error}");
}

