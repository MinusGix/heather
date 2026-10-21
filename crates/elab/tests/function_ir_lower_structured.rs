use crate::read_loop_fixture::checker_with;

// FunctionIR's structured regions lowered by a Heather function proved
// correct once (issues/function-ir-verified-lowering.md, round 2). The
// modules hold the pure fetched-run lemmas over the label assembler and the
// lowering with its theorem; the fixture lowers branches.hthr's shapes (a
// selected arithmetic, a nested conditional, an arm returning an input, a
// conditional on a conditional's bit) by evaluation, instantiates the
// theorem, and keeps the refusal controls (arms apart, a word condition, a
// clobbered condition, programs not laid out).
const EXAMPLES: &str = include_str!("fixtures/function_ir_lower_structured_examples.hthr");

#[test]
fn verified_structured_lowering_checks_and_lowers_the_examples() {
    let mut elaborator = checker_with(&[
        ("x86_64_kept", include_str!("../../../lib/std/arch/x86_64/x86_64_kept.hthr")),
        ("x86_64_stack", include_str!("../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
        ("function_ir_lower", include_str!("../../../lib/function_ir_lower.hthr")),
        ("function_ir_lower_structured", include_str!("../../../lib/function_ir_lower_structured.hthr")),
    ]);
    if let Err(error) = elaborator.elab_module_source("function_ir_lower_structured_examples", EXAMPLES) {
        panic!("the lowered examples did not check: {}", error.render(EXAMPLES));
    }
}
