use crate::read_loop_fixture::checker_with;

// FunctionIR programs with calls lowered by a Heather function proved
// correct once (issues/function-ir-verified-lowering.md, round 3). The
// module lowers each function to a frame, its body with calls saving the
// caller-saved registers around them, and RET, and proves every function
// meets its contract given the ones it calls meet theirs. The fixture
// lowers a caller of `double`, a value live across a call, and a call in a
// conditional's arm by evaluation, instantiates the theorem, and keeps the
// refusal controls (a value the call's result overwrites, recursion, a
// forward call, seven arguments).
const EXAMPLES: &str = include_str!("fixtures/function_ir_lower_calls_examples.hthr");

#[test]
fn verified_call_lowering_checks_and_lowers_the_examples() {
    let mut elaborator = checker_with(&[
        ("x86_64_kept", include_str!("../../../lib/std/arch/x86_64/x86_64_kept.hthr")),
        ("x86_64_stack", include_str!("../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
        ("x86_64_stack_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_stack_runs.hthr")),
        ("function_ir_lower", include_str!("../../../lib/native/function_ir/function_ir_lower.hthr")),
        ("function_ir_lower_structured", include_str!("../../../lib/native/function_ir/function_ir_lower_structured.hthr")),
        ("function_ir_lower_calls", include_str!("../../../lib/native/function_ir/function_ir_lower_calls.hthr")),
    ]);
    if let Err(error) = elaborator.elab_module_source("function_ir_lower_calls_examples", EXAMPLES) {
        panic!("the lowered examples did not check: {}", error.render(EXAMPLES));
    }
}
