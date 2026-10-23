use crate::read_loop_fixture::checker_with;

// What `compile-x86` states about a program
// (issues/function-ir-verified-lowering.md, round 4): the planner's
// placement lowers it, each function evaluates to its source by `refl`,
// and `compiled_returns` makes the two a returns claim. The fixture covers
// the planner's cases (a value live across calls, swapped and rotated
// arguments, calls in a branch's arms); the controls: a wrong source is
// refused, and so is a rotation scheduled without its staging move.
const EXAMPLES: &str = include_str!("fixtures/function_ir_compile_examples.hthr");

fn checker() -> heather_elab::Elaborator {
    checker_with(&[
        ("x86_64_kept", include_str!("../../../lib/std/arch/x86_64/x86_64_kept.hthr")),
        ("x86_64_stack", include_str!("../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
        ("x86_64_stack_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_stack_runs.hthr")),
        ("function_ir_eval", include_str!("../../../lib/native/function_ir/function_ir_eval.hthr")),
        ("function_ir_lower", include_str!("../../../lib/native/function_ir/function_ir_lower.hthr")),
        ("function_ir_lower_structured", include_str!("../../../lib/native/function_ir/function_ir_lower_structured.hthr")),
        ("function_ir_lower_calls", include_str!("../../../lib/native/function_ir/function_ir_lower_calls.hthr")),
        ("function_ir_compile", include_str!("../../../lib/native/function_ir/function_ir_compile.hthr")),
    ])
}

#[test]
fn compiled_programs_check() {
    let mut elaborator = checker();
    if let Err(error) = elaborator.elab_module_source("function_ir_compile_examples", EXAMPLES) {
        panic!("the compiled examples did not check: {}", error.render(EXAMPLES));
    }
}

#[test]
fn a_wrong_source_is_refused() {
    let mutant = EXAMPLES.replace("= y.sub(z).add(x) { refl }", "= z.sub(y).add(x) { refl }");
    assert_ne!(mutant, EXAMPLES, "the mutation site moved");
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("function_ir_compile_examples", &mutant).is_err(),
        "an evaluation was equated with the wrong source");
}

#[test]
fn a_rotation_needs_its_staging_move() {
    let mutant = EXAMPLES.replace("rotation_file().call_moves([1, 2, 0])).len() = 4", "rotation_file().call_moves([1, 2, 0])).len() = 3");
    assert_ne!(mutant, EXAMPLES, "the mutation site moved");
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("function_ir_compile_examples", &mutant).is_err(),
        "a rotation scheduled in three moves");
}
