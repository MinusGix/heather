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
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
        ("x86_64_stack_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_stack_runs.hthr")),
        ("function_ir_eval", include_str!("../../../lib/native/function_ir/function_ir_eval.hthr")),
        // The state a function's meaning threads and its runs over a file
        // (`function_ir_writes`), which the reads and the calls are stated over.
        ("nat_map", include_str!("../../../lib/std/data/nat_map.hthr")),
        ("function_ir_state", include_str!("../../../lib/native/function_ir/function_ir_state.hthr")),
        ("function_ir_writes", include_str!("../../../lib/native/function_ir/function_ir_writes.hthr")),
        // What the lowering's narrow widths read (`bitvec_nat` is the prefix's).
        ("function_ir_lower", include_str!("../../../lib/native/function_ir/function_ir_lower.hthr")),
        // `shared`, which the placement planner binds its plans with.
        // A call over views: the windows it lends and puts back.
        ("function_ir_views", include_str!("../../../lib/native/function_ir/function_ir_views.hthr")),
        // The evaluator that threads the file through stores and calls, which
        // `compiled_returns_run` states a writing function's answer by.
        ("function_ir_run", include_str!("../../../lib/native/function_ir/function_ir_run.hthr")),
        ("function_ir_lower_structured", include_str!("../../../lib/native/function_ir/function_ir_lower_structured.hthr")),
        // The reads of a lent span, which the calls module lowers through.
        ("function_ir_lower_reads", include_str!("../../../lib/native/function_ir/function_ir_lower_reads.hthr")),
        // The lending laws the calls module's contract is stated under.
        ("x86_64_lending", include_str!("../../../lib/std/arch/x86_64/x86_64_lending.hthr")),
        // A call over views: the machine's laws of a lent window, and what the
        // lowering checks of a view before it lends it.
        ("x86_64_views", include_str!("../../../lib/std/arch/x86_64/x86_64_views.hthr")),
        ("function_ir_lower_views", include_str!("../../../lib/native/function_ir/function_ir_lower_views.hthr")),
        ("function_ir_lower_calls", include_str!("../../../lib/native/function_ir/function_ir_lower_calls.hthr")),
        // What a pass owes for a program lowered in another's place
        // (`ProgramRewrites`), which the return theorems are stated through.
        ("function_ir_stage", include_str!("../../../lib/native/function_ir/function_ir_stage.hthr")),
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
