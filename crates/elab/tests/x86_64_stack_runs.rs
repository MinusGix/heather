use crate::read_loop_fixture::checker_with;

// Runs of the machine with the stack (issues/function-ir-verified-lowering.md,
// round 3): the stack forms and their profile, round 1's frame lemmas moved
// down, and the state-level runs over a label program. The fixture closes a
// callee by RET into its contract, composes a caller's CALL against it, and
// meets the stack laws with a toy memory.
const EXAMPLES: &str = include_str!("fixtures/x86_64_stack_runs_examples.hthr");

#[test]
fn the_stack_runs_compose_a_call() {
    let mut elaborator = checker_with(&[
        ("x86_64_kept", include_str!("../../../lib/std/arch/x86_64/x86_64_kept.hthr")),
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
        ("bitvec_shift_nat", include_str!("../../../lib/std/bitvec/bitvec_shift_nat.hthr")),
        ("x86_64_stack_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_stack_runs.hthr")),
    ]);
    if let Err(error) = elaborator.elab_module_source("x86_64_stack_runs_examples", EXAMPLES) {
        panic!("the stack runs did not compose: {}", error.render(EXAMPLES));
    }
}
