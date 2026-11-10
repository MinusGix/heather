use crate::read_loop_fixture::checker_with;

// Bounded loops lowered by `function_ir_lower_calls`'s one theorem
// (issues/function-ir-verified-lowering.md, round 5). The loop keeps its
// state in registers, counts its passes left down in a counter, and comes
// out with the exhausted bit in a flag register; the theorem is proved by
// induction on the passes left. The fixture lowers a fold that runs out of
// passes, gcd with a conditional in its body, and a call in a loop by
// evaluation and instantiates the theorem; shows a loop bounded by its
// measure never runs out (`loop_runs_unexhausted`); and keeps the refusal
// controls (the flag or counter sharing a register, the counter clobbered,
// too few registers, the flag in a callee-saved register).
const EXAMPLES: &str = include_str!("fixtures/function_ir_lower_loops_examples.hthr");

fn checker() -> heather_elab::Elaborator {
    checker_with(&[
        ("x86_64_kept", include_str!("../../../lib/std/arch/x86_64/x86_64_kept.hthr")),
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
        ("x86_64_stack_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_stack_runs.hthr")),
        ("function_ir_eval", include_str!("../../../lib/native/function_ir/function_ir_eval.hthr")),
        // What the lowering's narrow widths read (`bitvec_nat` is the prefix's).
        ("bitvec_resize", include_str!("../../../lib/std/bitvec/bitvec_resize.hthr")),
        ("function_ir_lower", include_str!("../../../lib/native/function_ir/function_ir_lower.hthr")),
        // `shared`, which the placement planner binds its plans with.
        ("nat_map", include_str!("../../../lib/std/data/nat_map.hthr")),
        ("function_ir_lower_structured", include_str!("../../../lib/native/function_ir/function_ir_lower_structured.hthr")),
        ("function_ir_lower_calls", include_str!("../../../lib/native/function_ir/function_ir_lower_calls.hthr")),
    ])
}

#[test]
fn verified_loop_lowering_checks_and_lowers_the_examples() {
    let mut elaborator = checker();
    if let Err(error) = elaborator.elab_module_source("function_ir_lower_loops_examples", EXAMPLES) {
        panic!("the lowered loops did not check: {}", error.render(EXAMPLES));
    }
}

#[test]
fn a_back_edge_to_the_wrong_label_is_refused() {
    let mutant = EXAMPLES.replace(".put(Block([AddRI8(Rcx, BitVec::ofNat(255))])).put(Jmp(2))\n        .label(4).put(Block([MovRI(Rdx, w(1))]))\n        .label(5)\n        .put(Block([MovRR(Rax, R8)])).put(Block([frame_free()])).put(Ret)\n}\n\ntheorem triangle_lowers",
        ".put(Block([AddRI8(Rcx, BitVec::ofNat(255))])).put(Jmp(3))\n        .label(4).put(Block([MovRI(Rdx, w(1))]))\n        .label(5)\n        .put(Block([MovRR(Rax, R8)])).put(Block([frame_free()])).put(Ret)\n}\n\ntheorem triangle_lowers");
    assert_ne!(mutant, EXAMPLES, "the mutation site moved");
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("function_ir_lower_loops_examples", &mutant).is_err(),
        "a loop whose back edge jumps to the wrong label was accepted");
}

#[test]
fn a_fold_is_not_claimed_to_leave_early() {
    let mutant = EXAMPLES.replace("Valuation::bind(Valuation::zero(), [0], [w(4)]))(1, 3) = BitVec::ofBool(True)",
        "Valuation::bind(Valuation::zero(), [0], [w(4)]))(1, 3) = BitVec::ofBool(False)");
    assert_ne!(mutant, EXAMPLES, "the mutation site moved");
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("function_ir_lower_loops_examples", &mutant).is_err(),
        "a fold that runs out of passes was evaluated as leaving early");
}
