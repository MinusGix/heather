use crate::read_loop_fixture::checker_with;

// FunctionIR evaluated by a total function, and the theorem that what it
// computes satisfies the region's equations
// (issues/function-ir-total-evaluator.md). The fixture evaluates the
// lowering rounds' programs by `refl`, instantiates the theorem at literal
// and open arguments, and keeps the schedules `evaluable` refuses. The
// controls: a wrong result is refused by the kernel, and the theorem does
// not instantiate at a call of the wrong arity.
const EXAMPLES: &str = include_str!("fixtures/function_ir_eval_examples.hthr");

fn checker() -> heather_elab::Elaborator {
    checker_with(&[("function_ir_eval", include_str!("../../../lib/native/function_ir/function_ir_eval.hthr"))])
}

#[test]
fn function_ir_eval_checks_and_evaluates_the_examples() {
    let mut elaborator = checker();
    if let Err(error) = elaborator.elab_module_source("function_ir_eval_examples", EXAMPLES) {
        panic!("the evaluated examples did not check: {}", error.render(EXAMPLES));
    }
}

#[test]
fn a_wrong_result_is_refused() {
    let mutant = EXAMPLES.replace("program_eval(pair(), 1, [w(3), w(4)]) = w(10) { refl }",
        "program_eval(pair(), 1, [w(3), w(4)]) = w(11) { refl }");
    assert_ne!(mutant, EXAMPLES, "the mutation site moved");
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("function_ir_eval_examples", &mutant).is_err(),
        "a wrong evaluated result was accepted");
}

#[test]
fn the_theorem_does_not_instantiate_at_the_wrong_arity() {
    let mutant = EXAMPLES.replace("program_eval_computes(pair(), pair_evaluable, 1, [w(3), w(4)], trivial,",
        "program_eval_computes(pair(), pair_evaluable, 1, [w(3)], trivial,");
    assert_ne!(mutant, EXAMPLES, "the mutation site moved");
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("function_ir_eval_examples", &mutant).is_err(),
        "the theorem instantiated at a call of the wrong arity");
}
