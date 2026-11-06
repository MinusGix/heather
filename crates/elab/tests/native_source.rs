use crate::read_loop_fixture::checker_with;

// The effectful layer over total FunctionIR (`lib/native/native_source.hthr`;
// issues/native-effect-source-compiler.md, round S3.1): statements, their
// trees over Linux's calls, the program a source denotes, and `cat`
// (`lib/native/native_cat.hthr`) run against a scripted world by
// evaluation. The controls: a run claimed to send the wrong bytes is
// refused, and so is a `cat` that exits 0 after a failed write.
const CAT: &str = include_str!("fixtures/native_source_cat.hthr");
const NATIVE_CAT: &str = include_str!("../../../lib/native/native_cat.hthr");

fn checker() -> heather_elab::Elaborator { checker_over(NATIVE_CAT) }

fn checker_over(native_cat: &str) -> heather_elab::Elaborator {
    checker_with(&[
        ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
        ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
        ("itree_deep", include_str!("../../../lib/std/itree/itree_deep.hthr")),
        ("linux_trees", include_str!("../../../lib/std/os/linux/linux_trees.hthr")),
        ("function_ir_eval", include_str!("../../../lib/native/function_ir/function_ir_eval.hthr")),
        ("function_ir_state", include_str!("../../../lib/native/function_ir/function_ir_state.hthr")),
        ("native_source", include_str!("../../../lib/native/native_source.hthr")),
        ("native_cat", native_cat),
    ])
}

#[test]
fn native_source_checks_and_cat_runs() {
    let mut elaborator = checker();
    if let Err(error) = elaborator.elab_module_source("native_source_cat", CAT) {
        panic!("cat did not check: {}", error.render(CAT));
    }
}

// The fixture up to its runs, and one run: each run costs a long
// evaluation, so a control checks only the run it is about.
fn with_run(program: &str, run: &str) -> String {
    let at = program.find("// Runs").expect("the fixture's runs moved");
    format!("{}\n{}\n", &program[..at], run)
}

const COPIES_ONE: &str = "theorem cat_copies_one(): world_run(1, False, cat(2).denote([]).at(6), [byte(7)], Nil)
    = Finished(BitVec::ofNat(0), [byte(7)]) { refl }";

const WRITE_FAILS: &str = "theorem cat_write_fails(): world_run(2, True, cat(2).denote([]).at(6), [byte(1)], Nil)
    = Finished(BitVec::ofNat(1), Nil) { refl }";

#[test]
fn a_run_sending_the_wrong_bytes_is_refused() {
    assert!(CAT.contains(COPIES_ONE), "the run the control mutates moved");
    let mutant = with_run(CAT, &COPIES_ONE.replace("[byte(7)]) { refl }", "[byte(8)]) { refl }"));
    let mut elaborator = checker();
    assert!(elaborator.elab_module_source("native_source_cat", &mutant).is_err(),
        "a run claimed to send the wrong bytes was accepted");
}

#[test]
fn a_cat_ignoring_a_failed_write_is_refused() {
    assert!(CAT.contains(WRITE_FAILS), "the run the control mutates moved");
    let program = NATIVE_CAT.replace("Branch(12, Exit(10), ops([]))", "Branch(12, Exit(11), ops([]))");
    assert_ne!(program, NATIVE_CAT, "the mutation site moved");
    let mutant = with_run(CAT, WRITE_FAILS);
    let mut elaborator = checker_over(&program);
    assert!(elaborator.elab_module_source("native_source_cat", &mutant).is_err(),
        "a cat exiting 0 after a failed write was accepted");
}
