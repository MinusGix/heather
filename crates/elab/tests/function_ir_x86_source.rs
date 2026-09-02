#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn function_ir_x86_source() {
    common::run_source_tests();
}

#[test]
#[ignore = "elaborated source reflection/module rail; run explicitly"]
fn elaborated_source_reflection_builds_a_shared_dag() {
    common::elaborated_source_reflection_builds_a_shared_dag();
}

#[test]
#[ignore = "full nested source-to-x86 proof rail; run explicitly"]
fn elaborated_shared_source_reaches_checked_x86_artifact() {
    common::elaborated_shared_source_reaches_checked_x86_artifact();
}
