//! The dataflow x86 certificate gates in one binary: lowering, source,
//! ALU and comparison groups share one replay of the 18-module prefix
//! (`base_image`), which at ~5 s per process was most of each group's cost
//! once the gate ran wide (2026-09-12, alone on furnace: suffixes 0.1 s,
//! 3.3 s, 2.5 s and 0.8 s against a 5.4 s replay each). The conditional and
//! control-region groups keep their own binaries: their suffixes are the
//! kernel-bound linked-conditional items ([`common::run_conditional_tests`]),
//! and the model group replays a different prefix length.
#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn function_ir_x86_dataflow() {
    common::run_lowering_tests();
    common::run_source_tests();
    common::run_alu_tests();
    common::run_comparison_tests();
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
