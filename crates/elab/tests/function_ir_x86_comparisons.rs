#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn function_ir_x86_comparisons() {
    common::run_comparison_tests();
}
