#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn function_ir_x86_lowering() {
    common::run_lowering_tests();
}
