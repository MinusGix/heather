#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn function_ir_x86_model() {
    common::run_model_tests();
}
