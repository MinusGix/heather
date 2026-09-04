#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn function_ir_x86_conditionals() {
    common::run_conditional_tests();
}
