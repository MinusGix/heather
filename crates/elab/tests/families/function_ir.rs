//! The `function_ir` family: FunctionIR, its certificates, the verified lowering, and the native models under it.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;
#[path = "../support/x86_prefix.rs"]
mod common;
#[path = "../support/read_loop.rs"]
mod read_loop_fixture;

#[path = "../function_ir.rs"]
mod function_ir;
#[path = "../function_ir_cert.rs"]
mod function_ir_cert;
#[path = "../function_ir_lower.rs"]
mod function_ir_lower;
#[path = "../function_ir_lower_structured.rs"]
mod function_ir_lower_structured;
#[path = "../function_ir_lower_calls.rs"]
mod function_ir_lower_calls;
#[path = "../function_ir_lower_loops.rs"]
mod function_ir_lower_loops;
#[path = "../function_ir_compile.rs"]
mod function_ir_compile;
#[path = "../function_ir_eval.rs"]
mod function_ir_eval;
#[path = "../native_source.rs"]
mod native_source;
#[path = "../native_cat_spec.rs"]
mod native_cat_spec;
#[path = "../function_ir_loop.rs"]
mod function_ir_loop;
#[path = "../linux_determinism.rs"]
mod linux_determinism;
#[path = "../native_foundation.rs"]
mod native_foundation;
#[path = "../linux_spec.rs"]
mod linux_spec;
#[path = "../linux_wp.rs"]
mod linux_wp;
#[path = "../linux_wp_count.rs"]
mod linux_wp_count;
#[path = "../linux_wp_call.rs"]
mod linux_wp_call;
#[path = "../x86_64_stack_runs.rs"]
mod x86_64_stack_runs;
#[path = "../x86_64_byte_memory.rs"]
mod x86_64_byte_memory;
