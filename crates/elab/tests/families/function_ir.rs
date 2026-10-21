//! The `function_ir` family: FunctionIR: the source language, its certificates and their lowering checks.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;
#[path = "../function_ir_x86.rs"]
mod common;
#[path = "../support/structured_composition.rs"]
mod composed_fixture;
#[path = "../support/read_loop.rs"]
mod read_loop_fixture;

#[path = "../function_ir.rs"]
mod function_ir;
#[path = "../function_ir_bounds.rs"]
mod function_ir_bounds;
#[path = "../function_ir_byte_read.rs"]
mod function_ir_byte_read;
#[path = "../function_ir_cert.rs"]
mod function_ir_cert;
#[path = "../function_ir_composed_certificates.rs"]
mod function_ir_composed_certificates;
#[path = "../function_ir_guarded_read.rs"]
mod function_ir_guarded_read;
#[path = "../function_ir_lower.rs"]
mod function_ir_lower;
#[path = "../function_ir_lower_structured.rs"]
mod function_ir_lower_structured;
#[path = "../function_ir_loop.rs"]
mod function_ir_loop;
#[path = "../function_ir_loop_trace.rs"]
mod function_ir_loop_trace;
#[path = "../linux_determinism.rs"]
mod linux_determinism;
#[path = "../native_foundation.rs"]
mod native_foundation;
#[path = "../linux_spec.rs"]
mod linux_spec;
#[path = "../x86_64_stack_runs.rs"]
mod x86_64_stack_runs;
#[path = "../crossing_link_cost.rs"]
mod crossing_link_cost;
#[path = "../function_ir_narrow_certificates.rs"]
mod function_ir_narrow_certificates;
#[path = "../function_ir_recursive.rs"]
mod function_ir_recursive;
#[path = "../function_ir_recursive_certificates.rs"]
mod function_ir_recursive_certificates;
#[path = "../function_ir_search_certificates.rs"]
mod function_ir_search_certificates;
#[path = "../function_ir_typed_publication.rs"]
mod function_ir_typed_publication;
#[path = "../function_ir_typed_scalar_publication.rs"]
mod function_ir_typed_scalar_publication;
