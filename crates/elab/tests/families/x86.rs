//! The `x86` family: The x86 model and lowering, the IR library, and the representation generators.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;
#[path = "../function_ir_x86.rs"]
mod common;

#[path = "../function_ir_x86_conditionals.rs"]
mod function_ir_x86_conditionals;
#[path = "../function_ir_x86_control_flow.rs"]
mod function_ir_x86_control_flow;
#[path = "../function_ir_x86_dataflow.rs"]
mod function_ir_x86_dataflow;
#[path = "../function_ir_x86_model.rs"]
mod function_ir_x86_model;
#[path = "../function_ir_x86_scaling.rs"]
mod function_ir_x86_scaling;
#[path = "../x86_64.rs"]
mod x86_64;
#[path = "../ir_v1.rs"]
mod ir_v1;
#[path = "../ir_pass_fuel.rs"]
mod ir_pass_fuel;
#[path = "../datarepr.rs"]
mod datarepr;
#[path = "../repr_access.rs"]
mod repr_access;
#[path = "../reprgen.rs"]
mod reprgen;
#[path = "../el_reader_audit.rs"]
mod el_reader_audit;
