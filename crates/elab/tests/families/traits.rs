//! The `traits` family: Traits, instances, receivers and operator classes.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../traits.rs"]
mod traits;
#[path = "../traits_inline_constraints.rs"]
mod traits_inline_constraints;
#[path = "../traits_receiver.rs"]
mod traits_receiver;
#[path = "../traits_resolution.rs"]
mod traits_resolution;
#[path = "../traits_type_former_carrier.rs"]
mod traits_type_former_carrier;
#[path = "../traits_type_projection.rs"]
mod traits_type_projection;
#[path = "../instance_resolved_key.rs"]
mod instance_resolved_key;
#[path = "../designation_resolved_key.rs"]
mod designation_resolved_key;
#[path = "../imported_receiver_dispatch.rs"]
mod imported_receiver_dispatch;
#[path = "../method_receiver.rs"]
mod method_receiver;
#[path = "../operation_indexed_classes.rs"]
mod operation_indexed_classes;
#[path = "../operators_onto_classes.rs"]
mod operators_onto_classes;
#[path = "../value_generic_instances.rs"]
mod value_generic_instances;
#[path = "../algebraic_theory_composition.rs"]
mod algebraic_theory_composition;
