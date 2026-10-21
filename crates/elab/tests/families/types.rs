//! The `types` family: Records, universes, polymorphism and function types.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).


#[path = "../records.rs"]
mod records;
#[path = "../record_projection_size.rs"]
mod record_projection_size;
#[path = "../record_type_partial_application.rs"]
mod record_type_partial_application;
#[path = "../record_type_values.rs"]
mod record_type_values;
#[path = "../type_members.rs"]
mod type_members;
#[path = "../types_as_expressions.rs"]
mod types_as_expressions;
#[path = "../universe.rs"]
mod universe;
#[path = "../polymorphism.rs"]
mod polymorphism;
#[path = "../function_types.rs"]
mod function_types;
#[path = "../vector_types.rs"]
mod vector_types;
#[path = "../value_parameters.rs"]
mod value_parameters;
#[path = "../inductive_value_parameters.rs"]
mod inductive_value_parameters;
#[path = "../surface_fin.rs"]
mod surface_fin;
#[path = "../surface_existential_probe.rs"]
mod surface_existential_probe;
