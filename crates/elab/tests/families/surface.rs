//! The `surface` family: Surface syntax: application, arguments, binders, blocks and operators.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../apply.rs"]
mod apply;
#[path = "../argument_slots.rs"]
mod argument_slots;
#[path = "../argument_type_reduction.rs"]
mod argument_type_reduction;
#[path = "../assuming_groups.rs"]
mod assuming_groups;
#[path = "../binder_symbol_notation.rs"]
mod binder_symbol_notation;
#[path = "../callback_expected_types.rs"]
mod callback_expected_types;
#[path = "../implicit_args.rs"]
mod implicit_args;
#[path = "../implicit_fn_binders.rs"]
mod implicit_fn_binders;
#[path = "../unifier_checked_assignment.rs"]
mod unifier_checked_assignment;
#[path = "../named_arguments.rs"]
mod named_arguments;
#[path = "../overapplication.rs"]
mod overapplication;
#[path = "../let_and_blocks.rs"]
mod let_and_blocks;
#[path = "../have.rs"]
mod have;
#[path = "../operators.rs"]
mod operators;
#[path = "../sections.rs"]
mod sections;
#[path = "../sequent_binders.rs"]
mod sequent_binders;
#[path = "../quotation.rs"]
mod quotation;
#[path = "../result_propagation.rs"]
mod result_propagation;
