//! The `logic` family: Logic, goals and holes, the parsers and the showcase.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../logic.rs"]
mod logic;
#[path = "../squash.rs"]
mod squash;
#[path = "../true_prop.rs"]
mod true_prop;
#[path = "../goal_combinators.rs"]
mod goal_combinators;
#[path = "../goal_holes.rs"]
mod goal_holes;
#[path = "../equation_rewrite.rs"]
mod equation_rewrite;
#[path = "../constructor_values.rs"]
mod constructor_values;
#[path = "../annotation_cost.rs"]
mod annotation_cost;
#[path = "../parser_core.rs"]
mod parser_core;
#[path = "../parser_library.rs"]
mod parser_library;
#[path = "../showcase_calculator.rs"]
mod showcase_calculator;
#[path = "../telescope_roles_compile.rs"]
mod telescope_roles_compile;
