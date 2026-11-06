//! Populate or safely replay the parser and calculator-showcase semantic test
//! prefix in resource-bounded processes before the `family_logic` members
//! that consume it (`parser_library`, `showcase_calculator`) run.
//!
//! Cold, that prefix (the omega prefix, grind's closure, the parser library,
//! the showcase) cost each consumer most of its CPU rail before its own tests
//! started, and under the suite's load `parser_library` died at it
//! (issues/elab-showcase-members-cold-rail.md). `scripts/test` runs each
//! stage below in a process of its own (`--exact`), in order, so a stage
//! builds only its own slice and replays the ones before it: images are keyed
//! by a module's source and its closure, not by the list that loaded it. In
//! the parallel phase the whole target runs again in one process, as a replay.

mod support;

use support::parser;

fn ready(modules: &[(&str, &str)]) {
    // Serial gate, as the consumers check it (`showcase_calculator::base`).
    support::semantic_test_base_with(modules, |e| e.set_kernel_workers(1));
}

#[test]
fn stage_1_omega_prefix_is_ready() {
    ready(parser::std_through("omega"));
}

#[test]
fn stage_2_grind_prefix_is_ready() {
    ready(parser::STD);
}

#[test]
fn stage_3_parser_library_is_ready() {
    ready(&parser::library_prefix());
}

#[test]
fn stage_4_showcase_is_ready() {
    ready(&parser::showcase_prefix());
}
