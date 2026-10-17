//! Populate or safely replay the per-file command's semantic test prefix
//! (support/command_prefix.rs) before `command_process` and
//! `command_refusals` replay it. scripts/test runs each test here in a
//! process of its own, filter half first: cold, the whole list is more than
//! one CPU rail.

mod support;
#[path = "support/command_prefix.rs"]
mod command_prefix;

use command_prefix::{COMMAND_PREFIX, filter_half};

#[test]
fn filter_half_is_ready() {
    support::semantic_test_base(filter_half());
}

#[test]
fn command_prefix_is_ready() {
    support::semantic_test_base(COMMAND_PREFIX);
}
