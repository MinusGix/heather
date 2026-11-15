//! The `literals` family: Natural-number arithmetic, literals of every kind, and the in-language list functions.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/infrastructure/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../nat_arith.rs"]
mod nat_arith;
#[path = "../nat_order.rs"]
mod nat_order;
#[path = "../nat_parity.rs"]
mod nat_parity;
#[path = "../nat_run_primitives.rs"]
mod nat_run_primitives;
#[path = "../nat_suite.rs"]
mod nat_suite;
#[path = "../large_nat_literals.rs"]
mod large_nat_literals;
#[path = "../radix_numerals.rs"]
mod radix_numerals;
#[path = "../carrier_numerals.rs"]
mod carrier_numerals;
#[path = "../char_string_literals.rs"]
mod char_string_literals;
#[path = "../list_literals.rs"]
mod list_literals;
#[path = "../in_language_fold.rs"]
mod in_language_fold;
#[path = "../in_language_map.rs"]
mod in_language_map;
#[path = "../in_language_nth.rs"]
mod in_language_nth;
#[path = "../in_language_tabulate.rs"]
mod in_language_tabulate;
