//! The `matching` family: Pattern matching, motives, decision procedures and equation checking.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/infrastructure/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../match_equation_split.rs"]
mod match_equation_split;
#[path = "../match_recursion.rs"]
mod match_recursion;
#[path = "../nested_match_patterns.rs"]
mod nested_match_patterns;
#[path = "../named_patterns.rs"]
mod named_patterns;
#[path = "../positional_if_let.rs"]
mod positional_if_let;
#[path = "../motives.rs"]
mod motives;
#[path = "../motive_synth.rs"]
mod motive_synth;
#[path = "../ih_generalization.rs"]
mod ih_generalization;
#[path = "../match_refines_hypotheses.rs"]
mod match_refines_hypotheses;
#[path = "../decidable_if.rs"]
mod decidable_if;
#[path = "../decidable_equation_carrier.rs"]
mod decidable_equation_carrier;
#[path = "../decide_combinator.rs"]
mod decide_combinator;
#[path = "../auto_refl.rs"]
mod auto_refl;
#[path = "../congruence_lgg.rs"]
mod congruence_lgg;
#[path = "../equality_endpoint_checking.rs"]
mod equality_endpoint_checking;
