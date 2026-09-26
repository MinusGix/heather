//! The `omega` family: Omega and the termination machinery that replays its library prefix.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;
#[path = "../omega_cases/mod.rs"]
mod omega_cases;

#[path = "../omega.rs"]
mod omega;
#[path = "../omega_div_mod.rs"]
mod omega_div_mod;
#[path = "../omega_div_mod_scaling.rs"]
mod omega_div_mod_scaling;
#[path = "../omega_logic.rs"]
mod omega_logic;
#[path = "../omega_measure_reduction.rs"]
mod omega_measure_reduction;
#[path = "../omega_reconstruction.rs"]
mod omega_reconstruction;
#[path = "../omega_wide_constants.rs"]
mod omega_wide_constants;
#[path = "../omega_relevance.rs"]
mod omega_relevance;
#[path = "../module_delta_omega_bench.rs"]
mod module_delta_omega_bench;
#[path = "../mutual_recursion.rs"]
mod mutual_recursion;
#[path = "../termination_measures.rs"]
mod termination_measures;
#[path = "../recursion_meaning.rs"]
mod recursion_meaning;
#[path = "../termination_local_evidence.rs"]
mod termination_local_evidence;
#[path = "../decreases_unfolding.rs"]
mod decreases_unfolding;
#[path = "../stable_termination_labels.rs"]
mod stable_termination_labels;
#[path = "../typed_termination_contexts.rs"]
mod typed_termination_contexts;
#[path = "../bv_omega.rs"]
mod bv_omega;
