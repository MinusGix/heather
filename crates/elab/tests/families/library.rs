//! The `lib_*` family: the standard library's modules, each checked by the
//! member file that names it. One binary instead of one per file, so a Rust
//! edit relinks the compiler once for all of them
//! (docs/infrastructure/elab-test-families-design.md). The runner still runs each member in
//! a process of its own (`scripts/run-test-targets.mjs`, family sharding), so
//! members keep their own rails, fixtures and timing rows.

#[path = "../support/mod.rs"]
mod support;

#[path = "../coinduction_probe.rs"]
mod coinduction_probe;
#[path = "../codata.rs"]
mod codata;
#[path = "../codata_indexed.rs"]
mod codata_indexed;
#[path = "../lib_algebra.rs"]
mod lib_algebra;
#[path = "../lib_kernel_model_reduction.rs"]
mod lib_kernel_model_reduction;
#[path = "../lib_setoid_mergeable.rs"]
mod lib_setoid_mergeable;
#[path = "../lib_std_bitvec.rs"]
mod lib_std_bitvec;
#[path = "../lib_std_bounded_list.rs"]
mod lib_std_bounded_list;
#[path = "../lib_std_coitree.rs"]
mod lib_std_coitree;
#[path = "../lib_std_coitree_bridge.rs"]
mod lib_std_coitree_bridge;
#[path = "../lib_std_coitree_eutt.rs"]
mod lib_std_coitree_eutt;
#[path = "../lib_std_creal.rs"]
mod lib_std_creal;
#[path = "../lib_std_evidence.rs"]
mod lib_std_evidence;
#[path = "../lib_std_float.rs"]
mod lib_std_float;
#[path = "../lib_std_itree.rs"]
mod lib_std_itree;
#[path = "../lib_std_itree_trace.rs"]
mod lib_std_itree_trace;
#[path = "../lib_std_itree_sim.rs"]
mod lib_std_itree_sim;
#[path = "../lib_std_int.rs"]
mod lib_std_int;
#[path = "../lib_std_list.rs"]
mod lib_std_list;
#[path = "../lib_std_memory.rs"]
mod lib_std_memory;
#[path = "../lib_std_ordered_field.rs"]
mod lib_std_ordered_field;
#[path = "../lib_std_rat.rs"]
mod lib_std_rat;
#[path = "../lib_std_relation.rs"]
mod lib_std_relation;
#[path = "../lib_std_ring.rs"]
mod lib_std_ring;
#[path = "../lib_std_semiring.rs"]
mod lib_std_semiring;
#[path = "../pos_binder_sugar.rs"]
mod pos_binder_sugar;
#[path = "../lib_std_string.rs"]
mod lib_std_string;
#[path = "../lib_std_tree.rs"]
mod lib_std_tree;
#[path = "../lib_std_utf8.rs"]
mod lib_std_utf8;
