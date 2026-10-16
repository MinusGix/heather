//! The `lib_*` family: the standard library's modules, each checked by the
//! member file that names it. One binary instead of one per file, so a Rust
//! edit relinks the compiler once for all of them
//! (docs/elab-test-families-design.md). The runner still runs each member in
//! a process of its own (`scripts/run-test-targets.mjs`, family sharding), so
//! members keep their own rails, fixtures and timing rows.

#[path = "../support/mod.rs"]
mod support;

#[path = "../lib_algebra.rs"]
mod lib_algebra;
#[path = "../lib_list_algos.rs"]
mod lib_list_algos;
#[path = "../lib_setoid_mergeable.rs"]
mod lib_setoid_mergeable;
#[path = "../lib_std_bitvec.rs"]
mod lib_std_bitvec;
#[path = "../lib_std_bounded_list.rs"]
mod lib_std_bounded_list;
#[path = "../lib_std_creal.rs"]
mod lib_std_creal;
#[path = "../lib_std_certified_lookup.rs"]
mod lib_std_certified_lookup;
#[path = "../lib_std_evidence.rs"]
mod lib_std_evidence;
#[path = "../lib_std_int.rs"]
mod lib_std_int;
#[path = "../lib_std_list.rs"]
mod lib_std_list;
#[path = "../lib_std_location.rs"]
mod lib_std_location;
#[path = "../lib_std_order.rs"]
mod lib_std_order;
#[path = "../lib_std_rat.rs"]
mod lib_std_rat;
#[path = "../lib_std_relation.rs"]
mod lib_std_relation;
#[path = "../lib_std_ring.rs"]
mod lib_std_ring;
#[path = "../pos_binder_sugar.rs"]
mod pos_binder_sugar;
#[path = "../lib_std_string.rs"]
mod lib_std_string;
#[path = "../lib_std_tree.rs"]
mod lib_std_tree;
#[path = "../lib_std_utf8.rs"]
mod lib_std_utf8;
