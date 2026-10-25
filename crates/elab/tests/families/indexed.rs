//! The `indexed` family: Indexed and branching inductive families, and containers.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).


#[path = "../support/mod.rs"]
mod support;

#[path = "../indexed_declared_families.rs"]
mod indexed_declared_families;
#[path = "../indexed_declared_index.rs"]
mod indexed_declared_index;
#[path = "../indexed_families.rs"]
mod indexed_families;
#[path = "../indexed_route1.rs"]
mod indexed_route1;
#[path = "../indexed_route_2b_declared.rs"]
mod indexed_route_2b_declared;
#[path = "../indexed_route_2b_gen.rs"]
mod indexed_route_2b_gen;
#[path = "../iwf_match_tiers.rs"]
mod iwf_match_tiers;
#[path = "../iwf_infinitary.rs"]
mod iwf_infinitary;
#[path = "../iwf_no_confusion.rs"]
mod iwf_no_confusion;
#[path = "../branching_route_a.rs"]
mod branching_route_a;
#[path = "../branching_route_c.rs"]
mod branching_route_c;
#[path = "../branching_route_c_nary.rs"]
mod branching_route_c_nary;
#[path = "../container_fields.rs"]
mod container_fields;
#[path = "../container_proofs.rs"]
mod container_proofs;
#[path = "../container_recursion.rs"]
mod container_recursion;
#[path = "../mutual_inductive.rs"]
mod mutual_inductive;
