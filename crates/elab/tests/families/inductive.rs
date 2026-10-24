//! The `inductive` family: the tier-0, tier-1 and tier-2 inductive schemas.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../inductive_tier0.rs"]
mod inductive_tier0;
#[path = "../inductive_tier1.rs"]
mod inductive_tier1;
#[path = "../inductive_tier2.rs"]
mod inductive_tier2;
#[path = "../tier1_fording.rs"]
mod tier1_fording;
#[path = "../tier1_list_proofs.rs"]
mod tier1_list_proofs;
