//! The `certgen` family: Certificate generation and the tier-0/tier-1 inductive schemas it certifies.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../certgen.rs"]
mod certgen;
#[path = "../certgen_cert.rs"]
mod certgen_cert;
#[path = "../certgen_controls.rs"]
mod certgen_controls;
#[path = "../certgen_emissions.rs"]
mod certgen_emissions;
#[path = "../certgen_nonnat.rs"]
mod certgen_nonnat;
#[path = "../certgen_route1_spike.rs"]
mod certgen_route1_spike;
#[path = "../certgen_t0param.rs"]
mod certgen_t0param;
#[path = "../certgen_tier1.rs"]
mod certgen_tier1;
#[path = "../inductive_tier0.rs"]
mod inductive_tier0;
#[path = "../inductive_tier1.rs"]
mod inductive_tier1;
#[path = "../tier1_fording.rs"]
mod tier1_fording;
#[path = "../tier1_list_proofs.rs"]
mod tier1_list_proofs;
