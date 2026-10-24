//! The `x86` family: the x86 model, the representation generators, and the frozen
//! `ir_v1` corpus.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../x86_64.rs"]
mod x86_64;
#[path = "../datarepr.rs"]
mod datarepr;
#[path = "../repr_access.rs"]
mod repr_access;
#[path = "../reprgen.rs"]
mod reprgen;
#[path = "../el_reader_audit.rs"]
mod el_reader_audit;
#[path = "../ir_v1.rs"]
mod ir_v1;
