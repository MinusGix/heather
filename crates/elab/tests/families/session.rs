//! The `session` family: Sessions, semantic images, the kernel pool, instrumentation and diagnostics.
//! One binary for these files instead of one each, so a Rust edit relinks the
//! compiler once for all of them; the runner still runs every member in a
//! process of its own, under its own rails and timing row
//! (docs/infrastructure/elab-test-families-design.md).

#[path = "../support/mod.rs"]
mod support;

#[path = "../semantic_image.rs"]
mod semantic_image;
#[path = "../semantic_test_support.rs"]
mod semantic_test_support;
#[path = "../slice_replay.rs"]
mod slice_replay;
#[path = "../session_transaction.rs"]
mod session_transaction;
#[path = "../determinism.rs"]
mod determinism;
#[path = "../kernel_pool.rs"]
mod kernel_pool;
#[path = "../instrumentation.rs"]
mod instrumentation;
#[path = "../obligation_records.rs"]
mod obligation_records;
#[path = "../axiom_provenance.rs"]
mod axiom_provenance;
#[path = "../template_registration.rs"]
mod template_registration;
#[path = "../modules.rs"]
mod modules;
#[path = "../owner_siblings.rs"]
mod owner_siblings;
#[path = "../warnings.rs"]
mod warnings;
#[path = "../check_diagnostics.rs"]
mod check_diagnostics;
#[path = "../check_reports_mismatch.rs"]
mod check_reports_mismatch;
#[path = "../display_surface.rs"]
mod display_surface;
