//! The Heather kernel: trusted checker for DeLaM (dependent layered modal
//! type theory). Correctness over performance; mirrors the structure of the
//! Coq formalization and of docs/delam/04–06, so divergences stay auditable.
//! See DESIGN.md for the v0 scope and representation decisions.
//!
//! Nothing outside this crate is trusted. The compiler, elaborator, and any
//! code-analysis functions produce terms/proofs that this crate re-checks.

mod fmt;
pub mod layer;
pub mod level;
pub mod subst;
pub mod term;
