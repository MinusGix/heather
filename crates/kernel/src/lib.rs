//! The Heather kernel: trusted checker for DeLaM (dependent layered modal
//! type theory). Correctness over performance; mirrors the structure of the
//! Coq formalization and of docs/delam/04–06, so divergences stay auditable.
//! See DESIGN.md for the v0 scope and representation decisions.
//!
//! Nothing outside this crate is trusted. The compiler, elaborator, and any
//! code-analysis functions produce terms/proofs that this crate re-checks.

mod bounds;
pub mod conv;
pub mod eval;
pub mod fmt;
pub mod layer;
pub mod level;
mod rec;
pub mod reduce;
pub mod subst;
pub mod term;
pub mod typing;
pub mod value;
