//! Reusable driver pieces shared by the CLI, benchmarks and future resident
//! consumers. Import discovery and semantic module replay live here so each
//! command does not grow its own subtly different module walk.
//!
//! `heather` is a binary, and the loader was a private module of it until the
//! frontend benchmark corpus needed the *same* closure the CLI computes
//! (`crates/elab/benches/frontend/fixtures/corpus.rs`). It had been carrying
//! a hand-written list of `lib/certgen/ir_v1.hthr`'s imports instead, which drifted
//! the day `lib/std/core/bool.hthr` gained `import logic;`
//! (issues/frontend-bench-ir-closure-stale.md): the closure no longer
//! satisfied its own imports, every module of it failed, and the corpus timed
//! an elaborator that was not doing the work.
//!
//! A second implementation of "which files does this root pull in" would have
//! drifted again, so the answer is that there is one implementation and the
//! bench links it. That is why this crate has a `lib` target at all; nothing
//! else here is meant to be a public API.

pub mod loader;
pub mod semantic;
// The showcase manifest is here for the same reason the loader is: four
// consumers each carried their own copy of "which showcase, over which `-L`
// dirs", and a second implementation is what drifts
// (issues/showcase-harness.md).
pub mod showcase;
