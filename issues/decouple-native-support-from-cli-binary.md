---
title: Decouple native proof support from the core CLI binary
status: open
labels: [compiler,x86,architecture,performance]
area: heather-in-heather
code: crates/cli/src/native/support.rs:2 @ e7870e2
created: 2026-09-21
updated: 2026-09-21
---

The native commands compile 34 Heather library modules (the closure of `function_ir_compile` since B2) into the `heather`
binary with `include_str!`. This makes their source bytes part of the Rust
compilation unit: editing any bundled file under `lib/` recompiles
`heather-cli` and relinks the core `heather` executable before Heather can
check the edit. It also puts a large, native-backend-specific proof corpus in
the general CLI binary even when the invocation is only `heather check`.

Move this corpus behind a boundary that is not a Rust dependency of the core
binary. The likely shapes are a runtime library/data directory, a separately
built support artifact, or an optional native component; choose among them
against installation and standalone-use requirements rather than preserving
embedding by accident. Do not merely move the same `include_str!` table into a
shared crate: that retains both the rebuild edge and the core-binary payload.

The logical boundary must remain at least as strong as today's. Native
compilation must use one coherent support corpus, elaborate or safely replay
it, kernel-check the generated certificate, and prevent a user's import path
from silently substituting a different module for one already used by the
certificate. Content-addressed semantic images and declaration verdicts may
cache that work; they should not require the source text itself to be compiled
into Rust.

## Acceptance

- An edit to a native support file under `lib/` does not cause
  `cargo build --bin heather` to recompile or relink the core binary.
- Plain checking does not carry or initialize the native support corpus.
- `build-x86` and `compile-x86` locate a version-coherent support corpus with
  an explicit, testable discovery rule and a useful missing-library error.
- The existing substituted-model/refusal controls continue to demonstrate
  that generated output was checked against exactly the support corpus the
  command selected.
- Packaging decides explicitly whether a lone copied binary supports native
  compilation; development-tree convenience must not silently define the
  installed layout.

## What it assumes from elsewhere

- **[[x86-native-export]]** owns the native command and certificate soundness
  boundary. Assumed here only: generated output continues to pass that same
  boundary after the support corpus moves.
- **[[semantic-module-images]]** owns content-addressed module replay. Assumed
  here only: a separately loaded support corpus may use its existing source
  and dependency identities rather than inventing another cache identity.

## Log

- 2026-09-21: Filed after observing that routine `lib/` edits rebuild
  `heather`. Decision for now is to defer implementation, but avoid treating
  the current embedding as the intended core architecture.
