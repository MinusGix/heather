---
title: Build a checked Heather-side API for declarations and proof construction
status: open
labels: [metaprogramming,elaboration,proofs,design]
area: tactics
milestone: [tac-host-interface]
created: 2026-09-08
updated: 2026-09-08
---

The reusable x86 callee round (`cb877f2`) still assembles scoped names, dependent
applications, intermediate equalities, and proof bodies in Rust. Structured
emission helps, but expression leaves and references can still be strings.
A Heather generator should be able to construct a small checked declaration
group and publish it in the caller's scope, with useful errors at construction.

## Acceptance

- Choose one bounded customer from `crates/cli/src/native/calls.rs`: a successor
  witness, frame-preservation lemma, or trace-composition declaration group.
- Design typed/scoped references, binders, applications, expected-type checking,
  and named intermediate facts without resolved-name string round trips.
- Preserve hygiene and source provenance; explain how a group refers to earlier
  declarations and how failed construction avoids partial publication.
- Separate pure code construction from host checking/publication capabilities.
  Initial host implementation may remain Rust; clients should be Heather code.
- Kernel-check all output. Construction typing does not by itself establish
  source-semantic preservation, and a generator's correctness is a separate proof.
- Exercise open types, neutral arguments, dependent binders, and malformed output.
- Compare the small customer with its current Rust producer before planning a
  wholesale migration. API shape and implementation sequence remain open.

## What it assumes from elsewhere

- [[host-elaboration-interface]] owns access to the active compiler and environment.
- [[scoped-declaration-generators]] owns invocation and scope publication.
- [[generators-in-the-language]] owns the broader migration.
