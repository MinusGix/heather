---
title: Ownership/linearity as certified static analyses over reflected code, never in the kernel
status: open
labels: [compiler,design,runtime,metaprogramming]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-08-11
updated: 2026-11-09
---

Direction, user-stated 2026-08-11 (explicitly still very much theoretical): a Rust-like ownership model for a subset of Heather so that fast, low-level, memory-safe code WITH mathematical proofs is excellent to write; linear types and similar disciplines by the same route.

The structural claim, from the same discussion: this never has to enter the type theory. An ownership/linearity discipline is a DECIDABLE SYNTACTIC JUDGMENT over reflected code — an ordinary Bool/Prop-valued function over an ElabCode-style AST ([[elabcode-abstraction-layer]]) — plus ONE soundness theorem proved against the runtime memory model that [[datarepr-separation]] will define: well-owned programs do not alias/leak/double-free under the runtime representation's semantics. Compilation passes then CONSUME ownership certificates exactly as mul consumes add's convergence certificate; a program's borrow-check run is a certificate, the informal soundness argument of a Rust-style checker becomes a theorem, and the kernel never learns the word ownership. Same Prop-laws/Bool-checkers/certificates-between pattern as [[class-ops-prop-vs-bool]].

Prerequisites, all owned elsewhere: the reflected-AST layer (elabcode-abstraction-layer), the runtime memory model (datarepr-separation), and the certificate-composition machinery that already exists (certifying-generator's kit). Unscheduled; filed so the ambition is written rather than assumed, per the repo's convention for direction issues.

## Log

- 2026-10-31: 2026-10-31: Round R12 of docs/compiler-milestones-proposal.md (§4.3), milestone nh-ownership: the second runtime fn setup ([[runtime-fn-setups-design]]). Minus leans toward it (2026-10-31): talking about things in a Rust-like way would make translating Rust code easier, and the lower-level control is powerful. The choice is confirmed when the round starts. Constant time (docs/constant-time-survey.md) is the cheaper alternative if a setup is wanted before [[native-heap-arena]].
- 2026-10-31: 2026-10-31: Requirement from item 6 of the fundamental-improvements memo (https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): the ownership judgment should produce the uniqueness facts that in-place update of let mut arrays and records needs, so the sequencing surface's pure updates (docs/sequencing-surface-design.md §8.2: let mut xs; xs.push(b); xs[i] := v) compile in place with no run-time reference count, and the runtime fn certificate states agreement with the pure function.
- 2026-10-31: 2026-10-31: `docs/runtime-fn-setups-design.md` §11 checks the setup record against this setup: after R3 a body has no mutation, so ownership over `rt` is a uniqueness judgment over SSA versions (a consumed version is not used again; borrows are non-consuming uses), its lowering updates buffers in place where the default copies, and its `sound` can reuse the default's cases. Same `rt`, stricter `judge`, its own `lower` and `sound`.
- 2026-11-05: gardener: cites a file it shares with [[native-constant-time]] (`docs/constant-time-survey.md`); [[native-secret-erasure]] (`docs/constant-time-survey.md`).
- 2026-11-09: 2026-11-09: the composable resource the setup needs (exclusive ownership of a footprint, split and rejoined across a borrow) is filed as [[separation-algebra-ownership]] (docs/native-mathematics-survey.md §7).
