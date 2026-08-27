---
title: Cache solver-proved sequents as persistent certified facts
status: open
labels: [proofs,elaboration,arithmetic,caching,design]
created: 2026-08-27
updated: 2026-08-27
---

Let untrusted solvers opportunistically persist useful proved sequents across
builds. An entry represents canonical premises and a conclusion together with
the compact data needed to reconstruct an ordinary Heather proof. Cache
contents are candidates only: every hit is reconstructed and checked through
the normal kernel boundary, so stale, corrupt, malicious, or solver-buggy data
can cause a miss/rejection but cannot establish a false theorem.

This is broader than memoizing one tactic. Omega, CutSat, future `linarith`,
nonlinear preprocessing, simplification, and `grind` should be able to
contribute and consume facts without depending on which solver discovered
them.

## Staged shape

1. **Exact canonical sequents.** Content-address the normalized domains,
   premises, and conclusion; store a versioned certificate recipe and required
   reconstruction lemmas. Exact lookup should not require the full index in
   memory.
2. **Unsatisfiable cores.** Store only reachable contradiction premises and
   retrieve a core when it is a subset of a later context. Keep the exact blob
   store separate from the inverted/subset index.
3. **Derived sequents.** Retain selected intermediate consequences under their
   actual premises, alpha-normalizing opaque atoms so locally discovered facts
   can become reusable parameterized lemmas.
4. **Conservative generalization.** A repeated family may suggest a symbolic
   theorem, but the generalized statement is a fresh proof obligation checked
   normally; concrete instances never justify an extrapolation by themselves.

Possible disk shapes include a content-addressed blob tree with a compact
prefix/Bloom rejection layer for exact keys, followed later by an inverted
constraint index (or an embedded transactional store) for core/subset queries.
The representation choice is owed by measurement, not fixed here.

## Safety and lifecycle rules

- Persist only positive, independently checkable artifacts: proof recipes,
  kernel-checked proof artifacts if that representation later exists, and
  models revalidated against every supported constraint.
- Never treat solver failure, timeout, resource exhaustion, or unsupported
  syntax as a mathematical cache result.
- Version canonicalization, certificate formats, reconstruction lemma
  interfaces, and relevant kernel/elaborator semantics.
- Bound opportunistic harvesting and track hits, saved reconstruction work,
  proof size, last use, and eviction value; affine consequence generation is
  otherwise effectively unbounded.
- Reproducible builds may benefit from a warm cache but never require one.
  Project-local and user-global stores need explicit policy and provenance.

## Acceptance for the first core

- A deterministic canonical sequent key is shared by at least two solver
  clients or by one solver and the arithmetic certificate materializer.
- Cold execution stores a compact recipe; a later process finds it without
  loading all keys and reconstructs it through the ordinary kernel gate.
- Corrupt blobs, version skew, hash/key mismatches, and mutated premises are
  rejected or treated as misses by tests.
- Telemetry demonstrates saved solver/reconstruction work separately from the
  unavoidable kernel validation cost.
- One ungated cold-path acceptance remains in the suite.

## Priority and triggers

Not an immediate prerequisite for complete Omega/CutSat. The nearer arithmetic
targets are direct reconstruction of terminal CutSat conflicts and economical
in-memory proof materialization. Reconsider the exact-sequent core when either
(a) repeated arithmetic certificates across declarations/builds become a
measured cost, (b) a second solver needs the same certificate store interface,
or (c) the in-memory canonical-sequent key from
[[arithmetic-certificate-dag-sharing]] is stable enough to persist without a
parallel representation.

## What it assumes from elsewhere

- **[[arithmetic-certificate-dag-sharing]]** owns scoped in-memory sharing and
  the first canonical arithmetic sequent/proof-node shape.
- **[[parallel-checking-and-caching]]** owns the existing declaration-cache
  trust/versioning precedent; this issue does not silently reuse declaration
  verdicts as theorem facts.
- **[[grind-port]]** owns whole-solver orchestration and decides when a general
  fact service becomes part of solver cooperation.
- **[[omega-performance-telemetry]]** owns arithmetic measurements that can
  trigger the first implementation slice.

