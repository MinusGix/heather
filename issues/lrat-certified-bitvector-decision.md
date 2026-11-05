---
title: Certified bitvector decisions: bit-blast, external SAT, kerneltime LRAT check
status: open
labels: [proofs,solver,bitvec,x86,design,research]
area: tactics
created: 2026-09-24
updated: 2026-10-25
---

Build (or first cost) a **kerneltime decision procedure for bitvector goals
with certificates**: bit-blast to CNF, run an external SAT solver, and have
the kernel check an LRAT certificate with a checker proved sound once. This
is Lean's `bv_decide` design: generators need no verification, outputs
carry certificates, which is Heather's own stance applied to decision
procedures.

## Why now

- x86 proofs are dominated by bitvector facts (flags, carries, width
  arithmetic). CutSat ([[cutsat-linear-integer-arithmetic]]) covers linear
  arithmetic, not bit-level identities.
- The kernel already has native bitvector values (`Val::BitRun`) and
  accelerated folds, so evaluating a bit-blasted circuit on concrete
  assignments is cheap. The open question is the **checker's** kerneltime
  cost on real certificates, which is mostly list/array manipulation over
  clause ids.
- [[reflection-through-decide-instances]] (closed) settled that a fast
  procedure behind a `Decide` instance keeps one notion at proof sites. An
  LRAT-backed instance is the same shape with an external oracle.

## Reading

- Cruz-Filipe, Heule, Hunt, Kaufmann, Schneider-Kamp, *Efficient Certified
  RAT Verification*, CADE 2017 — `docs/1612.02353.pdf` (the LRAT format).
- Szeider, *Streaming LRAT Certificates into Lean Theorems* (2026) —
  `docs/2607.00815.pdf` (a resumable, streaming checker in Lean core).

## Acceptance (first round, investigation)

Hand-check one small unsatisfiable CNF's LRAT proof with an in-language
checker on a probe, measure how the kernel's cost grows with certificate
size (a shape, not a number), and identify what dominates: clause lookup,
unit propagation, or list rebuilding. Decide from that whether the checker
needs a representation change (arrays/maps with good kernel behaviour)
before a generator is worth writing.

## What it assumes from elsewhere

- **[[kernel-acceleration-policy]]** owns what the kernel may accelerate.
  Assumed here: only that a checker is ordinary library code; no kernel
  case for it.
- **[[decide-class]]** owns the `Decide` interface.

## Log

- 2026-10-25: Second customer, from `docs/multi-width-bitvector-survey.md` §5 (Bhat et al., OOPSLA 2026, `docs/3839511.pdf`). A multi-width claim bounded by a global width o (all widths below 65, say) reduces to one QF_BV query at width o by masks, instead of o^k queries, one per width assignment. The reduction's correctness (the paper's Lemma 4.2) is a structural induction that Heather can prove once, where the paper trusts an unverified translator. What remains is exactly this issue's decision. Rung B of [[bitvec-width-generic-decision]] (k-induction over transducers) also needs it. Benchmarks for the first round should include a wide, mask-heavy query.
- 2026-11-05: gardener: cites a file it shares with [[function-ir-narrow-arithmetic]] (`docs/multi-width-bitvector-survey.md`).
