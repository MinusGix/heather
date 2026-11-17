---
title: Certified bitvector decisions: bit-blast, external SAT, kerneltime LRAT check
status: open
labels: [proofs,solver,bitvec,x86,design,research]
area: tactics
created: 2026-09-24
updated: 2026-11-16
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
  RAT Verification*, CADE 2017 — `docs/papers/1612.02353.pdf` (the LRAT format).
- Szeider, *Streaming LRAT Certificates into Lean Theorems* (2026) —
  `docs/papers/2607.00815.pdf` (a resumable, streaming checker in Lean core).

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

- 2026-10-25: Second customer, from `docs/surveys/multi-width-bitvector-survey.md` §5 (Bhat et al., OOPSLA 2026, `docs/papers/3839511.pdf`). A multi-width claim bounded by a global width o (all widths below 65, say) reduces to one QF_BV query at width o by masks, instead of o^k queries, one per width assignment. The reduction's correctness (the paper's Lemma 4.2) is a structural induction that Heather can prove once, where the paper trusts an unverified translator. What remains is exactly this issue's decision. Rung B of [[bitvec-width-generic-decision]] (k-induction over transducers) also needs it. Benchmarks for the first round should include a wide, mask-heavy query.
- 2026-11-05: gardener: cites a file it shares with [[function-ir-narrow-arithmetic]] (`docs/surveys/multi-width-bitvector-survey.md`).
- 2026-11-16: first round done. `lib/std/tactic/lrat.hthr` is the checker
  (literals as `2v`/`2v + 1`, the clause database a `NatMap` keyed by id,
  reverse unit propagation along the hints, no deletions) with its soundness
  proof: `refuted` says that once `check(formula_of(cs), steps) = True`,
  every valuation makes some clause of `cs` false. Probes in
  `lib/_tests/std/tactic/lrat_tests.hthr`, written by `scripts/lrat-probes`
  (Tseitin miters of `a + b ≠ b + a` and `a * b ≠ b * a`, a small untrusted
  CDCL solver in Python, since a vendored solver could not be built here).
  What the measurements say:
  - **Cost is linear in the hinted literals.** Each one is a variable lookup
    in the assignment's `NatMap` (logarithmic in the variable count), each
    unit an insertion, each hint a lookup by id (logarithmic in the id).
    Walking lists and `NatMap` nodes dominates; nothing is quadratic. A
    resolution-chain format over sorted clauses was measured too and costs
    the same, so the checker stays plain LRAT: no representation change.
  - **One `refl` holds a few hundred hints** before the conversion budget, so
    a proof is cut into stage theorems: `adds(f_k, chunk) = True` per stage,
    `add_all` naming the formula a stage leaves, `check` on the last, and
    `adds_sound` chaining them. Stages are cut by hinted literals, not by
    steps (learned clauses grow), and check in parallel on the kernel's
    workers.
  - **The formula must be a literal map**, not `formula_of(list)`: building
    it costs a large fraction of a stage, and every stage would rebuild it.
    For the same reason every few stages leave their formula as a literal
    checkpoint (`f_k_is: add_all(f_{k-1}, c_k) = f_k` by `refl`), else the
    replayed insertions grow with the stage's index and late stages run out.
  - 8-bit addition commutes: 655 steps, tens of thousands of hints, 83 stages;
    the whole refutation checks in seconds of wall time on eight workers.
  Next, in order: (1) a host request that runs an untrusted solver and
  returns LRAT; (2) a bit-blaster written in Heather, from `BitVec`
  expressions to a circuit to CNF, proved once (a valuation of the words
  satisfies the clauses), so `refuted` turns into the bitvector identity;
  (3) the tactic, which must emit the stages as declarations of their own;
  (4) the UTF-8 word-to-spec bridges in `examples/utf8/utf8_check.hthr` as
  the first customer.
- 2026-11-16: the solver is CaDiCaL (Minus chose it after the evaluation in
  the levers thread: native LRAT for every technique, MIT, maintained, what
  Lean's `bv_decide` runs). Vendored unedited as `vendor/cadical` (release
  3.0.1), compiled by `crates/sat` (`heather-sat`), which collects the proof
  in memory through CaDiCaL's tracer, trims it to what the empty clause
  depends on and renumbers it into the formula's own numbering;
  `heather sat <file.cnf>` prints it, and `scripts/lrat-probes` uses it by
  default. Its proofs are far shorter than the naive solver's on adders
  (8-bit addition commuting: a few stages instead of 83) and comparable on
  multipliers, which stay hard for any SAT solver. Gotcha: the tracer's ids
  for the input clauses skip where the input has units, so `heather-sat`
  maps them by the order and contents of the clauses reported, never by id.
