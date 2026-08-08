---
title: Benchmark suite for the frontend (parse, elaborate, full-file check)
status: closed
labels: [frontend,elaboration,performance,tooling]
created: 2026-07-27
updated: 2026-08-08
---

Companion to [[kernel-benchmarks]], separate because the questions differ:
the kernel's cost model must stay simple and predictable; the elaborator is
*allowed* to be clever, so what its benchmarks guard is user-facing latency —
time from source file to checked declarations — and how it scales with file
size, meta count, and generated-term volume.

## What this issue owns

Designing the frontend benchmark suite: harness, fixtures, and the latency
budget worth alarming on. Not any particular speedup.

## Design questions

- **Fixtures.** The stress-proof suite files are the natural corpus — real
  proofs, already maintained, already exercising the unifier, the inductive
  compiler and the container schemas. Plus a generated-scale fixture (many
  declarations, wide inductives) so growth is measured, not just the suite's
  current size.
- **What to time.** End-to-end per file, but also split parse / elaborate /
  kernel-check, so a regression names its layer. The kernel-check split
  overlaps [[kernel-benchmarks]] deliberately — same number, different
  question (there: cost model; here: how much of user latency it is).
- **Where it runs.** Wants [[cli-check-diagnostics]]: once a file can be
  checked from the CLI, "time the CLI on the corpus" is the whole harness,
  which is one more reason that issue is scheduled first.
- **Unifier pathology.** [[elab-unifier-completeness]] owns postponement;
  assumed here only that meta-heavy files exist to measure. A fixture that
  provokes retry/postponement behavior keeps quadratic blowups visible.

## Log

- 2026-08-04: Trigger noted from the 2b-generator round (2026-08-04): doc §14.2's μ-inlining cost is now measurable — indexed_route_2b_gen.rs is the slowest elab test binary (~2.6 s / 17 tests; μ appears in the family type, twice per Σ projection, several times per arm, multiplied when a forded type appears inside another type). When this suite exists, a forded-family fixture belongs in it, and the recorded fix (a kernel def) gets its number here.
- 2026-08-04: Second trigger from the form-A round (2026-08-04): fording doc §14.9 — a branching form-A arm at a three-constructor declared index exceeds DEFAULT_FUEL in conversion (one child_projection per child + one tag predicate per other constructor, each a whole elim_Wf, inlined per use; checks at 2× fuel). Pinned as a deliberate negative in indexed_route_2b_declared.rs. Same lever as the μ-inlining entry above: a kernel def for generated terms retires both, and this suite is where 'retired' gets its number.
- 2026-08-04: The suite exists (phase 1 of two): scripts/bench-frontend over crates/elab/benches/frontend/, baseline at crates/elab/benches/baseline.tsv, docs/frontend-benchmarking.md. In-process rather than 'time the CLI on the corpus' as this issue proposed, because the parse/elaborate/kernel-gate split needs instrumentation inside the elaborator (crates/elab/src/stats.rs) — the CLI's shape is kept as the corpus family's unit of work (a fresh prelude'd elaborator per file, exactly crates/cli/src/main.rs). Nine families; three of them the forded ones the 2026-08-04 triggers asked for. Measured, day one (recorded baseline; three full runs agreed on the exponents to <=0.25 while the absolute times moved up to 1.5x with machine load): forded/computed-arms slope 3.39 (31 ms at 2 arms to 1.25 s at 6), forded/declared-index-tags slope 2.65 (18 ms to 328 ms as the *index* type gains constructors), forded/occurrences ~119 ms per use. Both superlinear bands record the defect, not the design, per docs/benchmarking.md's rule. And the split answered the question this issue guessed at: on lib/ir_v1.hthr the wait is 0.0% parse / 1.2% elaborate / 98.8% kernel gate (on lib/vec_code.hthr, 10.6 / 49.3 / 40.2) — so elaborator optimization aimed at the heavy file would be aimed at 1% of it, and the leverage is entirely in what the elaborator emits. Latency budget: lib/ir_v1.hthr at 150 s (59 s measured through the release CLI quiet, 67-88 s from the harness depending on load), checked with or without a baseline. Residue for phase 2 and for whoever re-records on a quiet machine is in docs/frontend-benchmarking.md.
- 2026-08-04: Scope complete (managed round): harness (crates/elab/benches/frontend, scripts/bench-frontend, baseline.tsv), nine fixture families with the phase split and exponent bands, latency budgets gated in --check, docs/frontend-benchmarking.md. The split question this issue asked is answered: ir_v1.hthr is 0.0/1.2/98.8 parse/elab/kernel — user latency on heavy files IS kernel-gate time on oversized generated terms. Closing: the residue (the def round that re-records the forded bands) is owned by [[generated-term-defs]]; the 2026-08-04 baseline is ~1.3–1.5× pessimistic on absolutes (loaded machine), re-record quiet before trusting budgets tightly.
- 2026-08-08: Stale-baseline finding (2026-08-08, named-upcast round): scripts/bench-frontend --check reports corpus/prelude:build 91.5 µs -> 151.4 µs and corpus/prelude:clone 300 ns -> 410 ns as regressions, REPRODUCED ON THE CLEAN TREE (stashed working copy), so they are not that round's — and ir_v1.hthr:decls and meta/nested-inference 'improved' 0.68x/0.63x in the same run, which together read as a baseline recorded under different machine conditions. Wants a deliberate re-record of baseline.tsv on an idle machine (per docs/frontend-benchmarking.md's discipline), not a silent one from inside an unrelated round.
