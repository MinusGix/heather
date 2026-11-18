---
title: Some modules' semantic images are refused on every replay and re-elaborated
status: open
labels: [cache, module-image, performance]
area: infrastructure
created: 2026-11-18
updated: 2026-11-18
---

Found 2026-11-18 while re-elaborating the whole library cold
(`heather check --cache --expectations --build-jobs 4 --world lib lib`, a
fresh store) for the tactic-runs-on-the-machine round
([[runtime-generator-link-cost]]). Six modules' images were written and then
refused by the decoder when the same run replayed them, so each was
elaborated again:

- `invalid module-image structure: duplicate designed access path`
  (`crates/elab/src/module_image.rs`, the `DeltaEvent::Access` check):
  `bitvec_omega_tests`, `continuous_time_tests`,
  `imperative_statements_tests`, `runtime_held_for_tests`,
  `runtime_lifted_loops_tests`.
- `invalid module-image structure: slices do not partition the delta`:
  `constructor_equation_tests`.

Not caused by that round: master's binary does the same. To reproduce, twice
over one empty store:

    heather check --limits dev --cache --cache-dir /tmp/st --expectations --world lib \
        lib/_tests/std/tactic/bitvec_omega_tests.hthr

The second run says `stored module bitvec_omega_tests is unusable … — rebuilding`
and elaborates the module again; only its kernel verdicts come from the
store.

So a warm run never replays these modules, and every importer pays their
elaboration. Either the encoder writes a delta the decoder's invariants do
not admit (an access path designed twice, which the module may legitimately
do, or the decoder's check is too strict), or elaboration really designs one
twice and the encoder should refuse to write it. The first question is
which `designed` path repeats in `bitvec_omega_tests`.
