---
title: Move library facts out of Rust tests and into the library
status: open
labels: [testing,library]
area: infrastructure
created: 2026-10-24
updated: 2026-10-24
---

The library-module test files (`crates/elab/tests/lib_*.rs`, `nat_*.rs`; 377
tests) mostly restate the library (`docs/test-value-audit.md` §3.2–3.5, the
owner of the classification and the policy in §5):

- about 25 "the module checks" tests, which exist because nothing else
  checks the module ([[library-whole-check-gate]]);
- 13 "the kit is there" name lists, kept up by hand beside the module;
- about 85 computation examples (`theorem … { refl }`) and restatements of
  library theorems at open arguments, written in Rust strings;
- about 100 bare refusals, most of them a false mathematical claim refused,
  which a `¬` theorem states better ([[refusal-tests-pin-their-reason]]
  owns the rest). Two are shown proved in the audit
  (`zeros_differ`, `halves_differ`).

Pure-library PRs keep adding these: between a sixth and a half of their
library lines again as test lines over the last forty merges.

## Proposal (per module, when the module is next touched, or as one sweep)

- A theorem a client would cite goes in the module. Probes at specific
  values (checking the concept at particular cases) and headline contract
  restatements go to `lib/_tests`, which mirrors `lib/` with `_tests` stems
  (`lib/_tests/std/num/float/arith_tests.hthr`). Nothing outside it may
  import from it, and its names stay out of the library and the export
  (Minus, 2026-10-24; doc §4.5).
- False-claim refusals become `¬` theorems, in the module or its examples
  module.
- Kit lists go. Module-check tests go once the gate lands.
- What stays in Rust: cost and route assertions, definitional-equality
  refusals that guard something (labelled), checker refusals with their
  reason, and kernel-refused mutation controls.

## What it assumes from elsewhere

- **[[library-whole-check-gate]]** owns checking every module. Assumed here:
  only that every `lib/_tests` module is checked as a root, and that
  importing from `lib/_tests` outside it is refused by a lint.

## Log

- 2026-10-24: Float modules done: four `lib/_tests/std/num/float/*_tests.hthr` probe modules, `Finite::zeros_differ` in float.hthr, and one Rust file (`lib_std_float.rs`) of vacuity refusals with reasons, in place of four Rust files. Closed-value refusals dropped where a probe pins the right value.
