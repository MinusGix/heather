---
title: A single small-step reduction can overflow the native stack
status: closed
labels: [kernel,totality]
created: 2026-09-25
updated: 2026-09-25
---

`heather check` aborted with a native stack overflow on
`theorem a(x: Nat, h: x < 5): x < Nat::pow(3, 5000) { omega }` (and on any
body the elaborator checks against that expected type through
`ctor_here_expected`). It failed at 5079abcc and every commit before the fix.

Backtrace: `SemanticOracle::whnf_type` → `reduce::whnf_type_delta` →
`step_type_delta` → about 2,000 nested `step_term_delta` frames. The value
machine had already answered "stuck". The reducer was only spelling the
reduct under a small step budget, but one step recursed once per blocked head,
and δ-unfolding `pow` nests one per level of the exponent. Fuel counts steps,
so it never saw this.

## Scope

Put the small-step reducer under [[kernel-native-depth-budget]]'s
`NATIVE_DEPTH_LIMIT`, reporting `OutOfFuel`, with the same verdict-neutral
policy.

## Acceptance

- The repro and its `sorry`-shaped sibling report ordinary errors, not an
  abort.
- A kernel test: a step whose redex sits below the limit's worth of blocked
  heads answers `OutOfFuel`, and one just inside it still steps.
- Verdicts unchanged elsewhere: the full suite and `scripts/bench --check`.

## Log

- 2026-09-25: Landed. `reduce.rs` keeps a private `Frames` account per public step,
  against `NATIVE_DEPTH_LIMIT`. Past it a step marks itself exhausted, and the
  public entry points answer `Err(OutOfFuel)`; they now return
  `Result<Option<_>, OutOfFuel>`, so exhaustion never reads as "no rule
  applies". Callers propagate the error (`whnf_*`, `eval`, conversion's
  syntactic domain) or were already best-effort (the oracle's reducts and
  diagnostics, `inductive`'s decoded view). Kernel tests keep their `Option`
  assertions through a local shim that fails loudly on exhaustion. The new
  kernel test is `a_step_below_the_frame_budget_is_out_of_fuel`.

  The repro now reports omega's ordinary "stuck", and the `sorry` variant
  "unbound name". Every other probe's verdict matches the old binary. The full
  suite is green, and `scripts/bench --check` has all 112 comparisons within
  thresholds. Design note: docs/native-depth-budget-design.md §7.
