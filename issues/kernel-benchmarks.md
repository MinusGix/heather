---
title: Benchmark suite for the kernel (reduction, conversion, checking)
status: closed
labels: [kernel,performance,testing,tooling]
created: 2026-07-27
updated: 2026-11-20
---

Nothing measures kernel evaluation cost, and the design leans on it twice:
ordinary `fn`s *execute* by kernel computation, and `Compile` equiv proofs
are meant to discharge by conversion (a concrete IR value makes
`simulate ir` unfold). Both are claims about performance, and neither has a
number. [[numeral-stack-depth]] is the first place the gap showed
(~47 KB of stack per `Succ`), and it was found by accident, not by a bench.

The constraint that shapes this issue: the kernel stays a **simple trusted
basis** — the eventual bootstrap depends on it being small enough to trust
and re-check. So the answer to a slow benchmark is rarely "make the kernel
cleverer"; it is to know the cost model, keep it stable, and catch
regressions. Consistent measurement is the substitute for complexity.

## What this issue owns

Designing the benchmark suite: harness, fixtures, and what "regressed" means.
Not any particular optimization — a slow number files its own issue.

**Landed 2026-07-28** (see the log for the decisions): `scripts/bench` over
`crates/kernel/benches/kernel/`, baseline in
`crates/kernel/benches/baseline.tsv`, rationale and thresholds in
`docs/infrastructure/benchmarking.md`. The design questions below are answered there; they
are left as written so the log reads against them.

## Design questions

- **Harness.** Same discipline as `scripts/test`: whatever runs must sit
  under ulimit (a runaway normalization is exactly what benches provoke).
  Criterion vs. a plain timed harness; where numbers are recorded so runs
  are comparable across commits.
- **Fixtures.** Candidates: substitution on deep terms; whnf/normalization
  of numeral arithmetic at sizes beyond the current cap; conversion on the
  perturbed-pair generators that already exist in the property tests; `Wf`
  elimination at depth; checking the largest generated declarations the
  tier-1 lowering emits.
- **The thesis-shaped benchmark**, unwritable until [[ir-simulate-design]]
  lands but the reason this issue exists: conversion discharges
  `simulate ir fuel` against its result at realistic program size and fuel.
  When the IR exists, this fixture gets added here; until then the numeral
  and elimination fixtures are its proxies.
- **Scaling shape, not just points.** For fuel-like inputs the interesting
  output is the curve (linear? quadratic? stack-linear?), since unary `Nat`
  fuel makes everything at least linear in fuel by construction.

## What it assumes from elsewhere

- **[[numeral-stack-depth]]** owns the `Succ` stack cost and its fix.
  Assumed here: only that numerals are currently capped, so numeral fixtures
  must start under the cap and the bench should be what proves a fix lifted it.
- **[[ir-simulate-design]]** owns simulate's shape. Assumed here: only that
  it is fuel-indexed, so a fuel-scaling fixture will be meaningful.

## Log

- 2026-07-28: LANDED. Suite lives at crates/kernel/benches/kernel/ (bench target `kernel`, harness = false), run by scripts/bench, documented in docs/infrastructure/benchmarking.md. Design answers: (1) harness is first-party, not Criterion -- [[dependency-policy]]'s zero-dep rule covers dev-dependencies too, and what Criterion buys (bootstrapped CIs, outlier classification) targets small differences in noisy code, not the cost model of deterministic tree walks; ~250 lines of min-of-samples estimator does it. (2) numbers are recorded in-tree as crates/kernel/benches/baseline.tsv (TSV: greppable, diffable, parseable without a dependency; env rows tag host/cpu/profile/rustc/commit). (3) "regressed" = a case >=1.25x baseline (measured run-to-run spread here is 1-4%), or a fitted slope drifting >+0.35, or a slope leaving its declared band, or the stack probe losing >10% of its depth; times are compared only when host+profile match, slopes always -- the exponent is a property of the code, the time is a property of the machine. (4) scaling shape is the headline: 14 families each declare a work unit, and the log-log slope is fitted and gated, which is the machine-independent half of the suite.
- 2026-07-28: Fixtures (docs/infrastructure/benchmarking.md has the table): substitution on deep terms; numeral arithmetic well past the ~150 elaborate-path cap; conversion over the perturbed-pair generators from tests/conv_pair_properties.rs; Wf elimination at tree depth; the 45-branch code recursor, split into its fixed check cost (~0.54 ms) and its marginal per-code-node reduction cost; checker throughput over the generated corpus; plus a stack probe (subprocess bisection -- an overflow cannot be caught, only survived by someone else). Two rules the fixtures follow: setup is not timed, and every fixture validates before it is timed, because a fixture that stops doing its work gets FASTER and an unvalidated benchmark then reports a win for a bug. Not here, deliberately: checking the declarations tier-1 emits comes from elab, which a kernel bench cannot reach -- [[frontend-benchmarks]] owns it.
- 2026-07-28: First run found a defect, which is the point of the exercise: substitution deep-copies its payload three times even at depth zero, so one elim_Nat beta-step is linear in annotations it never reads (~150 ns/node) and `add n n` is QUADRATIC (slope 2.02; 230 ms at n=1024), as is conv on the same computation (2.20). Filed as [[subst-copies-payloads-at-depth-zero]] with nat/step-once as its isolating measurement -- this issue owns no optimizations. The three affected bands record today's exponent rather than the desired one, each with a comment naming the issue and the band it becomes when fixed: a permanently red gate is a gate nobody reads.
- 2026-07-28: Second finding, for [[numeral-stack-depth]]: the stack probe puts the kernel's check walk at 2.9 KiB/level in release (1414 levels in 4 MiB) and 53.9 KiB/level in debug (76 levels). Its ~47 KB/level headline is a dev-profile figure -- which is the profile scripts/test runs in, so it is the one that binds for tests, while a shipped checker pays 18x less. Logged there too. Closing: scope was the suite's design, and it is built, run and documented. Residue has owners -- the thesis-shaped simulate fixture goes to [[ir-simulate-design]] (logged there; conv/computed-numeral is its proxy meanwhile), the quadratic to [[subst-copies-payloads-at-depth-zero]], user-latency measurement to [[frontend-benchmarks]].
- 2026-11-20: Counters became the gate (Minus, after [[conversion-closed-sum-opaque-counter]]). Each case records the kernel's stats counters over its validating run (eval_steps, eval_delta_steps, reduce_steps, local_subst_nodes, shift_global_nodes, arena_peak_bytes; `COUNTED` in harness.rs), prints them and a work slope per counter, and baseline.tsv keeps them as `count` rows. `--check` fails when a counter grows (5% for the two address-keyed ones; arena bytes only under the baseline's rustc and profile); times and time-slope drift are printed as `slower` and no longer fail, so a baseline from another machine still gates fully. New `delta/*` families convert over Ψ definitions (closed sum over a chain of glued `max` folds, its numeral control, newer-side lockstep, same-head arguments through a chain); with `Eval::force_counter` disabled `delta/closed-sum` grows eval_steps 16K→32K and arena 4→12 MB at 128 definitions (work slope 1.21 and rising), which the exact counters catch and the old 1.25× time gate on a slope band did not. `scripts/bench-probes --check` gates its counters the same way.
- 2026-11-20: Second round of families (Minus: "a good bit more bench cases"): delta/refusal, shared-dag, record-projections, check-refl, bool-verdict; run/affine-literal, sync-literal, mul-literal, open-tail, fuel-exhaustion; subst/shared-dag; conv/shared-neutral-dag; syntax_eq_nodes joins the counted set. Two findings, each recorded in its family's band: [[wide-literal-run-cost]] (runs over literals past one word, time ~bits^1.5 with flat counters) and [[conversion-neutral-dag-syntax-memo]] (separately built neutral DAGs, syntax_eq_nodes n²).
