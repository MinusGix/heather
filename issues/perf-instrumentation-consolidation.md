---
title: One instrumentation layer: scoped counters and timers on every phase, dumped from heather check
status: open
labels: [tooling,performance,measurement,kernel,elaboration,cli]
created: 2026-09-11
updated: 2026-09-11
---

Every performance issue in the tracker starts its next action with "re-measure first", and the main command has nothing to measure with: `heather check` has no timing flag at all. What exists is real but scattered (survey 2026-09-11):

- an always-on thread-local kernel-gate timer (`crates/elab/src/stats.rs`) and an omega phase timer (`crates/elab/src/omega_cert.rs::OmegaPhases`) that are the same function written twice;
- per-declaration `ItemTiming` brackets on `elab_module_source` only, exposed solely through `--item-timings` on `compile-x86`/`build-x86` (`crates/cli/src/native.rs`); the `check_module_source` path has no bracket;
- `ValueMetrics` counters plus the conv-miss sampler behind the `value-metrics` cargo feature, printed via `HEATHER_VALUE_METRICS` / `HEATHER_CONV_MISS_TRACE`;
- four more hand-rolled env switches (`HEATHER_OMEGA_PHASES`, `HEATHER_X86_PHASES`, `HEATHER_FUNCTION_IR_X86_TIMINGS`, `HEATHER_OMEGA_PREFIX_PHASES`) and five copies of roll-up printing in `semantic.rs`, `native.rs`, and three test files.

Three enablement mechanisms coexist, and the code argues both ways: `stats.rs` says no feature gate so the benchmarked build is the shipped build; `value.rs` says feature gate so ordinary builds carry no branches. A uniform layer must settle that first. Proposed: always-compiled scoped counters and timers (one named registry, one per-declaration scope object, one dump surface), with only the expensive samplers (conv-miss excerpts, backtraces) behind the feature.

## Gaps with no attribution today

- any timing on `heather check` (parser at `crates/cli/src/main.rs::parse_check_args`, module loop below it);
- parse time separated from elaboration (`Elaborator::elab_module_source` runs `parse_file` before the timed loop);
- conversion *hits* (`Tc::conv_ty` returns from the memo before the clock starts; only misses are timed);
- evaluator step and δ-step counts (`Eval::step`, fuel decrement in `crates/kernel/src/eval.rs`);
- unification, trait resolution, match speculation, generated-declaration timers in the elaborator (omega is the only subsystem with phases);
- semantic image replay phases: decode / kernel-recheck / publish (`crates/cli/src/semantic.rs`), the thing the fast lane's premise rests on ([[semantic-replay-phase-attribution]]);
- declaration-cache hashing time (`crates/cache/src/lib.rs::Counts` has counts, no ns);
- `Elaborator::with_prelude` cost in shipping code ([[prelude-clone-cost-grew]]);
- per-test timing history: `target/test-target-timings-<lane>.tsv` is overwritten each run, and warmup subprocesses print nothing summable;
- fuel/memo/reduction counters that distinguish a mismatch from fuel exhaustion (residue of [[generated-proof-cost-diagnostics]], closed 2026-09-11);
- `scripts/perf`, a frame-pointer profile, and a generalized attach hook ([[perf-profile-build-target]] items 1 and 2, still absent).

## What it assumes from elsewhere

- **[[perf-tracking-consistent-environment]]** owns where numbers come from and what counts as a regression. Assumed here: only that attribution output is diagnostic, never a gate.
- **[[perf-profile-build-target]]** owns the sampling-profiler side. Assumed here: the two are complementary, and its item 3 (the miss sampler) is one of the surfaces to consolidate.

## Acceptance

- `heather check --timings <file.tsv>` (name open) writes per-module and per-declaration rows: parse, elaborate, kernel, conversion hits/misses, evaluator steps, cache/replay phases.
- One registry replaces `stats::time_kernel` and `OmegaPhases::timed`; one dump function replaces the five roll-up printers; the four env switches become one.
- Ordinary builds pay no measurable cost with it off (`scripts/bench --check` shape-only is enough to show it).
