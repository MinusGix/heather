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

## Log

- 2026-09-11: One instrumentation layer landed (design: docs/instrumentation-design.md), not yet committed. Kernel: crates/kernel/src/stats.rs, thread-local Cell<u64> counters behind one macro, always compiled, read by nothing inside the kernel — conv shortcut/memo hits, misses, and the miss's outcome split into conv_out_of_fuel vs conv_not_convertible (the residue [[generated-proof-cost-diagnostics]] left); evaluator steps/delta-steps/drives are plain fields on Eval flushed on drop, so the fuel decrement grows no thread-local access. crates/kernel/DESIGN.md gained the inert-counters paragraph. Elab: crates/elab/src/stats.rs is now a registry of 19 named timers and 5 named counters with scope rows (item/module/run), replacing stats::time_kernel and OmegaPhases::timed; nesting rule is timers exclusive (self time), scopes inclusive. stats::kernel_ns/reset_kernel_ns keep their exact old meaning so the frontend bench's parse/elab/kernel split is unchanged. New attribution: heather check --timings <file.tsv> (the primary command had none), parse separated from elaboration on BOTH module paths, a declaration scope on check_module_source, unify/resolve/matching/gendefs entry brackets, Elaborator::with_prelude, semantic replay's decode/recheck/publish ([[semantic-replay-phase-attribution]]), cache identity hashing and the merkle walk (Counts had counts, no ns). Consolidated: five roll-up printers (semantic.rs, native.rs, function_ir_x86.rs, x86_64.rs, omega_cases/mod.rs) become one stats::dump writing one TSV; four env switches (HEATHER_OMEGA_PHASES, HEATHER_X86_PHASES, HEATHER_FUNCTION_IR_X86_TIMINGS, HEATHER_OMEGA_PREFIX_PHASES) become HEATHER_TIMINGS=<path|->; --item-timings still parses as an alias for --timings; HEATHER_VALUE_METRICS/HEATHER_CONV_MISS_TRACE and the .conv-miss.txt sidecar are untouched. scripts/run-test-targets.mjs now APPENDS a run-id column to target/test-target-timings-<lane>.tsv (tail-capped at 4000 rows) and loadHistory takes the latest row per target. Tests: crates/elab/tests/instrumentation.rs (rows, exclusive nesting, header stability, mismatch-vs-fuel columns, off-by-default), crates/cli/tests/timings.rs (declaration/module/run rows, prelude and conversion-hit columns, cold publish + warm decode/recheck), one omega-timer assertion inside omega_cases. Verification on furnace: scripts/test --fast == suite: 2419 passed, 0 failed, 5 ignored ==; scripts/bench --check shape-only, 18 comparisons within thresholds, 88 skipped for the desktop-baseline env mismatch, no family flagged as a slope regression; crates/cli/tests/native.rs::source_to_native_binary green against the new TSV header. Real run: release heather check --timings on lib/std/omega.hthr wrote 632 rows; the run row reads kernel_gate 6.60s of 9.47s total, omega_check 1.07s, matching 38.5ms, resolve 12.8ms, parse 10.7ms, other 1.71s, with 2.78M conversion shortcut hits counted for the first time. Deliberately left out: scripts/perf and the frame-pointer profile ([[perf-profile-build-target]] items 1-2), per the round's scope. Also gone on purpose: the per-INVOCATION omega phase lines — the omega_* columns attribute by declaration instead, and OmegaReport still carries the inclusive per-invocation numbers through take_omega_reports.
- 2026-09-11: 2026-09-11 first field use (reused_callee build-x86, lib/std/omega check) and the residue it exposed: (1) the elaborator's unattributed 'other' bucket is 32 s of 118 s on the x86 certificate and 1.7 s of 9.5 s on omega — the next timers to add are elaborator-side whnf/conversion probes, infer/check of a declaration's type and body, and quoting/emission, so 'other' names something; (2) build-x86/compile-x86 write no run row (only heather check opens a Run scope); (3) in-process test bodies dump only if they opt in via stats::with_env_dump — the heather-cli bin unit tests (elf_header_mutations, 88 s) and lib_setoid_mergeable do not, so HEATHER_TIMINGS on them writes nothing; wire those two. Also worth a column: eval steps per kernel second is a useful derived rate (~1.7 M/s on the certificate).
