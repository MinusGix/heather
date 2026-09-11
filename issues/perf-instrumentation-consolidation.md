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
- 2026-09-11: the elaborator's `other` bucket is named, and it turned out to be **diagnostics**. Eight timers added (`decl_type`, `decl_body`, `decl_emit`, `decl_commit` — the four phases that partition `check_decl`; `lower` — the non-`fn` declaration forms' lowering; `elab_whnf` — the oracle's head-shape probes; `diag_note` — elaborator-side conversion run for a *message*; `lint`) plus one counter (`diag_notes`); 19 timers become 27. Residue item (2) done too: `build-x86`/`compile-x86` now open a `Run` scope and a `Module` scope around the generated certificate, so the native commands finally total. Desktop (minus-desktop), release, `HEATHER_KERNEL_WORKERS=1`, warm image cache, the first run after each rebuild discarded.

**`reused_callee` `build-x86`, summed over the 3474 certificate item rows:**

| | before | after |
| - | ------ | ----- |
| total | 110.10 s | 109.62 s |
| kernel_gate | 78.83 s | 78.55 s |
| diag_note | — | 20.33 s (18.5%) |
| decl_body | — | 5.40 s |
| decl_type | — | 1.71 s |
| decl_emit | — | 1.61 s |
| elab_whnf | — | 1.11 s |
| decl_commit | — | 0.47 s |
| lint / unify / resolve | 0.24 s | 0.14 s |
| **other** | **31.03 s (28.2%)** | **0.29 s (0.3%)** |

The new columns sum to 30.69 s against an old `other` of 31.03 s: the bucket is accounted for to within a third of a second. Wall 120.93 s → 120.19 s, so the brackets cost nothing measurable.

**`heather check lib/std/omega.hthr -L lib/std`, the run row:**

| | before | after |
| - | ------ | ----- |
| total | 10.19 s | 10.22 s |
| kernel_gate | 7.176 s | 7.156 s |
| diag_note | — | 0.791 s |
| omega_check | 1.156 s | 0.669 s |
| decl_body | — | 0.628 s |
| decl_emit | — | 0.599 s |
| elab_whnf | — | 0.054 s |
| decl_type | — | 0.049 s |
| decl_commit | — | 0.041 s |
| matching | 0.041 s | 0.027 s |
| lower / parse / omega_parse / resolve / lint / unify | 0.047 s | 0.056 s |
| **other** | **1.769 s (17.4%)** | **0.151 s (1.5%)** |

Here `omega_check` also sheds half a second, and correctly: that bracket wraps `elab_check` of a generated certificate, so the diagnostic probes and whnf probes inside it were always its *nested* time and now have their own columns. Wall 10.267 s → 10.299 s.

**What the bucket is.** `note_check_mismatch` and `note_refl_mismatch` run a conversion to find out whether they have anything to say, on every candidate, whether or not the declaration goes on to check: 33 019 notes on the certificate and 24 142 on omega, none of them printed, for 20.3 s and 0.79 s respectively. It is now the largest serial cost on the certificate workload and therefore the next thing standing in front of [[parallel-kernel-gate]]'s 2.88x — filed as [[elab-diagnostic-probe-cost]]. The rest of the old bucket is ordinary and wants nothing: the body walk, the respell-and-substitute step, the telescope, the commit.

**Placement rules kept.** `diag_note` and `elab_whnf` are placed where no `stats::time_kernel` bracket can enclose them (audited: every `time_kernel` site calls `typing::*` or `oracle::convert_*`, never `oracle::whnf_*` and never a note), so `stats::kernel_ns` keeps its exact old meaning and the frontend bench's parse/elab/kernel split is unmoved — `kernel_gate` 78.83 → 78.55 s and 7.176 → 7.156 s across the two workloads is run-to-run noise.

**Verification.** `furnace run -- scripts/test --fast` `== suite: 2435 passed, 0 failed, 5 ignored ==`. `scripts/bench --check` on the desktop that recorded the baseline: 6 regressions and 8 improvements, all of them the pre-existing `nat/step-once` + `nat/mul-normalize` Arc tax and the `check-numeral`/`wf/check-tree` wins already on record — this round's diff touches no file in `crates/kernel`, so the kernel bench binary is the same one, and no family is flagged for slope. `scripts/bench-frontend --check --no-heavy` against a `--save` taken on the same box from the un-instrumented tree (the committed frontend baseline is from 2026-08-17 and would measure a month, not this diff): 9 flags on the first run, 1 on the second — and the **control**, the un-instrumented tree checked against its own baseline, flags 6, including `corpus/parse:ir_v1.hthr` at 1.39x, which is one build of one parser against another build of the same parser. So `--no-heavy` on this box cannot resolve anything under about 1.4x per case, and the only family flagged in all three runs is `indexed/arms slope band` (2.46 in the control, 2.55 and 2.58 instrumented) — flagged against itself, not by this diff. The wall clock on the two real workloads is the better evidence: 120.93 -> 120.19 s and 10.267 -> 10.299 s, both inside noise, for two `Instant::now()` per declaration phase, per whnf probe and per diagnostic note.

**Left out on purpose.** Residue item (3) — the `heather-cli` bin unit tests and `lib_setoid_mergeable` do not opt into `stats::with_env_dump`, so `HEATHER_TIMINGS` on them still writes nothing. Residue item's derived `eval steps per kernel second` rate is not a column; the two counters it divides are both in the TSV already. `scripts/perf` and the frame-pointer profile stay [[perf-profile-build-target]]'s (a frame-pointer build plus `perf record` is how the bucket was located, but nothing about it landed in the tree).
