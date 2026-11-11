---
title: Where the time goes on 2026-11-11: overview and ranked findings
status: closed
labels: [performance,overview]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

An overview of where time goes on 2026-11-11, after #553, taken to decide whether the kernel performance thread continues. The full write-up with tables is the Claude Doc "Heather: where the time goes (2026-11-11)" (https://claude.ai/artifact/W4BewnWoW2uzv2UgoDhDQ7). The measurements are in `perf/snapshots/2026-11-11T093145Z-cloud.json` (the first cloud snapshot) and `perf/bench/results.tsv`. This issue is the index of what it found.

## What a person or a round waits for

One four-core cloud box, release binary at #553 plus the name-record fix.

| wait | today |
|---|---|
| warm check of a file | 0.04 to 0.5 s |
| re-check after an edit | 0.1 to 0.7 s (2 to 3 s for the x86 certificate and `native_compile_correct`) |
| cold check of the showcase, plain | 9.1 s at the default width, 11.1 s at width one (13.8 s and 16.0 s on master at #552) |
| cold check of an analysis or native file | 77 to 89 s |
| x86 certificate, cold | 27 s |
| rebuild of the test binaries after a one-line elaborator edit | 123 s |
| fast lane, warm stores | 143 s of tests |
| `--pr` lane | about 300 s of tests |
| exact lane | 507 and 544 s of tests in two runs; the library gate is 503 and 538 s of that |
| cold library build, `--build-jobs 4` | 215 s wall, 845 s of work |

## What the time is

- The kernel gate is 36% of a cold showcase check and 43% of the cold library at width one (shares of attributed time). Elaboration is 47% and 40%, images and hashes 13% and 10%, `omega` 3% and 7%.
- Kernel code is about 57% of a cold check's instructions: the elaborator runs the evaluator, substitution and conversion for its own questions nearly as much as the gate does.
- The library is flat: 23,856 declarations, the top 100 are 42% of declaration time, and one stands out.

## Ranked, with the issue that owns each

1. The elaborator crate's compile: [[elaborator-crate-compile-per-edit]] (done the same day: 123 s to 14 to 31 s). What it left: [[elaborator-edit-recompiles-shared-vec-unit]] and the kernel's own edit, [[kernel-edit-rebuild-cost]].
2. The cold library's total work:
   - one proof, 33 s and 1.3 GB: [[perform-call-heaviest-declaration]];
   - instance resolution on the reals: [[instance-resolution-on-the-reals]];
   - build children replaying their imports: [[build-children-replay-their-imports]];
   - name resolution: [[name-resolution-reads-entries-four-times]];
   - the kernel's open performance issues: [[conversion-closed-pairs-across-gates]], [[conv-query-identity-env-per-gamma]], [[instance-match-walks-the-template-twice]].
3. Native tools in every lane: [[native-tool-compile-attribution]].
4. The serial front of a cold check: [[proof-bodies-on-the-workers]].
5. The measuring tools: [[timings-instrumentation-cost]], [[bench-probe-cases-stale-2026-11]].

What does not hurt: warm checks, the edit loop, the native process floor (8.3 s on 2026-10-29, 1.1 s now), and memory apart from `perform_call`.
