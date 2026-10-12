---
title: The stat width refusal test runs at the CPU rail
status: closed
labels: [x86,testing,performance]
created: 2026-10-10
updated: 2026-10-11
---

`slow_acceptance_stat_width_refusals` (`crates/elab/tests/stat_width_refusals.rs`,
in `family_function_ir`) elaborates seven mutated copies of
`elf64_stat_width` over one replayed prefix. Each copy must be refused. Under
`scripts/test`'s `ulimit -t 300` it now sits at the rail:

- On master at 93de7a0, alone, at width one, with its prefix images warm, it
  took about 295 CPU-s, twice in a row, on a 4-core cloud box (2026-10-10).
- In a full suite on the positivity branch (master merged in), the test was
  killed at 300.0 CPU-s (SIGKILL), and the suite reported `INCOMPLETE`. Alone
  and warm, the same tree took about 260 to 277 CPU-s.

So the gate passes or fails depending on host speed. That is the failure mode
of [[native-print-test-cpu-margin]] and [[native-summary-test-cpu-margin]].
It lies outside the fast lane, so it tips in the full lane.

Not measured yet: what dominates. Each mutation re-elaborates the whole stat
pass module before its refusal, so the cost is about seven times one
`elf64_stat_width` check.

## Options

1. Split the seven mutations across two or three tests, so each process gets
   its own rail. This is the cheapest option and keeps every negative control.
2. Make the refusal cheaper: stop at the first failing declaration (it may
   already), or check only the theorem each mutation breaks, by an `--only`
   style probe.

## Log

- 2026-10-11: Measured after [[suite-iteration-chokepoints-2026-10]] (the refusal test's unmutated base is now replayed from the semantic images, not re-elaborated from source): 68.8 CPU-s in a full suite on a 4-CPU cloud box, 23% of the rail. Closing: the margin is back without splitting the mutations.
