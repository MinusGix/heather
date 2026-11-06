---
title: parser_library and showcase_calculator reach the CPU rail from a seeded store
status: open
labels: [testing,sentinel,performance]
area: infrastructure
created: 2026-11-06
updated: 2026-11-06
---

The first `scripts/test --pr` after #435 (2026-11-06, cloud box, stores
seeded from the last green sentinel at c374f3f) ended
`== suite: INCOMPLETE (3745 passed before death, 0 failed) ==`: the
`parser_library` member of `family_logic` was killed at its 300 s rail
(`TERMINATED (signal=SIGKILL) (442.01s, 298.8 CPU-s)`). The new per-process
section ([[test-cpu-rail-child-accounting]]) named both elab showcase
members:

```
   297.7 CPU-s  99% of 300 s  crates/elab/tests/parser_library.rs: family_logic-… --format pretty -Z unstable-options
   201.9 CPU-s  67% of 300 s  crates/elab/tests/showcase_calculator.rs: family_logic-… --format pretty -Z unstable-options
```

Rerun alone right after, over what the killed run had written: 35 CPU-s,
5 passed. So it is the cold half, as in [[master-red-2026-11-04]] (cold
and alone, showcase_calculator 184 CPU-s and parser_library 170, 55–60% of
the rail), now past it on a seeded box under the suite's load. The diff of
that run (#435) does not reach either test's sources.

Same shape as [[master-red-2026-11-06]]: a test process that elaborates a
shared prefix cold and then its own work, under one rail. Options, in the
order that note's fix suggests: warm their prefix in its own bounded process
before the parallel phase (as `semantic_warmup` does for the x86 and omega
families), or split the member so no one process carries the cold prefix and
the showcase together ([[integration-test-prefix-reelaboration]] owns the
longer-term fixture). Not a raised rail.
