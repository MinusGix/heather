---
title: parser_library and showcase_calculator reach the CPU rail from a seeded store
status: closed
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

## Resolution (2026-11-06)

`semantic_parser_warmup` (crates/elab/tests) builds the prefix the two
members replay, one slice per process, before the parallel phase:
`scripts/test`'s `parser_warmup` runs its four stages with `--exact`, each
under the warmup's own 6 GiB / 300 s rails, each replaying the slices
before it (images are keyed by a module's source and closure, not by the
list that loaded it). The stages: the omega prefix, grind's closure, the
parser library, the showcase. It runs whenever its target is selected
(unfiltered), or for a focused `--test family_logic` or whole-elab run.
The three lists the members and the warmup share now live once, in
`support::parser` (`STD`, `MODULES`, `SHOWCASE`).

Cold, on a fresh cloud box at width one: the stages cost about 4, 59, 4
and 2 CPU-s (grind's closure dominates), and the members after them about
1 CPU-s each, against the 170–300 they spent building it themselves. This
box's cold prefix was cheaper than the reports above; the point is that
neither member's rail carries it any more, and no stage is near its own.

The same round fixed the `--pr` lane's native path filter, which matched
`crates/cli/src/native/` but not `crates/cli/src/native.rs` (where #435's
`warm-native` lives), so a diff touching only `native.rs` ran just the
smoke.
