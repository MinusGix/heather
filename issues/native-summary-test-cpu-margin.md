---
title: The two-placement native summary test runs within 25% of the CPU rail and tips over under suite load
status: open
labels: [x86,testing,performance]
created: 2026-09-09
updated: 2026-09-09
---



`two_placed_calls_share_one_summary` (`crates/cli/tests/native_summary.rs`)
spawns `heather build-x86` under `scripts/test`'s `ulimit -t 300`. Measured
alone on a warm furnace box (2026-09-09, one release build, cap lifted to
900 s): **226 s CPU** with [[bitvec-width-bounded-defaults]] applied, **233 s**
without — so the test has no headroom to speak of, and in a plain full
`scripts/test` on the same box it was SIGKILLed at 300 s once while the same
tree's previous full run passed. The parallel suite (several 4 GiB children on
8 OCPUs) inflates CPU time enough to cross the rail; the test's own cost did
not move.

[[x86-native-certificate-cpu-budget]] brought it from over the rail to 224 s
and closed; this is the residue: a gate that passes or fails on host load is
not a gate. Options, in preference order: attribute and shrink the
certificate's cost (that issue's log names byte-fetch declarations as the bulk,
[[generated-proof-cost-diagnostics]] owns the tooling); split the check across
two children so each is well under the rail; or run it serially the way
[[mutual-recursion-test-rail]] keeps its target inside the rail. Do not raise
the rail or shrink the example.

## What it assumes from elsewhere

- **[[x86-native-certificate-cpu-budget]]** owns the 224 s datum and the
  prefix-skip helper; assumed here only that nothing since changed the cost
  (the A/B above says the swap did not).
- **[[mutual-recursion-test-rail]]** owns the serial-rail mechanism if that is
  the route taken.

## Log

- 2026-09-09: Route 2 taken (2026-09-09): native_summary is now an exclusive target in scripts/run-test-targets.mjs (the frontend_bench_smoke mechanism: sorted last, runs alone after the parallel phase), so its 226-233 s alone is what it pays, not the contended 294 s. Costs ~4 min of full-suite wall on an otherwise idle box; the certificate-cost route (option 1) stays open as the real lever. Same round: the fast lane now skips all six native certificate gates and their warmup (~1200 CPU-s that no elaborator edit iterates on).
- 2026-09-09: Verified on furnace (2026-09-09, warm box): full lane 2530 passed, native_summary 225.39 s alone as the exclusive target, suite 572 s wall; the fast lane dropped 461 s -> 195 s wall with the native gates skipped. Two further certificate-bearing unit tests (elf_header_mutations_are_rejected_by_heather, call_stack_semantics_and_refusals; 180 s together) were still in the lane on the first pass and are now skipped too.
