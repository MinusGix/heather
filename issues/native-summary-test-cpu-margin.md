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
