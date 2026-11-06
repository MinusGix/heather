---
title: Find why grind calls slow down with itree in scope
status: open
labels: [tactics,performance]
area: tactics
milestone: [tac-general]
created: 2026-11-06
updated: 2026-11-06
---

With `itree`/`coitree` imported, every grind call in `grind_tests` took
several times longer (the same kernel steps; a trivial call's time unchanged
without them), which put that probe module over its CPU rail on 2026-11-05;
the codata probes moved to `grind_codata_tests`. So something per call grows
with the scope rather than with the goal.

First suspects: name resolution (`Lookup`, `resolve`) or a host request that
walks the whole environment. Measure with `--timings` on one probe in both
scopes (the counters are the same, so the seconds and the host's own
attribution are what to read) before changing anything.

## Done when

The cause is named, and a grind call's cost does not grow with unrelated
imports (or this records why it must).

## What it assumes from elsewhere
- **[[grind-closure-cost]]** found it while making grind cheaper to import.
  Assumed here: only the measurement above.
