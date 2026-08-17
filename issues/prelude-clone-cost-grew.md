---
title: Cloning a prelude'd elaborator went 300 ns -> 6.9 us; the fixture argument that rests on it should be re-checked
status: open
labels: [elaboration,performance,tooling]
created: 2026-08-17
updated: 2026-08-17
---

## Log

- 2026-08-17: FOUND 2026-08-17 (managed tooling round) in the frontend baseline re-record, and it is a measurement rather than a diagnosis. `corpus/prelude` reads, on minus-desktop with only a desktop running: build 91.5 us -> 125.3 us (1.37x) and **clone 299.6 ns -> 6.87 us (23x)** against the 2026-08-05 baseline row. The clone figure is stable across five runs that evening (6.8-6.9 us) and it is the FIRST family measured in a run, so it is not the contamination of [[frontend-bench-heavy-contaminates-cheap-cases]].

The obvious reading is that the prelude got bigger -- `lib/std/logic.hthr` and its notation landed 2026-08-16, and a clone copies whatever the elaborator carries -- so this is plausibly a fact about the prelude rather than a defect in cloning. What makes it worth an issue is that a documented argument rests on the ratio: docs/frontend-benchmarking.md's fixture rules justify the generated families cloning a prelude instead of rebuilding one with "~100 us to build, ~104 ns to clone", i.e. a thousandfold. The ratio is now ~18x, and the absolute clone cost is 6.9 us against a smallest generated case of ~165 us -- 4%, which is a constant the doc's own reasoning says "does not merely add noise, it FLATTENS THE EXPONENT". At 4% the argument still holds and the doc's number is simply stale; at 40% it would not, and nothing is watching the trend.

So: (1) re-check what a clone actually copies now (is 23x explained by the prelude's growth, or is something per-clone deep-copying what it used to share?), (2) correct the doc's ratio to the measured one, and (3) if the answer to (1) is "it grew, and it will keep growing with std", record what fraction of the smallest generated fixture is the threshold at which the clone strategy stops being sound for an exponent fit.

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the fixture rule that generated families
  clone a prelude rather than build one. Assumed here: only that the rule's
  justification is the build/clone ratio.
