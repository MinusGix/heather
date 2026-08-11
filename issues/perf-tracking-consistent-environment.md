---
title: Consistent perf measurement: a place where a regression is a signal, not noise
status: open
labels: [performance,tooling,testing,meta]
created: 2026-08-11
updated: 2026-08-11
---

Filed from the 2026-08-11 iteration-time review. Two observations met:

1. Ad-hoc perf measurement keeps leaking into rounds that should not care.
   The bare-symbol round timed `heather check` by hand (a failed
   `/usr/bin/time` attempt, then a date-based loop) to prove a respelling
   was free — which CLAUDE.md now says plainly: an ordinary round does not
   measure. But the instinct came from somewhere real: nothing else would
   have noticed a regression.
2. The user's machine cannot be the baseline: "I'm always doing random
   stuff" — wall-clock numbers taken beside a browser build are noise, and
   the §12.7-style bands recorded in design docs go stale the moment the
   hardware or the load changes.

What exists: `scripts/bench --check` gates the kernel against
`crates/kernel/benches/baseline.tsv`, and its headline is the **scaling
exponent**, which is the one number that survives a machine change
(docs/benchmarking.md). Nothing gates the elaborator or the whole-library
checks; their §12.7-style bands live in prose.

The question this issue owns: what is the *program or environment* whose
numbers are consistent enough that a notable regression is a signal?
Directions to weigh, not decided:

- **Count instructions, not seconds.** `perf stat` retired-instruction
  counts (or cachegrind) are nearly load-immune and machine-comparable to
  first order; a `scripts/bench`-style gate over "instructions to check
  lib/std + ir_v1" would run fine on a busy machine. The harness stays
  first-party (dependency-policy: the kernel keeps zero deps; a script
  invoking perf is a script, not a dependency).
- **Extend the exponent discipline** from the kernel benches to elaborator
  workloads: exponents need less quiet than absolute times, and
  docs/benchmarking.md already explains why they are the headline.
- **GitHub CI** — unknown runner consistency (shared, throttled, changes
  under you); probably fine for exponents/instruction counts, useless for
  wall-clock bands. Also: is this repo even hosted where CI can see it?
- **A dedicated cadence** (nightly cron on an idle machine) if one exists.

Related: the one-deliberate-perf-round-per-session discipline is *when*
perf work happens; this is *where its numbers come from*.
[[bounds-metadata-taxes-one-shot-checking]], [[certgen-harness-cost]] and
[[synthesis-direction-cost-asymmetry]] all recorded "levers if it grows" —
each assumes something will notice growth, which is this issue.
