---
title: Suite wall time is two tests: certgen emissions (~13 min) and the full ir_v1 check (~15 min)
status: closed
labels: [testing,tooling,performance]
created: 2026-08-05
updated: 2026-08-05
---

Measured during the [[dependent-motive-crossing-sweep]] round (2026-08-05): `certgen::emissions_check_and_controls` ~13 min and `ir_v1::the_full_ir_library_checks` ~15 min dominate `scripts/test`; the other ~1060 tests finish in well under a minute combined. Every managed round pays this twice (agent run + coordinator verification).

Levers, none chosen yet: `#[ignore]` + a deliberate slow-lane invocation in scripts/test (kept on for full verification runs, off for inner-loop), fixture shrinking, or the accumulator levers already recorded on [[certgen-harness-cost]] — this ticket is the *harness-shape* question, that one owns the generator-cost question. Triggered ticket per the perf-accumulator convention; one deliberate round when turnaround starts to hurt.

## Log

- 2026-08-05: Measured under exact scripts/test conditions (2026-08-05, dev + opt overrides, 4 GiB cap): ir_v1 full check 120 CPU-s, certgen emissions 160 CPU-s — ~4.7 min combined, NOT ~28; the 13/15-min figures were wall-clock on a machine saturated by the sweep round itself and are withdrawn as the headline. What is real: the pair is ~80% of suite wall time (the rest of the suite is 27.5s wall), both grew +50-60% since 2026-08-02 tracking library/kit growth, and certgen sits at 53% of the 300s CPU rail, nearing [[certgen-harness-cost]]'s 200s trigger. Lever chosen and landed: scripts/test --fast skips the two by exact test name (default stays full; a round's FINAL verification and anything touching lib/, the kit, or the generators runs plain scripts/test). Budget notes updated in both test headers; release CLI check of the closure re-measured at 80.6s for the record. Growth watch stays with [[certgen-harness-cost]]. Closing: the harness-shape question this ticket owns is answered.
