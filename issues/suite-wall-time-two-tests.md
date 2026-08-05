---
title: Suite wall time is two tests: certgen emissions (~13 min) and the full ir_v1 check (~15 min)
status: open
labels: [testing,tooling,performance]
created: 2026-08-05
updated: 2026-08-05
---

Measured during the [[dependent-motive-crossing-sweep]] round (2026-08-05): `certgen::emissions_check_and_controls` ~13 min and `ir_v1::the_full_ir_library_checks` ~15 min dominate `scripts/test`; the other ~1060 tests finish in well under a minute combined. Every managed round pays this twice (agent run + coordinator verification).

Levers, none chosen yet: `#[ignore]` + a deliberate slow-lane invocation in scripts/test (kept on for full verification runs, off for inner-loop), fixture shrinking, or the accumulator levers already recorded on [[certgen-harness-cost]] — this ticket is the *harness-shape* question, that one owns the generator-cost question. Triggered ticket per the perf-accumulator convention; one deliberate round when turnaround starts to hurt.
