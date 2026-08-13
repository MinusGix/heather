---
title: Six certgen binaries each re-elaborate the shared library; snapshot it once per suite
status: open
labels: [testing,tooling,performance,elaboration]
created: 2026-08-12
updated: 2026-08-12
---

The standing lever [[certgen-harness-cost]] has recorded twice, promoted to its own issue after the non-Nat round (2026-08-12) gave it a 6x multiplier: the certgen test family is now six binaries (certgen, certgen_emissions, certgen_nonnat, certgen_controls, certgen_cert, certgen_route1_spike), and each one independently builds an elaborator and re-elaborates the same shared prefix — lib/ir_v1.hthr's declarations plus lib/certgen_code.hthr (~42 s alone after the round) plus lib/certgen_cert.hthr — before its own content starts. That is ~6 × 45 s of identical work per full suite, and every future binary split (the recorded remedy whenever a rail nears the 300 s `ulimit -t`) adds another copy. The two levers compound against each other: splitting binaries protects the rail by paying the prefix again.

Shape options, deliberately not chosen here:
- **Serialize the elaborator state**: elaborate the shared prefix once (a build-script step or a first "fixture" binary), serialize Ψ + the elaborator's tables, deserialize per binary. Largest surface — the elaborator was never designed to round-trip, and GenDef registries / MetaDefs / solver tables all carry indices that must survive.
- **Reuse the CLI's declaration cache**: `heather check --cache-dir` already skips the kernel gate on warm declarations (~95% of these files' cost per [[wf-field-conversion-cost]]'s measurement); a shared cache dir keyed for the test harness might buy most of the win with no new serialization — but the tests drive the elaborator *library*, not the CLI, and [[cache-verdicts-omit-check-settings]] is a correctness caveat on the cache as it stands. [[warm-path-rewalks-unchanged-declarations]] bounds the warm path's own cost.
- **Merge binaries behind a longer rail**: raise `ulimit -t` for a consolidated certgen binary. Rejected twice already ([[certgen-harness-cost]]) because the cap is the OOM/runaway backstop, but recorded so nobody re-derives it.

A deliberate round per the accumulator discipline (user deferred this explicitly on 2026-08-12: "we'll have to investigate that another time"). Measurement protocol per [[perf-tracking-consistent-environment]]. Trigger: the next deliberate perf round, or the next time a certgen rail split is proposed.
