---
title: Conversion's own cost on large canonical values: the residual no spelling reaches
status: open
labels: [kernel,conversion,performance]
created: 2026-08-13
updated: 2026-08-13
---

The residual named by two consecutive spelling rounds and owned by neither. After [[wf-field-conversion-cost]]'s component respell and [[wf-shape-annotation-slots]]'s slot naming removed most emitted node mass, `lib/ir_v1.hthr` whole moved least of the measured workloads (~1.25x where the declarations prefix moved ~1.6x and prefix+certgen_code ~3x): its theorems' wall time is **conversion on large values** — the kernel comparing/reducing big canonical constructor trees — which no annotation spelling touches, because the cost is in the values themselves, not their type annotations.

Both rounds' logs name it explicitly ("the residual that no spelling reaches", docs/annotation-component-respell-design.md and docs/wf-shape-code-design.md §7); this issue is its home so the next re-attribution has somewhere to point.

Related but distinct: [[value-domain-allocation-constant]] (the value domain's constant-factor allocation where there is no sharing to win) and the closed [[whnf-sharing-term-growth]] (working-term growth in non-tail eval nesting). Whether this issue's cost decomposes into those or is its own defect is the first thing a round here should measure.

## When

Triggered: the next time `lib/ir_v1.hthr`'s theorem wall time (or any large-value workload's conversion share) matters — one deliberate round, per the accumulator discipline. Measurement first: profile where conversion spends on one of ir_v1's value-heavy theorems before proposing anything.
