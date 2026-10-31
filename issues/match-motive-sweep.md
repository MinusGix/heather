---
title: Sweep the library's redundant written motives and hand convoys
status: open
labels: [stdlib,cleanup,match]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 7 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §10), last.

On a 379-motive sample, `heather check --review` finds 180 (47%) of the written motives redundant on master `35b223d` (design §1.2). Apply the lint's deletions library-wide, then rewrite the hand equation convoys (259 motives, 145 `(refl)` applications) and the arrow motives whose hypotheses slices 1–2 now supply. Measure with `scripts/perf ab --source-patch`.

## Done when
- The census in [[match-motive-surface-audit]] is rerun on the result, with what remains classified.
