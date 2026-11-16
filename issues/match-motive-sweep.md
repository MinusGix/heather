---
title: Sweep the library's redundant written motives and hand convoys
status: closed
labels: [stdlib,cleanup,match]
area: language
created: 2026-10-31
updated: 2026-11-02
---

Slice 7 of [[dependent-match-compiler]] (docs/language/matching/dependent-match-compiler-design.md §10), last.

On a 379-motive sample, `heather check --review` finds 180 (47%) of the written motives redundant on master `35b223d` (design §1.2). Apply the lint's deletions library-wide, then rewrite the hand equation convoys (259 motives, 145 `(refl)` applications) and the arrow motives whose hypotheses slices 1–2 now supply. Measure with `scripts/perf ab --source-patch`.

## Done when
- The census in [[match-motive-surface-audit]] is rerun on the result, with what remains classified.

## Log

- 2026-11-02: 2026-11-01, slice 7 on PR #318. heather check --review over the whole library, run with a fresh cache dir so every module re-elaborates (--build-jobs workers do not run the review lints, and cached images skip them), reported 823 redundant written motives. 818 were deleted by script across 66 files. One more needed a hand fix: a motive that itself contained a match. Five reports point at measure-generated matches, filed as review-lint-redundant-motive-on-generated. The library re-checks ok with 184 expected refusals matched. Census of written motives: 1778 → 923, of which 292 are unapplied arrow motives, 241 are applied with hand-carried hypotheses, 203 are dependent goals the lint could not drop, 168 are (…)(refl) convoys and 19 are large eliminations. The rewrites (convoys onto match h:, applied locals onto refinement) are filed as match-convoy-rewrite-sweep. perf ab --source-patch on round.hthr (106 deletions): wall and gate +3% and separate, counters +1–2%. Synthesized motives spell slightly larger terms than the written ones they replace, and that is the trade this sweep makes.
