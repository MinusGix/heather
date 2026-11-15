---
title: prelude::class CollectionLiteral checks at 70–105 µs per evaluator step, 60–100× the median, in every file
status: open
labels: [performance,kernel,prelude,traits]
area: kernel
created: 2026-09-22
updated: 2026-09-23
---

The 2026-09-23 perf snapshot's per-step outlier list names one declaration,
the same one in every corpus file:

```text
24.8ms  gate 82%  lower 10%  misses 14  steps 192  105.5 µs/step  rescope 965  omega: prelude::class CollectionLiteral   (file median 1.2 µs/step)
16.3ms  gate 86%  lower 13%  misses 14  steps 192   72.5 µs/step  rescope 965  nat: prelude::class CollectionLiteral     (file median 1.0 µs/step)
15.8ms  gate 85%  lower 13%  misses 14  steps 192   69.9 µs/step  rescope 965  calc_parser: prelude::class CollectionLiteral (file median 1.7 µs/step)
```

192 evaluator steps and 14 misses should not cost 16–25 ms of kernel time:
each step is 60–100× the file's median, so the time is in what a step
*touches*, not in how many there are. The class is telescoped and its spine
is dependent (`fromLiteral` mentions `element`;
`docs/elaborator/telescoped-record-projections-design.md`), so a large type rebuilt or
compared per step is the first suspect, not a proven one.

It is small in absolute terms, but it is in the **prelude**, so every check
of every file pays it, cold and uncached, whatever the file's size — which
makes it a fixed tax on the small-file end of the corpus (it is a visible
fraction of `nat`'s 0.2 s).

Method: `--only` cannot select a prelude item, so probe it with an empty
module and `--timings`, then `HEATHER_VALUE_METRICS=1` under
`--features value-metrics` for what the steps touch
(the value-metrics build's per-module `ValueMetricsSnapshot`; run without `--cache`, or the declaration is accepted from the cache and nothing is measured).

## Log

- 2026-09-23: 2026-09-23 suite-wide reading (HEATHER_SUITE_DECLS=1 fast lane): the class is checked by 1,855 test threads, 2,531 times, 6.28 s summed — the prelude tax, measured across the suite rather than per file.
- 2026-09-23: 2026-09-23 suite-wide rows add a wrinkle: of the prelude module's 6.9 s over 1,855 tests, most is the images & cache phase group (image_*, merkle_walk, cache_hash), not the kernel gate — so the per-test prelude price is not only this class's check. Split the two before sizing a fix (dashboard: What the suite elaborates → prelude row).
