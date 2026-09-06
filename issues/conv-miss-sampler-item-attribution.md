---
title: Attribute conversion-miss buckets to the declaration being checked
status: open
labels: [tooling,performance,kernel,elaboration]
created: 2026-09-06
updated: 2026-09-06
---

The `Tc::conv_ty` miss sampler ([[perf-profile-build-target]], landed
2026-09-06 behind `value-metrics`) says *which two spellings met* — head
pair, count, total ns, an exact first-difference excerpt — but not
*where*. Attributing the `Sum` vs `Sum` family of
[[inductive-spelling-codes-nonrecursive]]'s round to `List<Instruction>`
values took reading the excerpt's character offsets against the library's
declarations by hand; a row keyed by declaration would have said it
outright.

## Shape

- The elaborator already brackets each declaration for item timings
  (`enable_item_timings`, `take_item_timings`, `lib.rs`); set a current
  item name on the `ValueMetrics` collector around the same bracket, and
  key the miss table by `(item, expected head, inferred head)` — or keep
  the head-pair table and add a per-item breakdown of its top rows.
- Report: per bucket, the top three items by total ns; per item, its top
  bucket. Print from the x86 rail beside the existing table.
- Keep the excerpt per bucket (one rendering), not per item.
- No cost outside the feature: the collector pointer is already
  `cfg`-gated; the item name is a `Cell<Option<Rc<str>>>` on it.

Acceptance: on the five-node FunctionIR/x86 module the `Sigma`/`Sigma`
and `Pi`/`Pi` rows of [[emission-site-respell-audit]] name their items
without a manual search.

## What it assumes from elsewhere

- **[[perf-profile-build-target]]** owns the sampler and the profiling
  tooling. Assumed here: only the sampler's bucket table.
