---
title: Attribute conversion-miss buckets to the declaration being checked
status: closed
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

## Log

- 2026-09-06: LANDED. `ValueMetrics::set_current_item` (crates/kernel/src/value.rs, a `RefCell<Option<Rc<str>>>` behind `value-metrics`, a no-op without it); `Elaborator::elab_module_source` sets it to `item_timing_name(item)` for the whole item bracket (minting between items included) whenever a collector is enabled and clears it after. Each `ConvMissBucket` keeps a per-item (count, ns) map; `conv_miss_report` prints, under every bucket, its top three items by total ns, and after the table one `conv miss item <name> total=… top expected=… inferred=…` line per item, heaviest first. The excerpt stays one per bucket. The x86 rail prints it with the existing table (nothing changed there — same `value_conv_miss_report`). `scripts/measure-x86-conv-miss` is the one-script, ulimit-wrapped five-node run for furnace (`DUMP=<path>` also dumps the generated module). **Datum, 2026-09-06, five-node module before the audit:** `Sigma`/`Sigma` 450 → `value_{4,5,6,7,8}_after_node_*` 90 each; `Pi`/`Pi` 150 → `gprs_congruent` 56 + 14 per value theorem; `Sum`/`Sum` 312 → `graph_1..5` 36 each; `Sigma`/`El⌜⌝` 154 → 25 per value theorem; per item, `gprs_congruent` was the heaviest at 0.385 s. That column plus the generated module's text named the pairs of emission sites for [[emission-site-respell-audit]] without a manual search, which was the acceptance. Not landed: the diagnosis that finished the job also needed the *kernel term form* at the miss (a temporary check/infer stack of variant names in `Tc::tm_check`/`tm_infer` and a `Backtrace::force_capture` in the first excerpt of each bucket, both under the feature) — cheap to re-add, noted on [[perf-profile-build-target]] as the next column if a round wants it permanently.
