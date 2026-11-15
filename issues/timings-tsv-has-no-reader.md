---
title: Give --timings a reader, and give "queries" one definition
status: closed
labels: [tooling,performance,benchmarking,diagnostics]
created: 2026-09-16
updated: 2026-09-17
---

`heather check --timings out.tsv` writes 50-plus positional columns. Reading it
is currently `awk -F"\t" '$3==item{print $4/1e6, $8/1e6, $45}'` with the indices
counted by hand off the header, and on 2026-09-16 that went wrong twice in one
session: `$44` is `conv_memo_hits`, not `check_terms` (`$42`), and `$50` is
`eval_drives`, not `eval_steps` (`$48`). Both errors produced plausible numbers.

Worse than the indices: **"queries" is not defined anywhere.**
`docs/elaborator/complete-post-attribution-design.md` §10.2 and
`docs/elaborator/close-body-family-attribution-design.md` both quote a queries column per
item; summing `conv_shortcut_hits + conv_memo_hits + conv_misses` on the same
tree gives a different number (`close_body`: 1 320 910 against the docs'
2 585 801). One of those is a different sum, a different tree, or a different
build, and from the outside there is no way to tell which — so §10.7's table
had to hedge its own column label rather than compare against the chapter above
it.

Wanted: `scripts/timings <file.tsv> [item…]` that prints the five columns every
design doc quotes — total ms, gate ms, misses, queries, evaluator steps — with
one definition of each, and a `--diff a.tsv b.tsv` mode that prints per-item
deltas and says plainly which columns are counts (comparable) and which are
seconds (±5 % on repeat, per this box). Then the definition lives in one place
and a doc's table is reproducible by re-running the script rather than by
reconstructing an awk line.

Secondary, same shape: the header should probably carry a format version, so a
column inserted in the middle does not silently re-point every recorded awk
snippet in the docs.

## What it assumes from elsewhere

- **[[perf-instrumentation-consolidation]]** owns the instrumentation layer the
  columns come from, and what each *means*. Assumed here: only that the meanings are stable enough to be written
  down once; if a column's definition is still moving, that is the finding.

## Log

- 2026-09-16: Filed after mislabelling three columns in one session and being
  unable to reconcile a "queries" number with the two design docs that quote
  one. Sibling paper cut: [[issue-log-text-through-stdin]].
- 2026-09-17: Landed as `scripts/timings`, and the "queries" question is answered — it was
  two questions, and neither was the one the filing asked.

  **The reader.** `scripts/timings <file.tsv> [item…]` prints total ms, gate ms,
  misses, queries and evaluator steps, sorted, with the item-row sum and the run
  row beneath; `--diff a.tsv b.tsv` prints per-item deltas ranked by the first
  column and says which columns are counts and which are seconds. Every column is
  looked up **by name**, which is also why the header gets no format version:
  inserting a column in the middle is already a non-event for anything that does
  not count indices, and a version line would break `crates/cli/tests/timings.rs`,
  which parses line 1 as the header. A name that is absent is a loud exit naming
  the columns that are present, not a silent zero. `--columns` reaches `shortcut`,
  `memo`, `gated` and `delta` beyond the default five; `--list-columns` prints the
  file's own header.

  **"queries" had one definition all along, and the docs quote a different
  column.** A `Tc::conv_ty` query has exactly three outcomes, so
  `conv_shortcut_hits + conv_memo_hits + conv_misses` is every query the kernel
  was asked, and that is what the reader means by the word. The attribution docs
  mean `conv_shortcut_hits` **alone** — `docs/elaborator/complete-post-attribution-design.md`
  §10.1 labels its column that way in the header and is right; the close-body
  chapter's §2 table uses the same column without saying so. Run-wide the two are
  within 1.5 % (memo hits are 5 197 against 14.5 M shortcut hits), which is why
  they were mistaken for each other, and on one item they are 3.7 % apart.

  **The 2 585 801 that would not reconcile was the tree, not the sum.** Measured
  serial on this tree (release, no `--cache`, one furnace job, the showcase's
  960-item closure): the rows that do not go through the receiver chain reproduce
  the close-body table **to the unit** — `complete_post` 3 681 039, `Grammar`
  457 050, `Certified` 357 891, `symbol_span` 71 609, `certify_at` 34 196 — while
  the family's own rows have halved, `close_body` 2 585 801 → 1 316 602 and
  6 773 ms → 2 904 ms. That is `0245b31` (the instance matcher seeing through a
  quote), which landed after `be365f3` and whose own message records `close_body`
  6.8 s → 3.0 s. So the filing's "on the same tree" was the wrong premise, and
  the number it could not reconcile, 1 320 910, is this tree's three-sum.

  A third axis turned up while checking: §10.7's tables are summed over *the
  file's own items*, not over the import closure a run reports, so its 46 497
  misses and the run's 205 997 are both right. The reader's `[item…]` filter is
  that restriction.

  Two properties recorded in `docs/infrastructure/instrumentation-design.md` §4 because they
  would otherwise be re-derived from a table that looks wrong: counts are
  **invariant in the worker count** (width 1 and width 8 report identical run-row
  misses, queries and steps, though a handful of instance declarations shuffle
  counts between items), and times are not — at width 8 the item rows sum to
  57.6 s inside a 28.0 s run, because each item is charged the wall its own gate
  spent and several were spent at once. The reader prints a note when it sees it.

  Also fixed in passing: `docs/showcase/README.md`'s repro command has never
  worked as written — `-L docs/showcase` offers a second `parser_core`, which is
  refused rather than resolved by precedence. It now copies the two files it
  needs. That cost this round one furnace job.

  Column definitions now live in the script; `docs/infrastructure/instrumentation-design.md` §4,
  the two attribution chapters and `CLAUDE.md` point at it rather than restating
  it. Closing.
