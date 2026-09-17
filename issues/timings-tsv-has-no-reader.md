---
title: Give --timings a reader, and give "queries" one definition
status: open
labels: [tooling,performance,benchmarking,diagnostics]
created: 2026-09-16
updated: 2026-09-16
---

`heather check --timings out.tsv` writes 50-plus positional columns. Reading it
is currently `awk -F"\t" '$3==item{print $4/1e6, $8/1e6, $45}'` with the indices
counted by hand off the header, and on 2026-09-16 that went wrong twice in one
session: `$44` is `conv_memo_hits`, not `check_terms` (`$42`), and `$50` is
`eval_drives`, not `eval_steps` (`$48`). Both errors produced plausible numbers.

Worse than the indices: **"queries" is not defined anywhere.**
`docs/complete-post-attribution-design.md` §10.2 and
`docs/close-body-family-attribution-design.md` both quote a queries column per
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
