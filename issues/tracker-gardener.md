---
title: A tracker gardener: tie issues together, and propose placements in batches
status: open
labels: [tooling,meta,tracker]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

`docs/agent-policy.md` §7 owns what the gardener may do on its own and what
it proposes. This issue owns the checks and their output.

Why: on 2026-11-02 the tracker held 525 open issues, 379 of them serving no
milestone. `language` had 144 unplaced open issues with a median of 45 days
since their last update; `kernel` and `infrastructure` were almost entirely
unplaced. Filing has been accelerating (459 issues created in October). No
person reads that by hand, so the tracker has to tie itself together.

## Applied directly (listed in the digest)

- **Links**: add wiki links between open issues that cite the same files,
  `code:` references, or declarations. Logged as one line on each.
- **Area**: set `area:` when exactly one area's lane footprint
  (`docs/roadmap.md`, Parallel lanes) covers the issue's code references.
- **Duplicates**: flag pairs with a log line on each; never merge.
- **The two hand checks** in `issues/README.md`: open issues whose last log
  says landed or done, and open issues nothing links to.
- **Stale notes**: area notes whose `assessed:` predates closed work in
  their area ([[area-notes-and-roadmap-map]]).

## Proposed in batches

- Close, merge duplicates, add or change a milestone, add `wanted`, mark
  intentionally unplaced, promote a cluster to a predicted need.
- Batches of about twenty, grouped by cluster, each written as one decision
  with a default. Accepting a batch applies it in one commit.

## Work

- `scripts/issue garden [--apply] [--propose]`, stdlib like the rest of the
  script: the deterministic checks first (links by shared code references,
  the README's checks, stale notes). Clustering and duplicate detection can
  start as a thread run over `scripts/issue index`, with the script holding
  only the bookkeeping.
- `milestone: [none]` as the spelling of *intentionally unplaced*: `check`
  accepts it, and `areas` counts unplaced issues separately from it.
- A digest (what was applied, what awaits a decision) in the shape
  `scripts/plan-digest` already writes.
- Scheduling: nightly, beside the master sentinel, once
  [[bookkeeping-auto-merge]] lets its commits land without review.

## Done when

The unplaced count is falling batch by batch, and the README's two hand
checks are no longer by hand.
