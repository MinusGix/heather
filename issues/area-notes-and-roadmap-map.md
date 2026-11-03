---
title: Area notes and a roadmap map: how good each area is, and why
status: open
labels: [tooling,meta,tracker,design]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

The roadmap says where effort goes; nothing says how good each part is.
`scripts/issue areas` reports open-issue counts, which cannot say "solid
but missing its bridge to the real-number laws" or "native compilation
works, but its performance has stalled". The roadmap's "Where it stands"
paragraphs try, and rot: on 2026-11-02 the Mathematics section still said
there was nothing yet for floating point, while six `float-*` submilestones
were marked done in the table above it.

## Area notes

One tracked file per area, and per milestone where it earns one, owning
exactly what no issue or design doc owns: **judgment and observations**.

```markdown
---
node: math-float          # an area or milestone id from docs/roadmap.md
health: usable            # solid | usable | rough | stalled | missing
assessed: 2026-11-02
assessed-by: thread:math  # or minus
starred: true             # Minus only
---
## What exists
A few lines, linking the design docs that own the detail.
## Assessment
Why it has this health, with evidence linked.
## Gaps
- [[float-kahan-bound]]: what is missing and who it hurts ★
## Observations
- 2026-11-02 (minus): …
```

- The roadmap's "Where it stands" paragraphs move into the notes, and the
  roadmap keeps only priority, milestones and their "done when", so it
  changes rarely and stays a reviewed file.
- A note is owned by the thread working its area; it updates Assessment
  and Gaps when it closes work there. Observations are appended by anyone,
  attributed and dated. `starred:` and stars on gaps are Minus's.
- Observations and health are bookkeeping and merge without review; a
  change to Gaps that adds `wanted` work is a proposal
  (`docs/agent-policy.md` §6–§7).

## The map

A **Roadmap** tab in `scripts/issue serve`:

- Areas as lanes in priority order; milestone trees as nodes.
- Node colour is health; a ring shows closed against total issues serving
  it; badges for stars, workaround debt ([[workaround-markers]]) and open
  dependency requests ([[dependency-requests]]); a sparkline of closures.
- Computed flags: **stale note** (closed work after `assessed:`),
  **churning** (issues filed and updated, none closing), **perf stalled**
  (for nodes that name a perf case, a flat headline counter across rounds in
  `perf/snapshots/`), **unplaced** (open issues in the area with no
  milestone).
- A **Review** tab beside it is [[review-by-trust-boundary]].
- A node's panel shows its note, issues, design docs and recent commits,
  with actions: star, add an observation, and *discuss*, which today copies
  a prompt for the area's thread and later starts one.

`serve` is read-only today; the actions make it write files, so it stays
localhost-only and writes through the same functions as the CLI.

## Work

1. The note format, `scripts/issue note <node>` (show, observe, star), and
   validation in `check`.
2. Seed notes for the focus areas and `math-float`, drafted from the
   roadmap, design docs and issue logs, with health left for Minus.
3. The Roadmap tab with health, rings and stars; the computed flags after.

## Done when

Minus can see, per area and milestone, how good it is and why, star a gap,
and have the next round in that area read it.
