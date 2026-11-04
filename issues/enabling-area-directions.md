---
title: Give language, kernel and infrastructure directions and milestones of their own
status: open
labels: [meta,roadmap,decision]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Decision issue for Minus. `docs/roadmap.md` now lets enabling work invest
ahead of demand (`docs/agent-policy.md` §1), but the enabling areas still
have no direction of their own, and `kernel` and `infrastructure` have no
milestones. On 2026-11-02 they held most of the unplaced backlog: 144
unplaced open issues in `language`, 44 in `kernel`, 51 in
`infrastructure`.

## Proposal shape

Each enabling area gets a one-line direction and two or three milestones,
judged by what they unlock rather than by a customer's slice, and the
`wanted` label marks the issues that serve them ahead of a puller.
Candidates to choose from, not decided:

- `language`: the two milestones it has (`lang-sequencing`,
  `lang-proof-modularity`), plus diagnostics good enough that a model
  working in Heather recovers from an error without guessing (the thesis
  `issues/ai-facing-tooling.md` owns).
- `kernel`: checking cost as a milestone stated in exponents, as
  `CLAUDE.md` asks costs to be stated; the extensions the directions keep
  needing as a predicted-needs list.
- `infrastructure`: an inner loop fast enough to iterate in (the perf Minus
  has named as harming iteration), stated against `scripts/perf report`'s
  corpus; the tracker work this policy files.

## Work

- Minus picks the directions and milestones; they go in the roadmap's
  tables, with a log line.
- A first gardener batch ([[tracker-gardener]]) proposes milestones or
  *intentionally unplaced* for the 239 unplaced enabling issues against the
  new milestones.

## Done when

Each enabling area has a direction row and at least one milestone in
`docs/roadmap.md`, and its unplaced count has been triaged once.
