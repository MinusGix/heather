---
title: Dependency requests in the tracker: degraded-by and slowed-by beside blocked-by
status: open
labels: [tooling,meta,tracker]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

`docs/agent-policy.md` §2 owns what a dependency request is and when one is
granted (§3). This issue owns the tracker support for it.

A round hurt by a missing or weak foundation names the issue that would fix
it, with one of three kinds. `blocked-by:` exists already; two fields are
new:

- `degraded-by: [slug, …]`: the round can proceed, but its result will be
  worse code without the dependency.
- `slowed-by: [slug, …]`: iteration cost (elaboration, checking, build time)
  is what the dependency would fix.

## Work

- `parse_issue` reads both as lists (today only `labels`, `blocked-by` and
  `milestone` are).
- `scripts/issue check` validates them like `blocked-by`: the slug exists,
  and a closed dependency on an open issue is reported (the request is
  probably satisfied and the round can resume).
- `scripts/issue wants [--area A] [--kind K]`: open requests, grouped by
  dependency, each marked **granted by default** or **needs Minus** by the
  rules of §3 (serves an open milestone, `wanted`, starred, or listed in an
  area note's gaps; otherwise needs Minus). The depth guard counts
  request chains.
- `show` prints the three kinds in both directions, as it already does for
  `Referenced by:`.
- The web viewer shows requests as typed edges in the graph, and an open
  request count on each issue.

## Done when

The fields are read, checked and listed, and the policy's grant rule can
be computed from tracker state alone, with no thread judging it.

## What it assumes from elsewhere

- **[[area-notes-and-roadmap-map]]** owns area notes and stars. Assumed
  here: only that a note's gaps list names issue slugs and stars are
  machine-readable. Until that lands, "wanted" is the label and milestones
  only.
