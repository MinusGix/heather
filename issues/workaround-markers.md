---
title: Workaround markers: name the issue that retires each workaround, and count them
status: open
labels: [tooling,meta,tracker]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

`docs/agent-policy.md` §4 (option 3) owns the rule: a round may work around
a weak foundation, but every place the workaround lives carries a marker
naming the issue that would retire it.

```
// workaround: [[real-completeness-interfaces]]
```

The same `//` comment serves Rust and `.hthr`. This issue owns the tooling
that makes markers count.

## Work

- `scripts/issue check` scans `crates/`, `lib/`, `scripts/` for
  `workaround:` markers and reports a slug that does not exist, and a
  marker whose issue is closed (the workaround should now be retired).
- `scripts/issue workarounds [--area A] [--milestone M]`: markers grouped
  by the issue that would retire them, with file and line, and the area
  and milestones of the file's owning issue where known.
- Counts per area and milestone in `scripts/issue areas` and the web
  viewer's Areas tab ("debt").
- The done-gate: `check` warns when a milestone is `done` in
  `docs/roadmap.md` while markers point at open issues serving it, unless
  the roadmap's log has a waiver line naming the milestone.

## Not in scope

Converting the existing `TODO`/`FIXME`/`HACK` comments (about thirty-five across
`crates/` and `lib/` on 2026-11-02). A gardener pass may propose markers for
the ones that are workarounds ([[tracker-gardener]]).

## Done when

A workaround without a valid marker is caught by `check`, and the debt
count per milestone is visible where milestones are.
