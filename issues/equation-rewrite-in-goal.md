---
title: Rewrite a goal along an equation without writing j's motive
status: open
labels: [frontend,elaboration,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-07
updated: 2026-10-07
---

Rewriting a goal along an equation is written as a transport with a
hand-written motive:

```heather
j(sym(rsi_value), λ w _ => ReadsFrom(file, page, source0, w), λ i => refl)    // elf64_stat_width.hthr:707
```

There are about 714 `j(` uses in the library, most of them this shape. The
match-motive work already abstracts a scrutinee's occurrences from the goal
(`docs/goal-motive-synthesis-design.md`), and the contextual-rewrite rounds
do the relational case (`docs/contextual-rewrite-round.md`).

Wanted: the `=` case at a checking position. Given `h: a = b` and a goal
mentioning `b`, abstract `b`'s occurrences to build the motive, and elaborate
to `j` (a `rewrite h` form, or Lean's `h ▸ e`). Occurrence and direction
controls as [[relational-rewrite-controls]] defines them.

## What it assumes from elsewhere

- **[[relational-rewrite-controls]]** owns direction and occurrence controls
  for relational rewrites. Assumed here: only that the `=` case can share
  their spelling.
- **[[goal-motive-by-scrutinee-abstraction]]** (closed) owns occurrence
  abstraction for motives. Assumed here: only that it can be reused.
