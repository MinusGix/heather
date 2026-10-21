---
title: Rewrite a goal along an equation without writing j's motive
status: closed
labels: [frontend,elaboration,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-07
updated: 2026-10-21
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

## Log

- 2026-10-21: landed as `rewrite(h₁, …, hₙ, e)` at a checking position
  (`docs/equation-rewrite-design.md`, `crates/elab/src/rewrite.rs`). Each
  equation rewrites its left side to its right side in the goal as written
  (then one exposed layer), in turn; `sym(h)` reverses; `at := k` /
  `at := [k, …]` selects occurrences of one equation
  (`Type::abstract_local_at`). The motive is checked to be a type before the
  kernel gate. Library: the `=` transports in the std arithmetic and list
  modules converted where they checked; sites whose motive states a reduct of
  the goal, or mentions the proof, keep `j`. Out of scope, recorded in the
  design §5: relations other than `=` (that is
  [[relational-rewrite-controls]]'s), rewriting in hypotheses, matching up to
  conversion.
