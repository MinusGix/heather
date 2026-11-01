---
title: "Unique: the second fact on demand, with in-place update as its consumer"
status: open
labels: [compiler, ownership, design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-01
updated: 2026-11-01
---

`Unique(p, k)`: the buffer the `k`th update of `p` consumes is not read
again, neither by that name nor by any name sharing its storage. Consumer:
compile that update in place instead of copying. Producers, cheapest first
(`docs/facts-on-demand-design.md` §7):

- the ownership setup's judgment, as a plain evidence rule
  `Unique::of_owned({p}, {k}, o: Owned(p) := infer)`, `Owned(p)` a linearity
  check that evaluates to `True`;
- a per-site liveness check, verified once and answered by evaluation, as
  the compiler's budgeted fallback.

The mechanism (search rules, `Synth`, `request`, proof-carrying sites) is
[[facts-on-demand]]'s and carries over unchanged. What `Unique` adds is a
semantics where aliasing is observable: the compiler's theorem is a
simulation against a store of slots with a name→slot map, whose invariant is
that every live name reads its slot. That store is `rt`'s memory and the
ownership setup's, so this is built over them rather than over a toy store
that would be discarded.

## Acceptance

- A program with a linear update compiles it in place, the fact from the
  ownership judgment; a non-linear program whose consumed buffer is dead
  anyway gets it from the liveness fallback; one that reads the old buffer
  after the update keeps the copy.
- The compiler's theorem is proved once, for any facts.

## What it assumes from elsewhere

- **[[facts-on-demand]]** owns the request and the order of producers.
- **[[ownership-discipline-over-code]]** owns the ownership judgment.
  Assumed: it is a decidable judgment over reflected code with one
  soundness theorem.
- **[[runtime-fn-reflected-language]]** owns `rt` and its memory.

## Log

- 2026-11-01: Filed from the facts-on-demand prototype, which built
  `InBounds` end to end and designed this one (design §7).
