---
title: Footprints of effectful functions: Io::Only, its lemmas, and an analysis over ETm
status: open
labels: [effects,proofs,facts]
area: interaction-trees
milestone: [nh-effects]
created: 2026-11-08
updated: 2026-11-08
---

Nothing states which calls an effectful function may make, so a spec or a
pass cannot use "`f` only writes stdout" (`docs/language/effects-locality-design.md`
§3 N1, §5.3). The note's appendix probe reads such a fact off the meaning
by `refl` for one function at a neutral world; this issue makes it a
predicate with lemmas and a producer.

## Scope

- `Io::Only(P, f)` (in the `linux_world_co` family): for every world `io`
  and every `Returns(f(io), m)`, `m.past` is new exchanges, each satisfying
  `P`, prepended to `io.past`. Closed under `Io::reads_bind`'s sequencing
  and `Io::iterate` (a body's footprint is its loop's), and invariant under
  `Eutt`.
- A verified analysis over `ETm`/`ELoop` (every `Invoke`'s effect kind and,
  where the descriptor operand is a literal, the descriptor) whose `True`
  gives `Io::Only` of the meaning, so a compiled function's footprint costs
  one evaluation (`docs/compilation-vision.md` §2.3, producer 1).
- Published as a fact beside `Compile(f)` (`docs/native/facts-on-demand-design.md`),
  with one consumer: a probe that reorders two calls with disjoint
  footprints, or a spec that uses it.

## What it assumes from elsewhere

- **[[world-separable-frame]]** owns the frame theorem that makes a
  footprint useful against the environment. Assumed here: nothing.
- **[[facts-on-demand]]** owns how facts are requested and found.
