---
title: A course-of-values window costs O(d²) nodes in its annotations; recorded before it matters
status: open
labels: [elaboration,performance,kernel]
created: 2026-08-17
updated: 2026-09-18
---

An accumulator issue in the sense
`issues/perf-tracking-consistent-environment.md` wants: filed at the moment the
shape is known, with **no measurement**, so that if the cost ever shows up
there is something to read instead of a rediscovery.

[[recursion-at-deeper-subterms]] emits, for a recursion carrying `d` values, a
Σ-tuple whose `i`-th component type is `M[pred^i z]`. `pred` is itself an
`elim_Nat` — five nodes — so the annotations alone are

    Σ nesting:      d-1 pairs, each carrying its tail type
    pred chains:    0 + 1 + … + (d-1) = O(d²) pred nodes

and every `fst`/`snd` in the body repeats the tail annotation it projects
through. The convoy multiplies this by the nesting: each nested `match` on the
chain carries a Π whose domain is the whole window type again.

**2026-09-18, the same shape on chain-shaped `Wf` declarations**
([[list-course-of-values-recursion]]): `pred` becomes `tail_D`, which is a
whole `elim_Wf` with a case tree on the tag rather than five nodes. So the
`O(d²)` *count* is unchanged and its **constant is larger** — by roughly the
size of one no-confusion-style projection per link. The customer's `d` is 4
(`utf8::decode`), the largest in the tree; the convoy multiplier is the same,
and the levers below all apply verbatim with `tail_D` in `pred`'s place. Lever
1 has no `Wf` counterpart — there is no one-node "child of" former to add — so
lever 2, sharing the tail types, is the one that would carry both cases. Not
measured, per the accumulator discipline.

## Why it is not a problem now

`d = 2` for every `Nat` customer that exists (`half`, `Even`, `Odd`, `fib`),
`d = 3` for `trib` in the tests, `d = 4` for `utf8::decode`. At those sizes
the tuple is smaller than the arm it sits in. The full suite showed no wall-clock change worth naming.

## What would make it one

- A `d` that grows: a digit-wise recursion at base 10, an interpreter that
  reads a fixed window of previous states.
- **Conversion**, not construction. The annotations are compared by
  `conv`, and a `pred` chain is an `elim_Nat` whose scrutinee is another —
  neutral at an open argument, so comparison walks the whole chain each time.
  This is the interaction to watch, and it is the same shape
  [[conversion-cost-at-large-values]] tracks for numerals.

## The levers, if it ever needs them

1. **A kernel `pred`**, or a `Nat` predecessor that is one node rather than an
   `elim_Nat`. Cheapest, and it makes the annotations linear in `d` rather than
   quadratic. Costs a former, which [[kernel-v1-extensions]] would have to want
   for other reasons too.
2. **Share the tail types** — the same `Type` is rebuilt per projection today
   and could be an `Rc` handed around. Pure implementation, no semantic change.
3. **Left-nested rather than right-nested tuples**, which shortens the deepest
   projection but lengthens the shallowest; only worth it if profiles say the
   deep end dominates.

## What it assumes from elsewhere

- **[[recursion-at-deeper-subterms]]** (closed) owns the emission shape.
  Assumed here: that component `i` is the motive at `pred^i`, its §3.
- **No numbers here on purpose**, per the accumulator discipline
  [[perf-tracking-consistent-environment]] states. If this is ever acted on,
  the protocol is `scripts/bench` against the recorded baseline, not a
  stopwatch on one run.
