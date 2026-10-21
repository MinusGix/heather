---
title: A tactic run is limited to about a thousand requests by its continuation chain
status: open
labels: [metaprogramming,performance,tier2]
area: tactics
milestone: [tac-host-interface]
created: 2026-10-21
updated: 2026-10-21
---

A `by t` run fails once the tactic has answered about a thousand requests:
reading the final `Pure` leaf runs out of the evaluator's nesting depth
(`NATIVE_DEPTH_LIMIT`, 1024), so the error says "ran out of fuel or nesting
depth, after N requests". Every step before it is cheap and constant (about
80 µs after the `elim_W` memo of the same round); only the force that reads
the *result* is deep, and its depth grows by one per answered request.

## What is known

- Measured with a tactic that asks `n` `Defeq` requests in a row
  (`spin(n)`): `n = 900` succeeds, `n = 1100` fails at the final step, and
  raising the per-force fuel 64× does not move the threshold, so it is the
  depth rail and not fuel.
- Likely mechanism, not yet confirmed: `Tac` is a tier-2 inductive, lowered
  to `Σ(t : W). canon t` (docs/inductive-tier2-w-lowering.md). A `match` binds
  the continuation `k` so that `k(x)`'s proof component is projected from the
  *scrutinee's* proof. Each resume therefore chains the new tree's proof onto
  the previous one, and only a leaf arm (the `J` at `Pure`) forces that
  proof, which walks the whole chain at once.

## Possible fixes

- Host side: force the proof component of each new tree as it is made, so
  the memo keeps the chain one deep. This needs the proof's whnf to actually
  cut the chain, which is the unconfirmed part.
- Library side: end a run with a request (`Done(e)`) rather than a `Pure`
  leaf, so the host never matches the deep leaf.
- Encoding side: a tier-2 match whose leaf arm does not need the chained
  proof (owned by [[tier2-fragment-extensions]]).

Not urgent for round 1's tactics (`assumption` makes one request per local),
but a search tactic in `tac-first-port` can exceed a thousand requests.

## What it assumes from elsewhere

- [[host-elaboration-interface]] owns the host loop (`crates/elab/src/host.rs`).
