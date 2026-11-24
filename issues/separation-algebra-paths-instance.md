---
title: Separation algebra at a store's paths, and an access-map frame theorem
status: open
labels: [algebra,ownership]
area: mathematics
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

The separation algebra is built (`docs/library/separation-algebra-design.md`):
the `Pcm` class, exclusive footprints over `SpanSet`, fractional shares, the
access map, and the store frame theorem against byte memory through a
`Footprint` frame. Three pieces were left for when their inputs exist.

## Scope

- **A `Pcm` instance at a store's paths** (`docs/language/ownership-design.md`
  §10.7: a token is the store's value split where paths are apart). The
  carrier is a set of paths held, with shares, composing where `Apart` holds;
  the bridge is that a write through a held path keeps every predicate local
  to a composed frame of paths, the path-level form of
  `Footprint::store_keeps`.
- **The access-map frame theorem**: `Footprint::store_keeps` with an
  `Access` frame (local to the addresses where the frame holds a positive
  share) and a whole held by the writer, so a frozen view's predicate is kept
  by a store elsewhere and the store is refused where the view is live.
- **A decider for `Access::Valid`** of holdings built from finitely many
  footprints and shares (a list of `(SpanSet, Share)`), with sound and
  complete certificates, so a judgment can check a closed holding by
  evaluation.

## Done when

The soundness round can state "this path's holder owns it exclusively"
and "this view's footprint is frozen" as `Pcm` elements at paths, and cite a
frame theorem for each.

## What it assumes from elsewhere

- **[[ownership-paths]]** owns paths, `Valid` and `Apart`. Assumed here: only
  that `Apart` of two paths is a proposition with a decider.
- **[[separation-algebra-ownership]]** owns the class and its instances.
