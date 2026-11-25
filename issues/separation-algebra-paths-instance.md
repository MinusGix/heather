---
title: Separation algebra at a store's paths, and an access-map frame theorem
status: closed
labels: [algebra,ownership]
area: mathematics
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
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

## Log

- 2026-11-25: Discharged by [[ownership-library-join]] (2026-11-25), as designed in `docs/library/separation-algebra-design.md` §7:

  - **The instance at paths**: `Held` (`lib/std/data/set/held.hthr`), finitely many footprints at shares, denoting an access map; `Pcm<Held>(Held::Same, Held::join, Held::Valid)`, every law read through `Held::share_at_append`. The carrier holds paths' footprints, not paths: `Apart` of paths has no general decider and paths no decidable equality, so a carrier of paths could not decide its validity. A path's holder holds `Held::own(span)`, a view `Held::at(span, q)`; an owned path's holding composing with any positive holding of another makes the two `Apart` (`Held::apart_of_valid`, in `lib/std/machine/access_frame.hthr`); keys the same over a store's slots (`Held::key`, `Held::keys_apart_of_valid`). Sound for `Apart`, not complete (footprints over-approximate; views compose overlapping).
  - **The access-map frame theorem**: `Access::store_keeps` and `Access::store_keeps_sep` (`access_frame.hthr`), `Footprint::store_keeps` with the frame an `Access` and locality at its positive addresses (`Access::Local`); `Held::store_keeps` with a `Held` frame. The path-level form: `Held::path_keeps`, `Held::path_keeps_sep`, and `Held::view_kept` (a frozen view's predicate kept by every write of a holder it composes with). A store where the view is live: `Held::view_refuses_store`.
  - **The decider**: `Held::valid`, sound and complete (`valid_sound`, `valid_complete`), checking every address below the last end. Its cost is linear in that bound; an endpoint decider is filed as [[held-endpoint-decider]].

  Done-when met: "this path's holder owns it exclusively" is `Held::own(span)` with `Held::own_excludes` and the frame theorem `Held::path_keeps`; "this view's footprint is frozen" is `Held::at(span, q)` with `Held::view_kept` and `Held::view_refuses_store`. Probes: `lib/_tests/std/data/set/held_tests.hthr`, `lib/_tests/std/machine/access_frame_tests.hthr`.
