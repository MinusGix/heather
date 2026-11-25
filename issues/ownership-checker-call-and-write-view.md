---
title: The ownership checker's second experiment: a call with a &mut window and a returned view
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The second experiment of `docs/language/ownership-design.md` §15.6: one call with a `&mut` window and a returned view, over [[ownership-checker-spike]]'s module (`lib/lang/ownership/place_check.hthr`). Library only.

## Scope

- **Write views**: `let w = &mut x[lo..lo+n]`, writes through `w`, and the place's `out(viewer)` state; eager write-back (§15.2) in the meaning, so `eval1` updates the place after each statement that may change `w`.
- **Deaths**: a binding that dies at a site, from the annotation (§15.3), restoring `whole` or removing a viewer.
- **One call**: a callee's signature as data (modes, the region of its result, whether the result is fresh or one of its parameters), checked at the call; the callee's own `check_sound` as what the caller cites.
- **A returned view**: the call returns a read view of its `&mut` argument's window, frozen in the caller after the loan ends.

## What the first experiment says will change

From the spike's log (2026-11-25): the place state stays per object, but an object's state becomes per span (whole, frozen windows, out windows) instead of one holder and a table of read views; `Residual` becomes a sum (apart, and below its length for a write through a window); the meaning's object environment must allow write-back to a name (the spike's is append-only); and `Inv.held` weakens to "the buffer holds the holder's value outside its out windows, and each out window holds its viewer's value", which is where "a usable place reads its value" is first tested against a loan. The step lemmas for get, read, view and clone carry over unchanged; the set step's frame becomes `PathIn::agree_apart` over a window path instead of an element.

## Done when

The fragment with those four additions has `check_sound`, with one accepted program per addition and a `¬` control for each refusal, and the log answers whether the place-state invariant still suffices.
