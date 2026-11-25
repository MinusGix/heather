---
title: A found proof does not read a test over a word bound by let to a read of an array field
status: open
labels: [native,runtime-fn,tactics]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Met writing `Arena::push_fit` ([[bv-omega-fits-through-wrapping-sum]]): in a `runtime fn` of `Arena`, a call with found proofs over words bound by `let` to reads of the heap fails, even for a proof the code's own test gives.

```heather
let base = a.heap.at(h);
let cap = a.heap.at(h + 1);
let len = a.heap.at(h + 2);
if room: len < cap {
    if ok: window_fits(base, cap, 16) {
        let old = a.store(base, cap, len, x);   // `inside := bv_omega` refused
```

The default runs in the caller's hygienic context (`Cx::hygienic`, `__caller_` names). The tests there are `__caller___if_bitN: unsigned_lt_bit(at(a.heap, h + ofNat(2), inside := squash(bv_omega)), …) = True`: the facts are over the reads, not over `len`, and a read carries its own found `inside` as `squash(…)` of a proof that has no source spelling. `omega` lists them as "skipped unspellable facts … `toNat(at(…, inside := squash(bv_omega)))` has no source spelling here", and `bv_omega`, whose comparison bridge needs the operands spelled, leaves the test out. So `store`'s `inside` (from `room`) is refused, not only its `fits`.

`Arena::store_item` takes the header's words as parameters instead, as `put_item` does, and `push_fit` passes the reads to it; that compiles.

## Wanted

A test over a let-bound word reads as a fact about the word a tactic can name: either the fact is stated over the `let`'s name, or a read's found proof spells (its source was `bv_omega`, and a proof term's spelling as the tactic that wrote it is what a re-elaboration would do). Then `store_item` folds back into a `push_fit` that reads the header itself.
