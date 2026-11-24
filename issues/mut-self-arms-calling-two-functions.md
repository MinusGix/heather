---
title: A mut self runtime fn whose arms call two different functions is refused with "trivial proves True"
status: open
labels: [native,runtime-fn,elaboration]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-24
updated: 2026-11-24
---

A `mut self` `runtime fn` of a laid record whose arms end in calls of two
different functions of the record is refused by the elaborator with an
error that names neither:

```heather
runtime fn Arena::push(mut self a: Arena, h, x: u64) → u64 {
    if hb: h < 14 {
        if room: a.heap.at(h + 2) < a.heap.at(h + 1) { a.push_in(h, x) } else { a.grow_push(h, x) }
    } else { a.push_in(h, x) }
}
```

over `lib/native/runtime/arena.hthr`'s `Arena` (with `grow_push` a `mut
self` function: `let g = a.grow(h); if grew: g = 1 { a.push_in(h, x) }
else { 0 }`) answers "`trivial` proves `True`, but `u64` is expected
here", at the function's closing brace. The same shape with one call and
a literal in the other arm (`… { a.push_in(h, x) } else { 0 }`) is
taken, and so is `if hb: h < 14 { a.push_in(h, x) } else { 0 }`;
binding the cap and length with `let`s first changes nothing.

Who waits: a `push` with branch equations. The arena's `push` is written
instead as a call, a test of its answer and a call (`let r =
a.push_in(h, x); if full: r = 2 { … } else { r }`), which compiles and runs
but gets no branch equations, so its meaning is read off `push_in_abs`
and `grow_abs` (`arena_laws.hthr`) rather than proved of `push` itself.

## Done when

The function above elaborates (or is refused with a reason that names the
shape), and the arena's `push` is written with the room test first, with
a law `push_abs` (a push that answers 1 appends) over it.
