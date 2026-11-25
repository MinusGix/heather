---
title: A function that only reads a laid record, with a branch whose arm calls another function of the record
status: open
labels: [native,runtime-fn,reflector]
area: heather-in-heather
created: 2026-11-25
updated: 2026-11-25
---

`runtime fn Arena::d(self a: Arena, i: u64) → u64 { if i < 4 { a.top_of(i) } else { 0 } }`, where `Arena::top_of(self a: Arena, k: u64) → u64` is another function of the record that only reads it, is refused with a misleading "rt: a local that is not runtime data (a proof, or a match's payload)". No erased parameter is involved: met in [[runtime-record-calls-erased]] (2026-11-25), where the same shape with an arena window's `a.read(…)` fails the same way. The `mut self` form of the same function compiles (`Arena::port_first`, `lib/_tests/native/runtime/runtime_ports_tests.hthr`), and so does a `self` function whose tail is the call with no branch (`Slots::get_first`, `runtime_erased_tests.hthr`).

Where it likely is: `rt_held_tail`'s reading path (`reads && !rt_held_arm`, `lib/native/runtime/rt_held_reflect.hthr`) makes the calls `Ready` finds and then walks the arm with the pure reflector (`rt_go`); in a branch arm the call is evidently not made first, so `rt_go` reflects it as a plain call and walks into its arguments. Not investigated further.

## Done when

The function above compiles with its `runs_held`, or is refused by name with the form to write.
