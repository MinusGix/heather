---
title: rt: a byte read before a store and used after it is refused by the reflector for functions that write a span
status: closed
labels: [native,runtime,reflector]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-15
---

A function over a span it writes may not use, after a store, a byte it
read before the store:

```heather
fn List::swap_in(mut self span: List<BitVec(8)>, length, i, v: BitVec(64)) → BitVec(64) {
    let old = span.byte_within(length, i);
    span.put_within(length, i, v.truncate(8, 56));
    old.zero_extend(56)
}
```

is refused by the reflector (`rt_file_reflect`, "the span as it was before
a store"; the probe is `swap_in_refused` in
`lib/_tests/native/runtime/rt_file_reflect_tests.hthr`). The program is
sound and the computation layer can say it (`Let(Byte(…), Put(…,
Pure(Var(…))))`): the read is before the store. The reflector cannot,
because the elaborated body has no `let`: `old` is inlined where it is
used, so the read stands after the store as `byte_within(span₀, …)`, a
read of the span as it was, which no `FTm` names. The walk meets it only
when it reflects the value that uses it, after it has emitted the store.

What a swap, a reverse in place and a shift all need. Two routes:

1. The walk keeps the steps it has emitted with levels in place of
   indices (as the pure walk's nodes are before `RSt::at_depth`), so that
   a read of the span at an earlier link of the chain can be bound before
   that link's successor after the fact, and converts to indices once at
   the end.
2. A first pass over the body collects the reads of each state of the
   span, and the walk binds a state's reads before it emits the store
   that ends the state. It reads more than is used on some paths.

Route 1 is the smaller change to the reflector and reads nothing
unneeded.

## Log

- 2026-11-15: Done. The reflector binds a byte of an earlier state before the link that ends that state, and reads the later use as that variable (route 2, per path, so nothing is read on a path that does not use it except where one pure branch of the path's value does). Each path's links and what it ends in are in hand at its end (`rt_file_upto`): `rt_file_plan` scans the later links' operands and the end's values for `byte_within` of a state before the one they are read at (states numbered by `rt_file_state_in`, the same handle or a copy), `rt_file_hoist` binds each before its state's link (`attempt`ed: a read only a proof makes is never used, and one whose index is not known yet is left), and `rt_old_byte` reads the use by state and index from `FileKnown.olds`. Route 1 (levels, retro-inserted binders) was not taken: the walk holds index-form terms in flight (pure arms, `If` arms), which an insertion would leave stale. Still refused, with its reason: a read of the span as it was at an index only a later step computes (`read_back_late_refused`). Probes: `swap_in`, `swap`, `keep_across`, `swap_in_if` reflected and pinned by `refl` in `rt_file_reflect_tests.hthr`; `List::swap` and an insertion sort (`List::sift`, `List::sort_from`) as `runtime fn`s in `runtime_span_tests.hthr` (the sort's key read before `sift` writes and stored after). `compile-x86` certifies `sort_from`, and the native code agreed with `qsort` on 2,000 random arrays. Found on the way: [[measured-loop-inner-if-companions]].
