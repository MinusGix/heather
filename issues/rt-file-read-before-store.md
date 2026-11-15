---
title: rt: a byte read before a store and used after it is refused by the reflector for functions that write a span
status: open
labels: [native,runtime,reflector]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-11
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

- 2026-11-15: The sort example (`examples/sort`) works around it with a shift-insert that takes its key as a word parameter; a neighbouring refusal it hit is `runtime-mut-self-let-read-walk` (filed and fixed in its own PR).
