---
title: a measured mut self runtime fn that binds a read with `let` before a branch gets no companions
status: open
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-15
updated: 2026-11-15
---

Writing the sort example's inner loop (`examples/sort/sort.hthr`,
`List::insert_below`) with the byte below `j` bound once,

```text
runtime fn List::insert_below(mut self s: List<u8>, n, j, x: u64) → u64 decreases j.toNat() {
    if h: 0 < j {
        let below = s.byte_within(n, j - 1);
        if larger: x < below.zero_extend(56) { s.put_within(n, j, below); s.insert_below(n, j - 1, x) }
        else { … }
    } else { … }
}
```

is refused with "a marked call this walk cannot read": the generated
`f::unfold`/`f::ext` are not produced for a `let` of a span read ahead of a
measured branch in a `mut self` body. Spelling the read at each use (the
example's form) is accepted, and the compiler shares the two reads anyway,
so the cost is only in the source. The walk should read a `let` of a
`List<u8>` read the way it reads the read inline.
