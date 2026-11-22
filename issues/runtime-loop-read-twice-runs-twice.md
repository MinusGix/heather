---
title: A runtime loop whose record state is read twice afterwards runs twice
status: open
thread: Rebuild loops on one combinator
labels: [native,runtime-fn,sharing]
area: heather-in-heather
created: 2026-11-21
updated: 2026-11-21
---

A `runtime fn` whose loop has a record state and reads two or more of its
locals after the loop runs the loop once per read. In

```heather
runtime fn three(n: u64) → u64 {
    let mut a: u64 = 0; let mut b: u64 = 1; let mut i: u64 = 0;
    while i < n decreases (n - i).toNat() { a := a + 1; b := b + 2; i := i + 1; }
    a + b
}
```

the reflected program has two `Iterate` nodes, one under `a`'s read and one
under `b`'s: the elaborator writes `let #for = <loop>; let a = #for.a; …`, and
the elaborated body repeats a `let`'s value at each use
([[elaborated-let-sharing-lost]]). The reflector's value numbering would
merge two equal nodes, but it leaves `Iterate` out (`RSt::finish`), and
the copies would not compare equal anyway: their test and body are reflected
at different depths, so their indices to outer variables differ.

The lifted loops this replaced did not pay it, since a repeated call of
`f#run` is numbered once. Either fix the sharing (the issue above), or
number `Iterate` up to a shift of its outer references.
