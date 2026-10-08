---
title: A BitVec(8) method is offered on BitVec(16) and refused by the kernel
status: open
labels: [frontend,elaboration,diagnostics]
created: 2026-10-07
updated: 2026-10-07
---

A method declared for one width of `BitVec` is offered on receivers of any
width, and the mismatch is found by the kernel. Probed 2026-10-07 at
`b5b2b9d`:

```text
fn BitVec::is_nl(self b: BitVec(8)) → Bool { decide_bit<b = '\n'>() }
fn g(x: BitVec(16)) → Bool { x.is_nl() }

error: the kernel rejected `g`: NotConvertible. this has type `BitVec` where
a type that displays the same is expected; they differ in something the
display does not show
```

Receiver dispatch keys on the head `BitVec` and does not check the width
argument, and the type display drops it, so the message reads as a
contradiction. Width-specific methods are the natural home for byte classes
([[byte-type-and-predicates]]), so this will be hit as soon as they exist.

Wanted: the elaborator checks the receiver against the method's `self` type
and says "`is_nl` takes `BitVec(8)`, found `BitVec(16)`"; and a type display
that differs only in an argument shows that argument.

## What it assumes from elsewhere

- **[[byte-type-and-predicates]]** owns whether byte classes become methods
  on `BitVec(8)`. Assumed here: only that width-specific methods are a
  likely shape.
