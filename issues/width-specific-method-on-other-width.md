---
title: A BitVec(8) method is offered on BitVec(16) and refused by the kernel
status: closed
labels: [frontend,elaboration,diagnostics]
created: 2026-10-07
updated: 2026-10-08
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

## Log

- 2026-10-08: Fixed on the diagnostic side, which is what was wanted.
  Selection is unchanged: a namespace holds one `BitVec::is_nl`, so there is
  no other member to choose. Two parts. The type display recovers an
  instance's value arguments through the checked instance matcher
  (`display_vargs`, beside `instance_args`), so a mismatch that differs only
  in them is stated: "this has type `BitVec(16)`, but `BitVec(8)` is expected
  here". And a mismatch at a receiver its type selected a member for names
  the member: "`BitVec::is_nl` takes a receiver of type `BitVec(8)`, but this
  receiver has type `BitVec(16)`", recorded by span on the success path like
  `unmarked_receivers` and probed only on rejection. The source-spelling
  flavour is untouched, so generated annotations do not move. Residue, not
  filed for want of a customer: a declaration with both type and value
  parameters still prints its type arguments as `<…>` beside the recovered
  values, because `display_targs` declines for it. Tests:
  `crates/elab/tests/type_members.rs` §7.
- 2026-10-08: The display change exposed a stale note. Instance search builds
  each candidate in checking position, so a rejected candidate (`Bool::Monoid`
  at `and` while `or` was asked) left a mismatch note behind. It used to
  display alike and lose to the `refl` note; spelled, it won and blamed the
  search. `resolve_goal_from` now drops a rejected candidate's notes along
  with its dependency edges. Caught by `lib_algebra` and
  `operation_indexed_classes`.
