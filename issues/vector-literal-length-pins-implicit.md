---
title: A vector literal's length does not pin a width implicit; the argument is deferred instead
status: closed
labels: [frontend,elaboration,inference,bitvec]
created: 2026-09-24
updated: 2026-09-24
---

A vector literal's length does not pin a width implicit: the argument is
deferred and never elaborated, though its length is known from the syntax.

```heather
fn c03(y: Bool) → BitVec(3) { BitVec::from_bits([y, False, True]) }   // ok (checking)
fn b01(y: Bool) → Type {
    BitVec::from_bits([y, False, True]) = BitVec::from_bits([False, False, True])
}   // error: this argument of `BitVec::from_bits` was deferred — the type of
    // its parameter `bits` still mentions an implicit that could not be inferred
fn c04(p: BitVec(7)) → BitVec(8) { BitVec::concat(p, BitVec::from_bits([False])) }
    // same error: `?m + ?k` against 8 cannot be inverted, and the literal that
    // would give `?k = 1` is the deferred argument
```

`BitVec::from_bits({n: Nat}, bits: [Bool; n])`: checking `[a, b, c]` against
`[Bool; ?n]` could solve `?n := 3` outright — the literal's length is not
inferred, it is counted. The per-call deferral
(`docs/unifier-completeness-design.md` §3–§5) treats the literal like any
checking-only argument instead.

Found by the 2026-09-24 probe of the remaining `@` sites: ~20 of the 80
(`@BitVec::from_bits` ×15 in `lib/std/utf8.hthr`'s bit proofs, `@BitVec::concat`
×5). Slice #1b with [[unify-succ-under-addition]], under
[[elab-unifier-completeness]]. Sibling shape: [[nullary-ctor-argument-not-deferred]].

## Log

- 2026-09-24: 2026-09-24: Landed as slice #1b (docs/unifier-completeness-design.md §10), with tests in crates/elab/tests/implicit_args.rs. Full suite 2942 passed.
