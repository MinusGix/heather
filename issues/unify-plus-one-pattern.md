---
title: The unifier does not step a pattern ?n + 1 to meet Succ(m)
status: closed
labels: [frontend,elaboration,inference,unification,bitvec]
area: language
created: 2026-11-17
updated: 2026-11-17
---

The converse of [[unify-succ-under-addition]]. A signature that spells a
width the everyday way, `BitVec(n + 1)`, leaves the pattern `?n + 1` for the
unifier, and the subject is very often a successor: the `Succ(k)` a match
on the width leaves, a numeral, another `m + Succ(k)`, or a call that
computes to one. None of those learned `?n`:

```heather
fn plus_one_head({n: Nat}, x: BitVec(n + 1)) → Bool { x.head_bit() }
fn at_succ(k: Nat, x: BitVec(Succ(k))) → Bool { plus_one_head(x) }
    // could not infer the implicit argument `n`
fn at_sum(m, k: Nat, x: BitVec(m + Succ(k))) → Bool { plus_one_head(x) }
    // this has type `BitVec(m + Succ(k))`, but `BitVec(m + 1)` is expected
```

The second is worse than a refusal: the application congruence paired
`?n := m` and `1` with `Succ(k)`, so the call reported a mismatch.

It blocked respelling the library's `Succ(n)` as `n + 1` (Minus,
2026-11-17): `BitVec::cons_bit`'s result `BitVec(n + 1)` met a `match` arm's
`BitVec(Succ(_))` in 213 of `bitvec.hthr`'s declarations.

`Nat::add` recurses on its second argument, so `a + k` at a positive
numeral `k` is `Succ(a + (k - 1))` after one δι step. The unifier takes
that step on the pattern side (`U::succ_pred`, `unification.rs`): `a + k`
against `Succ(b)` or a positive numeral meets their predecessors; against
another `_ + k'` the two predecessors meet; against a call, the subject
takes its weak head first, as a canonical pattern's subject already did.
Learn-only, like every case there; the kernel judges the call.

Probes: `lib/_tests/lang/plus_one_pattern_tests.hthr` (successor, numeral,
sum, computed subject, a checking position, and `BitVec(0)` as the negative
control).
