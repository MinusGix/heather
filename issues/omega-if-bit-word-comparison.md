---
title: omega reads an `if h:` branch's word comparison only while the branch names `h`
status: open
labels: [tactics]
area: tactics
created: 2026-11-16
updated: 2026-11-16
---

An `if larger: x < y { … } else { … }` over words binds `larger` (as `x < y`
or `¬(x < y)`) only in a branch that names it; a branch that does not keeps
the test as the bit's equation, `__if_bitN: unsigned_lt_bit(x, y) = True`,
which `omega` and `bv_omega` are meant to read in its place
(`crates/syntax/src/parser.rs`, the `eqbind` comment in the `if` lowering).
`bv_omega` does. `omega` turns the equation into a guard,
`bit(unsigned_lt_bit(x, y)) = 1`, and keeps that bit as an atom unrelated
to `toNat(x)` and `toNat(y)`, so it gets stuck on a goal that the named
`larger` proves.

Seen in the sort example (`examples/sort/sort.hthr`, `insert_at_inserts`):
once the branch steps went through `simp_only(List::sift, …)` instead of
citing `List::sift::True::True(…, larger)`, neither branch named `larger`,
and `let ab: BitVec::unsigned_le(a, b) = omega` (and `ba` in the other
branch) failed; they are `bv_omega` now.

Done when `omega` reads an unsigned comparison bit's equation as the
comparison of the `toNat`s (as it reads the proposition), so the two
facts in the sort example go back to `omega`, or when the lowering always
gives a written name its proposition and the hidden equation is only for
unnamed tests.
