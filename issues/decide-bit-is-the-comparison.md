---
title: A comparison's Decide bit is its leb, so a guard is a decision
status: open
labels: [stdlib,decidability,proofs,ergonomics]
area: tactics
created: 2026-10-30
updated: 2026-10-30
---

`instance(n, m: Nat) Decide<Nat::Le(n, m)>` has `bit := or_bit(Nat::le_dec(n, m))`
(`lib/std/num/nat.hthr`), and `Int`'s, `Rat`'s and the equality instances the
same. A Bool guard a program writes uses `n.leb(m)`, so
`decide_bit<n <= m ∧ …>()` is never that guard, and a Bool-guarded record
field (`Finite`'s `ok: F.canonical(mag, bexp).IsTrue()`) has to build its
`Reflects` by hand: `Format::canonical_reflects` (2026-10-30), and the
`or_bit(…le_dec…)` bits in `float/literal`'s `Rat::dy_exact`.

Proposal, `docs/bool-guard-reflection-design.md` §3.1:

1. `Decide<Nat::Le(n, m)>` with `bit := n.leb(m)`,
   `reflects := Nat::leb_reflects(n, m)` (and the analogous `Int`, `=` bits);
2. `instance<P: Decide, Q: Decide> Decide<P → Q>` with bit `!P.bit || Q.bit`;
3. `decide_intro<P: Decide>(p: P): decide_bit<P>().IsTrue()` and
   `decide_elim<P: Decide>(h: decide_bit<P>().IsTrue()): P`, the `IsTrue`
   readings of `reflects_intro` / `reflects_elim`;
4. `Format::canonical := decide_bit<F.Canonical(mag, bexp)>()`, deleting
   `canonical_reflects` and making intro/elim `decide_intro` / `decide_elim`.

To measure before deciding: closed `refl`s over `canonical` and the literal
`exact` bits re-evaluate through the instance dictionaries
(`float_tests`, `arith_tests`, `literal_tests`); the kernel's stuck-`leb`
handling (`crates/kernel/src/conv.rs`) now applies to every decided `<=`;
and the native frontend lowers `if n <= m` through `decide_bit`
([[native-frontend-decided-matches]]), so the bit it sees changes from
`or_bit(le_dec)` to `leb`.

Related: [[omega-reads-bool-guards]], [[derive-decide-instances]],
[[class-ops-prop-vs-bool]].
