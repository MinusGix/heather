---
title: The unifier does not reduce m + Succ(k) to expose Succ against Succ(?n)
status: closed
labels: [frontend,elaboration,inference,unification,bitvec]
created: 2026-09-24
updated: 2026-09-24
---

The elaborator's unifier does not reduce a rigid Nat addition to expose a
`Succ`, so an implicit that the kernel could read off by one ι-step is refused.

```heather
fn e03(m, k: Nat, x: BitVec(Succ(m + k))) → Bool { x.head_bit() }    // ok
fn e05(m, k: Nat, x: BitVec(m + Succ(k))) → BitVec(Succ(m + k)) { x } // ok (kernel conversion)
fn e01(m, k: Nat, x: BitVec(m + Succ(k))) → Bool { x.head_bit() }
fn e06(k: Nat, x: BitVec(k + 1)) → Bool { x.head_bit() }
    // both: could not infer the implicit argument `n` of `BitVec::head_bit`
```

`BitVec::head_bit({n: Nat}, self x: BitVec(Succ(n)))` needs
`Succ(?n) ≟ m + Succ(k)`. `Nat::add` recurses on its second argument, so the
right side is `Succ(m + k)` after one δι step, and `Succ(?n) ≟ NatLit(k)` is
already handled (added during the 2026-09-22 de-@ pass). What is missing is
weak-head reduction of the rigid side before the structural case gives up.
`k + 1` is the everyday spelling of a width, so this recurs across the x86 line.

Found by the 2026-09-24 probe of the remaining `@` sites: `@BitVec::head_bit(m + k, x)`
(`take_low`, `concat_split`) and the `cons_bit_cong(m + k, …)` sites around them.
Slice #1b with [[vector-literal-length-pins-implicit]], under
[[elab-unifier-completeness]]. Unifier is on the hot path: the reduction should
fire only when a flex/rigid pair would otherwise fail.

## Log

- 2026-09-24: 2026-09-24: A second shape of the same gap, from the namespace round's sweep: a plain `BitVec::cons_bit_cong(n, refl, ih)` fails wherever the goal has to unfold before it shows `xs.cons_bit(a)` (`decrement_increment_step`'s `True` arm). The library now spells those sites with named implicits (`a := …, xs := …`). They are acceptance for this slice.
- 2026-09-24: 2026-09-24: Landed as slice #1b (docs/unifier-completeness-design.md §10), with tests in crates/elab/tests/implicit_args.rs. Full suite 2942 passed.
