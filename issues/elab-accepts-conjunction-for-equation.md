---
title: A conjunction passed for an equation argument is refused only by the kernel
status: open
labels: [frontend,elaboration,diagnostics]
created: 2026-10-04
updated: 2026-10-04
---

Found while proving the stat pass (`lib/elf64_stat_width.hthr`, 2026-10-04).
A proof of a conjunction passed where an equation is expected gets past the
elaborator, and only the kernel refuses it, at the whole declaration, with no
span and no types:

```heather
theorem bad4(a, b: Nat, p: (a = b) ∧ (b = b)): b = a { sym(p) }
// error: the kernel rejected `bad4`: NotConvertible
//   --> …:1:1
theorem bad2(a, b, c: Nat, p: (a = b) ∧ (b = b), q: b = c): a = c { trans(p, q) }
// the same; `trans<Nat>(p, q)` and a `let r: (a = c) = trans(p, q)` too
```

`sym` and `trans` are ordinary prelude theorems (`crates/elab/src/prelude.hthr`)
whose equation's sides are implicit, so the check of `p` against `?a = ?b`
should fail to unify `Eq` with `∧`. Something in that path accepts it instead
(the sibling [[check-fallback-discards-expected-type]] was the inference
fallback; that one is closed, so this is a different route).

How it cost time: one projection too few (`regs.right…right` stopping at the
last conjunction instead of its right side) inside a 40-line proof. The
kernel's refusal named the theorem only; finding the line took a bisection
with `axiom hole<A>(): A;` stand-ins, and it hid behind an unused `let`
(dropped before the kernel sees it), so a stand-in for the *use* passed while
the bad `let` was still in the source.

Not a soundness problem (the kernel refuses), a diagnostics one: the
elaborator should point at `p` and say it is a conjunction, not an equation.

The counting that produced the bad projection is [[conjunction-facts-read-by-counting]].
