---
title: Left-nested binds over a tier-2 tree cost exponentially in their depth
status: open
labels: [metaprogramming,performance,tier2]
area: tactics
milestone: [tac-host-interface]
created: 2026-10-21
updated: 2026-10-21
---

A tactic whose binds nest to the left, the shape a loop written as "do the
first `j` steps, then one more" takes, runs out of fuel after a few dozen
requests. With

```
fn tick() → Tac<Expr> { defeq(NatLit(0), NatLit(0)).bind(λ g => assumption()) }
fn lspin(k: Nat) → Tac<Expr> {
    match k { Zero => assumption(), Succ(j) => lspin(j).bind(λ e => tick()) }
}
```

`by lspin(12)` succeeds and `by lspin(14)` fails after about forty requests,
and the time to get there roughly doubles with each level of nesting. A
64× fuel budget does not rescue it; it runs until the address-space rail
instead. It was the same before the continuation chain fix
([[tactic-run-continuation-chain]]), and slower, so that fix neither caused it
nor cures it. The right-nested shape (`step.bind(λ _ => loop(j))`) is linear
and runs thousands of requests.

## Likely mechanism, not yet confirmed

A tier-2 constructor with a function child stores the child twice:
`⟨sup(ℓ; λy. fst(k y)), λy. snd(k y)⟩`
(docs/inductive-tier2-w-lowering.md §6). `Tac::bind`'s `Ask` arm builds
exactly that over `k' = λx. k(x).bind(f)`, so the tree component and the
proof component each evaluate `k(x).bind(f)` on their own: the two `k y`
applications are different closures in different environments, and the force
cache, keyed by closure, cannot share them. One bind therefore evaluates the
tree below it twice, and `d` binds nested to the left evaluate the innermost
`2^d` times. The host's pinning of the outer tree (the chain fix) only cuts
the outermost layer; the inner layers are rebuilt by every resume.

The same shape is ordinary Heather code, not only tactics:
`lib/std/itree.hthr`'s `bind` is this `match`, so evaluating a left-nested
interaction tree should show it too (not measured).

## Possible fixes

- **Share the child in the value domain**: memoize the application of a
  closure to an argument closure (both pointers are the same for the `fst` and
  `snd` uses, since both lambdas are applied to the one `y` the match's alias
  `k := λy. ⟨f' y, c y⟩` binds). A kernel evaluator change, sound because
  evaluation is pure, with a cost on every application that would need
  `scripts/perf ab`.
- **A lowering that stores the child once**, if one exists that keeps §2.4's
  leaf equation; the split is what Σ-over-W makes necessary today.
- **Library side**: write tactic loops right-nested, and give R3's
  combinators (`first_of`, `repeat`) that shape. A stopgap, and a convention a
  tactic author can break without noticing.

## What it assumes from elsewhere

- [[tier2-fragment-extensions]] owns the tier-2 encoding.
- [[host-elaboration-interface]] owns the host loop.
