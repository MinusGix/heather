---
title: An induction hypothesis typed by a motive application cannot fill implicit arguments
status: open
labels: [frontend,elaborator,inference,proofs]
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]), ranked #2 there. It is what makes
a hand-written induction principle expensive to *use*, as opposed to expensive to
state.

`Int` is a non-recursive inductive, so nothing recurses on an integer and every
law that needs induction goes through `lib/std/int.hthr`'s `int_ind`, whose motive
is a value parameter `P: Int -> Type`. In an arm written as

```heather
λ (k: Nat) (ih: add(a, OfNat(k)) = add(OfNat(k), a)) => trans(cong_int(isucc, ih), …)
```

the `cong_int` call is **refused**: "could not infer the implicit argument `b` of
`cong_int`". `cong_int(f: Int -> Int, {a, b: Int}, p: a = b)` fills its two
implicits by unifying against a type, and the type it has to read is `ih`'s, which
is the motive *applied* — `(λ (z: Int) => add(a, z) = add(z, a))(OfNat(k))`. That
is a β-redex, not an `Id`, so nothing can be read off it. The λ's own annotation
does not help: the binder is checked *against* the parameter type, and the entry
that lands in the context is the expected one.

The same happens with `sym(ih)`, so it is about implicit-filling from an argument
type in general, not about `cong_int`.

## What works, at what cost

All three of these check, and the round used the first:

1. `@cong_int(isucc, add(a, OfNat(k)), add(OfNat(k), a), ih)` — the implicits
   spelled positionally. Costs one restatement of `ih`'s type per rewrite; **10
   sites** in `lib/std/int.hthr` (`add_comm`, `add_assoc`, `neg_add`,
   `mul_add_distr` and the three cancellation/`mul_isucc` chains).
2. A named helper theorem per arm, taking `ih` as an ordinary parameter — the
   conversion check at the call site accepts the redex, and inside the helper the
   hypothesis has a real `Id` type.
3. Reordering the `trans` chain so the deferred argument is on the other side —
   works only when some *other* argument determines the middle point, which is why
   `std/nat`'s existing `trans(cong_nat(…), lemma)` sites were never affected.

## The fix

whnf the argument's type before reading implicits off it (or, equivalently, β-normalize
a motive application when it is used as a hypothesis type). This is the same
sentence as the fix that landed 2026-08-17 for
[[match-arg-of-polymorphic-callee-needs-motive]]'s sibling — "an argument's type
is evidence even after the parameters run out" — extended to *reducible* argument
types.

A narrower alternative that would also have paid for this round: have a λ binder's
written annotation replace the expected type in the context when the two are
convertible. That is a smaller change and it makes annotations mean what a reader
thinks they mean, but it fixes only the arms a writer thought to annotate.

## What it assumes from elsewhere

- **[[std-int-encoding]]** owns the round and the `int_ind` spelling. Assumed
  here: only that `Int`'s induction principle has to be a declaration with a
  value-parameter motive, because `Int` has no structural recursion of its own.
- **[[ih-generalization]]** owns the curried-recursion tax. Assumed here: nothing;
  this is the *hypothesis's type*, not the recursion's shape.

## Log

- 2026-08-17: Filed by the `Int` round. 10 sites, each paying one restatement of the hypothesis's own statement inside `@cong_int`. Ranked #2 of that round's six.
