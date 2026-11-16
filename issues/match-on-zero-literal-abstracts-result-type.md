---
title: match on the literal 0 abstracts the 0s inside the result type's lowering
status: open
labels: [frontend,elaboration,matching]
area: language
created: 2026-11-16
updated: 2026-11-16
---

A `match` on the literal `0` whose arms return a value of a list type is
handed to the kernel with a motive the arms do not have, and the kernel
refuses it:

```
fn f3(tl: List<Nat>) → List<Nat> { match 0 { Zero => tl, Succ(v0) => tl } }
```

```
error: the kernel rejected `f3`: NotConvertible. no checking site recorded
this refusal: the kernel refused `λ (z: List<Nat>) => z` where
`List<Nat> -> List<Nat>` is expected
```

`(Zero: Nat)` as the scrutinee does the same. These check: `match 1 { … }`,
a variable scrutinee, and the same function at `Option<Nat>`, `Nat`, `Bool`,
a pair or `Nat → Nat`. A pair holding a list fails
(`Zero => Pair((Nil: List<Nat>), 0)`).

The kernel is right to refuse. Not confirmed by reading the elaborator, but
the shape fits motive synthesis abstracting the scrutinee out of the result
type: `List<Nat>`'s lowering holds `Zero` somewhere, so the motive becomes
`x. List<Nat>[x/0]`, which is `List<Nat>` at `0` and something else at
`Succ(v0)`, where the arm's `tl` still has type `List<Nat>`. `1` does not
occur in the lowering, so `match 1` is untouched.

What should happen: the abstraction applies only to occurrences the user
wrote (or the constant motive is tried when the abstracted one is refused),
and a refusal here is the elaborator's, at the `match`, not the gate's.

Found by the kernel bug hunt's program fuzzer (2026-11-16); it is not a
soundness problem.
