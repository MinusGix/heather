---
title: An instance cannot be generic over a value: instance Decide<Le(n, m)>
status: open
labels: [frontend,elaboration,traits,design]
created: 2026-08-17
updated: 2026-08-17
---

An instance may be generic over **types** (`instance<A> Monoid<List<A>>`) or
carry fixed value **indices** (`instance CommMonoid<Nat>(add)`). Nothing binds
an ordinary *value* parameter, so

```heather
instance Decide<Le(n, m)>          // generic in n, m : Nat
```

has no spelling. `requires` accepts only class references — `requires n: Nat`
is a parse error, and `docs/surface-value-parameters.md` §1 records why a value
list in that position would be ambiguous against a parameter list.

## Why this is the blocker that matters

Found by [[decide-class]] (2026-08-17), and it is what actually stands between
`Decide` and the example that issue was filed for. `insert(x, Cons(h, t))`
decides `Le(x, h)` at **open** `x` and `h`; a closed instance cannot serve it,
and elaboration-time search already answers the closed case, so the open case
is the only one with content.

The carrier widening landed the same day (`docs/decide-class-design.md` §2)
means `instance Decide<Le(2, 5)>` now registers *successfully* — and is
useless. That the reachable case is exactly the worthless one is the sharpest
statement of this gap.

## What it is not

Not the canonical-name key. `Le(n, m)` keys at `Le` perfectly well, and
resolution never consults the head anyway (`docs/decide-class-design.md` §2.2).
Not [[decidable-equation-carrier]] either — that one is about the key and this
one is about binders; they are independent and neither subsumes the other.

## Sketch

The instance head already elaborates a carrier containing free names; what is
missing is a binder list for them. The two candidate spellings:

```heather
instance(n, m: Nat) Decide<Le(n, m)> { … }        // a parameter list
instance Decide<Le(n, m)> forall n, m: Nat { … }  // a trailing binder
```

The first collides with nothing at `instance` (unlike after `requires`), which
is the parse constraint that killed the obvious route. Whichever is chosen, the
instance value becomes a function of those binders and resolution has to
*infer* them from the goal — which is unification against the instance head,
and is the same machinery `instance<A> Monoid<List<A>>` already needs for its
type parameters. That similarity is the reason to expect this is smaller than
it looks.

## Acceptance

`instance Decide<Le(n, m)>` registers, and `insert` decides through the class
rather than by naming `le_dec`. The `list_algos` restatement is the ready-made
regression: it should be rewritable to reach the decider by resolution with no
other change.
