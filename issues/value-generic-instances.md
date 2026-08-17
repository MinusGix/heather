---
title: An instance cannot be generic over a value: instance Decide<Le(n, m)>
status: closed
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

## Log

- 2026-08-17: Landed. `instance(n, m: Nat) Decide<Le(n, m)>` — a value-parameter list at the instance head, the same production a `record` head takes; the sketch's first candidate, chosen because `(` after `instance` begins nothing else. docs/value-generic-instances-design.md is the record. The issue's guess that this is smaller than it looks was right and then some: NOTHING in the resolver, the registry key or the unifier changed. Measured before writing anything — a hand-rolled `fn ld({n: Nat}, {m: Nat}) -> Decide<Le(n, m)>` referenced bare in checking position already resolved at open arguments, which is exactly what build_candidate writes, because the unifier decomposes `Le(?n, ?m)` against `Le(x, h)` (both stuck at the same fn). What was missing was a binder list. Value binders are marked implicit in the parser and lead the telescope ahead of the solver parameters. Three things did need saying: (1) a binder must OCCUR in the head, since head-against-goal unification is the only route that determines it and one the head omits is a metavariable nothing can ever solve — refused at the declaration instead of surfacing as an uninstantiated implicit at an unrelated use site; (2) Paterson's variable condition now counts value binders, which duplicate exactly as type parameters do; (3) grouped runs `(n, m: Nat)` now parse in all four heads, because a reader who has written `fn f(n, m: Nat)` cannot know the head is a different production. std/nat gains one line and list_algos's three call sites go from `le_dec(x, h)` to `decide<Le(x, h)>()` with the proofs unchanged — the acceptance, and a substitution rather than a rewrite. Backchaining is the part that is not a rename: `decide<Not(Le(x, h))>()` and the And/Or composites now resolve at open arguments, where before every such goal died at the Le leaf. The occurrence rule is NOT imposed on type parameters (`instance<A> C<Rat>` has been legal since layer 1) — noted in §4 as the natural companion tightening.
- 2026-08-17: Filed while writing the mixed type-and-value test: [[recursive-self-call-type-arguments]] — a recursive self-call cannot name its own type arguments (`fn Rep<A>(n: Nat) -> Type { … Rep<A>(k) … }`), and the diagnostic says the declaration "takes no type arguments" while pointing at a declaration that visibly does. Unrelated to this round's feature and not blocking it; the test was rewritten around a non-recursive former, which is why nothing in the suite covers it.
