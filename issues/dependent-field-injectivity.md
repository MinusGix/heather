---
title: Injectivity at a field whose type depends on an earlier one
status: open
labels: [frontend,elaboration,inductives]
area: language
created: 2026-07-26
updated: 2026-07-26
---

`inj(k, p)` is derived at tier 0 by a case tree at a **constant** motive —
"that field's type" — using the left-hand side's own field value as the
default at every other constructor (`docs/inductives/inductive-tier0-lowering.md` §6.2).
Constant is exactly what a *dependent* field type is not, so:

```heather
inductive B { Mk(n: Nat, p: n = n) }
// inj(0, …) works; inj(1, …) is diagnosed, not derived
```

Field 0 of such a constructor is still injective; only the dependent field is
out of reach. The generator checks the side condition by reading the field
type off *both* sides' encodings and comparing with kernel conversion, and
reports the limitation rather than emitting an ill-typed term.

## The second instance, which is why this is now its own issue

A **container field** hits the identical wall
(`docs/language/container-fields.md` §6, §9.2). Its type is `[D; len]`, which depends
on the length field before it, so `inj` at it would need both sides' lengths
definitionally equal:

```heather
inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }
// inj(2, …) diagnosed: `kids`'s type depends on `len`
```

This is not a container-specific gap and should not get a container-specific
fix. Two instances of one restriction is the point at which it deserves
tracking on its own rather than as a paragraph in each tier's document.

Note the container case is the more *likely* one to be hit in practice: a
dependent payload field is unusual, whereas every container field is dependent
by construction.

## What lifting it takes

`docs/inductives/inductive-tier0-lowering.md` §6.2 names two routes, neither yet needed:

- **A code-valued family.** The motive becomes a `Ty l`-valued function of the
  scrutinee, decoded with `El`. Recovers the general case, at the price of the
  level restriction non-cumulativity forces (the reason tier 0's *first* draft
  of injectivity was rewritten to use the constant-motive trick at all).
- **Transport along the earlier field's equation.** `inj` at field `j < k`
  already gives `a_j = b_j`; transport the `k`-th field along it and the two
  types agree. This is the more promising one for the container case
  specifically, because the equation needed is exactly `len_a = len_b`, which
  is `inj` at the length field — an ordinary non-dependent `Nat` field.
  The result is then `kids_a = transport(…, kids_b)` rather than
  `kids_a = kids_b`, i.e. a *heterogeneous* statement, and deciding whether
  that is the API we want is the actual design question.

The second route also decides a question this repo has not faced yet: what
`inj` should *state* when the field types differ. Until that is answered,
diagnosing is the right behaviour.

## Related

- [[inductive-compiler]] — lists dependent-field injectivity among tier 0's
  deferred items; this is that item, promoted.
- [[nested-inductives-container-fields]] — the container instance.
- [[setoid-auto-lifting]] — transport-shaped statements are adjacent to the
  quotient/setoid story.

## Log

- 2026-07-26: Filed while landing container fields phase 1, which produced the
  second instance of the same restriction. Documented in both tiers' schemes
  before this; the issue exists so that the *shared* fix has somewhere to
  live, and so the claim "these should be lifted together" is tracked rather
  than asserted in a doc comment.
- 2026-11-05: gardener: cites a file it shares with [[parametric-type-families]] (`docs/inductives/inductive-tier0-lowering.md`).
