---
title: "Decide at a dependent function type: `decide` on a bare `(a: A) → p(a) = True` over a finite type"
status: open
labels: [classes,decide,elaborator]
area: language
milestone: [math-finite]
created: 2026-11-11
updated: 2026-11-11
---

Found by [[finite-types-and-enumeration]] (2026-11-11).

    instance<A: Fintype>(p: A → Bool) Decide<(a: A) → p(a) = True> { … }

is refused: "the carrier `A -> p(a) = True` has no head type name, so this
instance has no canonical name". An arrow with no binder has the class's
`#Fn` key (`crates/elab/src/traits.rs`, the `Decide<P → Q>` case); a
dependent one has none.

The library works around it with a type former, `Fintype::All<A>(p)`,
which unfolds to the function type. So `decide` proves a goal written
`Fintype::All<Bool>(λ b => …)` and not the same goal written
`(b: Bool) → …`, and a theorem stated the natural way spends
`Fintype::all_sound(p, refl)` by hand.

## Scope

- A structural key for a binder-headed carrier (`#Pi@Class`), beside `#Fn`.
- Resolution against it: the goal `(a: A) → Q` matches the head by
  abstracting `a` from `Q`, a pattern-unification step
  (`docs/unifier-completeness-design.md`), with `A`'s `Fintype` as the
  premise.
- The second half is the general predicate: an instance whose premise is
  a family of instances, `(a: A) → Decide<P(a)>`, so that `P` need not be
  a Bool. Decide whether instance premises may be quantified, or whether
  the Bool form with `decide_bit<P(a)>()` stays the spelling.

## Done when

`theorem t(): (b: Bool) → (b || !b) = True { decide }` checks, and
`Fintype::All` is either retired or kept as a documented alias.
