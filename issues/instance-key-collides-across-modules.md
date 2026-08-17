---
title: "Instance keys are the carrier head's surface name, so two modules' relations collide"
status: open
labels: [traits,stdlib,modules]
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]). It is the **one row of that
round's kit that could not be written**, so per [[std-api-waves]]'s doctrine it
was stalled rather than worked around, and `lib/std/int.hthr` carries a comment
where the instance would be.

`std/nat` registers the order's decision generically in both values
(`docs/value-generic-instances-design.md`):

```heather
instance(n, m: Nat) Decide<Le(n, m)> { dec := le_dec(n)(m) }
```

`std/int` declaring the same thing at its own order is refused:

```
`Le` already has an instance of `Decide` (`Le::Decide`), declared as
`Decide<Le(n, m)>`: at layer 1 the canonical name is keyed on the carrier's
*head* and the index spelling, so two carriers with the same head collide
```

The two `Le`s are different declarations in different modules — `nat::Le` and
`int::Le` — and nothing about them is ambiguous *to a reader* or to name
resolution, which qualifies by module (`docs/modules-design.md` §4). The registry
key is the head's **surface name**, so it cannot tell them apart.

## Why the workarounds are worse than the stall

- **Rename to `Le_int`.** This is what `std/bool` already pays (`Le_bool`,
  `le_bool_refl`, `le_bool_dec`), and it works — but it is exactly the encoding
  that erases the datum, and it costs the carrier its operator: `<=` at `Int`
  resolves through `designation <= at Int := Le` and reads the carrier off the
  operand, which is the mechanism that lets a downstream file write `x <= y` at
  both carriers. `bool`'s dodge predates that mechanism; reproducing it in 2026-08
  would be moving backwards.
- **Skip `Decide` and name the decider.** This is what the file does, and it is
  the same position `nat::eq_dec` is in for the neighbouring reason
  ([[decidable-equation-carrier]]): the decision is *available*, it is just not
  *found*. `Cmp<Int>` registers fine, because it is keyed on `Int`.

## The fix

Key an instance's canonical name on the carrier head's **resolved declaration**
(module-qualified) rather than on its spelling. `Le::Decide` becomes
`nat::Le::Decide` and `int::Le::Decide`, and nothing else about resolution moves:
a goal arrives with a resolved head already, since the goal's type was elaborated.

This is layer 1's key, so it is adjacent to but *not* the same as
[[decidable-equation-carrier]]'s layer-2 (class, carrier-syntax) key — that one is
about a carrier with *no* head to key on, this one about two heads with one name.
Both would be answered by a key that is a declaration reference.

## What it assumes from elsewhere

- **[[decidable-equation-carrier]]** owns the equation-carrier key. Assumed here:
  only that it is a *different* missing key, so neither issue subsumes the other.
- **[[std-int-encoding]]** owns the stalled row. Assumed here: only that the row
  is `Decide` at `int::Le` and that it is stalled, not worked around.

## Log

- 2026-08-17: Filed by the `Int` round as the round's only refused row. Ranked #3 of six, and it is the one that cost a *kit item* rather than proof lines.
