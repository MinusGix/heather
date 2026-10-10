---
title: Decide how positivity is spelled: keep Pos, hypotheses, or binder sugar over infer
status: open
labels: [stdlib,elaboration,traits,design,ergonomics]
created: 2026-10-10
updated: 2026-10-10
---

Decide whether `lib/std/pos.hthr`'s shifted `Pos { pred }` stays, and how
positivity is spelled and discharged. The options, the probes of what
`:= infer` does today, and a costed recommendation are in
`docs/positivity-evidence-design.md`.

The recommendation: grow `:= infer` at proposition goals (computation to
`True`, then registered evidence rules keyed by the positive term's head),
make `Pos<A>` binder sugar for `x: A, x_pos: 0 < x := infer` rather than a
type, migrate `Rat`, and delete the shifted representation. A real
refinement type for function domains and containers waits for
[[regular-cauchy-reals]].

## Decisions wanted (design note §7)

1. Route: sugar over the search (recommended), the search alone, or a
   refinement record now.
2. Spelling: `n: Pos<Nat>`, `n: Nat where 0 < n`, or both.
3. How an evidence rule is registered.
4. Whether `infer` looks through `∧` projections of locals.

No refactor of `Pos` users until the route is picked.

## What it assumes from elsewhere

- **[[implicit-logical-assumptions]]** owns `infer`'s precedence across
  `assuming`/`using` scopes. Assumed here: new sources slot after locals and
  derivations and do not reorder them.
- **[[field-defaults-under-locals]]** owns stored-goal defaults. Assumed
  here: parameter defaults, if ever wanted for positivity, share it.
- **[[subtype-transfer-and-evidence]]** owns evidence policies for real
  subtypes, which the deferred refinement type would use.
- **[[positive-naturals-and-rationals]]** landed the current `Pos`.

## Log

- 2026-10-10: Filed with the design note, from Minus's question whether
  `Pos` should exist at all.
