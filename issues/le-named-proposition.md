---
title: Le as a named proposition: retire the leb(n)(m) = True spelling
status: open
labels: [stdlib,elaboration,ergonomics]
created: 2026-08-01
updated: 2026-08-01
---

Every ordering statement in lib/ir_v1.hthr is spelled `leb(n)(m) = True` — boolean reflection worn on the sleeve, curried because `leb` recurses on both arguments and nested match patterns don't exist yet ([[nested-match-patterns]]). `fuel_monotone`'s stated interface (docs/ir-simulate-design.md §6 says `n <= m`) reads as an implementation detail instead.

Three separable pieces; this issue owns the first:

1. **The named proposition** — writable today, since [[type-definitions]] landed:

   ```heather
   fn Le(n: Nat, m: Nat) -> Type { leb(n)(m) = True }
   ```

   Restate the kit over it (`le_refl`, `le_succ_r`, `le_add_l`, `le_add_r`, `le_add` — lib/ir_v1.hthr ~L798–835) and `fuel_monotone`'s `hle` binder. Definitional unfolding means existing proofs keep working under the new statements; the round is mostly mechanical. Whether `Le` stays reflection-backed or becomes an inductive is NOT this issue — reflection is fine while conversion discharges the concrete cases for free.

2. **The un-currying** of `leb` itself: owned by [[nested-match-patterns]].

3. **`<=` at the surface**: [[comparison-operators]], which wants this issue's `Le` as its desugar target.

Home question: the kit belongs in the prelude eventually ([[prelude-option-and-friends]] layer 1's shopping list already grew once for fuel_monotone); do the restatement in-file now, move when prelude residency lands.
