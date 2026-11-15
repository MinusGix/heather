---
title: linarith at Rat without ordered_field in scope reads the goal at Int and fails there
status: closed
labels: [tactics,linarith,diagnostics]
area: tactics
created: 2026-11-10
updated: 2026-11-10
---

In a module that imports `rat` and `linarith` but not `ordered_field` (nor
`algebra`, `algebra_rel`, `semiring`), a linear goal over `Rat` is not
proved, and the refusal reports the goal read at `Int`:

```
theorem lt_of_twice({p, q, m: Rat}, h: p < q, e: m + m ≈ p + q): p < m { linarith(h, e) }
// `linarith` could not prove `p < m` at `Int`/`Nat`: `omega` found no proof
// with `ring`'s monomials as atoms; the sides read as [`p.num * int(m.den)` …
```

With `import ordered_field;` (and the three it needs) added, the same line is
accepted. `Rat`'s order and `≈` are definitions over `Int`, so with no
ordered-field instance in scope the tactic unfolds them and tries the
numerator-denominator reading, which is nonlinear.

## Scope

- When the goal's relation is a designation at a carrier that has an
  `OrderedField` instance somewhere in the library but not in scope, say so:
  name the carrier and the import, before or instead of the `Int` reading.
- Or have `rat` re-export what `linarith` needs at `Rat`, so importing the
  carrier and the tactic is enough.

Found writing lib/std/locale/real_locale.hthr (docs/library/localic-reals-design.md §8).

## Log

- 2026-11-10: Done (thread 'Make linarith work on Rat without imports'), the issue's second option in Minus's form: the prelude imports ordered_field (qualified-only), so the tactics' key lookups of ordered_field::OrderedField and semiring::CommRingOfInt succeed; and a callee's written solver goal (ring::RingExpr::eval_rel's CommRingOfInt<A>(≈, +, *)) whose class the caller cannot name is read in the callee's module (dispatch/dictionary.rs solver_class_ref), which made numerals in linarith's certificates and in ring at Rat constants again. Probes: lib/_tests/std/tactic/linarith_carrier_import_tests.hthr. The first option (a diagnostic naming the missing import) is moot for Rat/CReal.
