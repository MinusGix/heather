---
title: ring refuses a goal whose atom is a field read like x.seq(n)
status: closed
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

At a `≈` carrier, `ring` fails with "`ring` could not spell one of the Rat
atoms as source" when an atom is a field read off a value, such as a Cauchy
real's term:

```heather
theorem p(x: CReal, n: Nat): x.seq(n) + 1 ≈ 1 + x.seq(n) { ring }   // could not spell
```

The certificate names its atoms by their source spelling (the atom list is
elaborated from text), so an atom that does not spell refuses the whole
reading. `CReal`'s regularity proofs meet this constantly: the
[[field-simp]] round had to apply `ring` under
`Rat::add_respects(x.seq(n).same_refl(), ring)` instead of on the whole step
(lib/std/num/creal.hthr, `lt_of_term` and `lt_respects`).

omega had the same failure for record projections of locals and fixed it by
spelling the inline walk ([[omega-record-projection-atoms]]). `CReal`'s `seq`
is a function-valued field applied to `n`, which may be a different path in
the speller.

Shape of a fix: spell the read the way omega's fix does, or name the atoms
through aliases (as `ring` already does for hypotheses and reciprocal facts)
instead of through text.

## Log

- 2026-10-27: Fixed by [[linarith-ordered-fields]]'s round (docs/linarith-design.md §4): an atom with no spelling is named in the atom list by an alias bound to the term (`__ring_a{i}`), so `x.seq(n) + 1 ≈ 1 + x.seq(n)` is `ring`'s (probe in lib/_tests/std/tactic/ring_field_tests.hthr). The `add_respects(x.seq(n).same_refl(), ring)` workarounds in creal.hthr still check and can be simplified when next touched.
