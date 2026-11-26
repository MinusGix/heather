---
title: Diagnose a constructor name read as a type in a type position
status: open
labels: [elaborator,diagnostics]
area: language
milestone: [none]
created: 2026-11-26
updated: 2026-11-26
---

In a type position (a motive, an equation's side) `Fin(f)` resolves to the
index type `Fin(n)` rather than the constructor `Float::Fin`, since type and
constructor names share one namespace ([[false-collides-with-bools-constructor]]).
The resolution is by design; the diagnostic is not helpful:

    error: this has type `Finite(F)`, but `Nat` is expected here

(`round_odd_fin_cases` in `lib/std/num/float/project.hthr`, before it said
`Float::Fin(f)`). When an argument's type is a constructor's field type for
a same-named constructor in scope, the error should name that constructor
and suggest qualifying it (`Float::Fin(f)`).
