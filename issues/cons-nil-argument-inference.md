---
title: Infer an earlier argument's implicit from a later argument (Cons(Nil, xs))
status: open
labels: [elaboration,inference]
created: 2026-10-02
updated: 2026-10-02
---

`Cons(Nil, pieces)` with `pieces: List<List<A>>` is refused: "cannot infer
the type argument `A` of `List` here — no argument of `Nil` determines it".
The second argument fixes `Cons`'s type parameter, and with it `Nil`'s, but
the arguments are elaborated left to right and `Nil` is inferred before
`pieces` is seen. Found writing the generic run-count lemma (2026-10-02,
probes for [[native-programs-read-like-programs]]); the workaround is
`Nil<A>`.

Wanted: postpone an argument whose inference is stuck on an implicit, and
elaborate it in checking mode once the later arguments have solved the
implicit. Check against existing postponement machinery before designing
anything new.
