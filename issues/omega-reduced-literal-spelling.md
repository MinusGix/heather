---
title: omega reads a closed literal left by a reduced motive
status: open
labels: [omega,proof-ergonomics]
area: tactics
milestone: [none]
created: 2026-11-26
updated: 2026-11-26
---

`omega` reports "could not spell a natural expression: `1` has no source
spelling here; bind it with a `let` it can be named by" when the goal holds a
literal left by reducing a match's motive. In `Nat::count_away_eq`
(`lib/std/num/float/project.hthr`) the arm's goal was
`count_away(k, M, m) + (match Inl(le) { Inl(_) => 1, Inr(_) => 0 }) = …`
after reduction, and both arms needed a typed `let` restating the goal
before `omega` could close it.

The message names the workaround, but the literal is a closed numeral: omega
should read a closed `Nat` literal whatever term produced it (whnf the atom
before giving up on spelling it).
