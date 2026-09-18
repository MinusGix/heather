---
title: Course-of-values recursion on lists and other inductives, not only Nat
status: open
labels: [frontend,elaboration,termination,stdlib,design]
created: 2026-09-18
updated: 2026-09-18
---

`utf8::decode` consumes one to four bytes per step, so its self-call lands
on a grandchild (or great-great-grandchild) of the scrutinee. Structural
recursion on lists refuses that — "argument `bytes` has to be one of the
recursive fields bound by the enclosing `match`. A deeper subterm is refused
too" — while `Nat` admits it since [[recursion-at-deeper-subterms]]
(`docs/course-of-values-recursion-design.md`, customer `nat::half`). The
`decreases` route is no help either: a measured body written with the
equation bindings its obligations need gets no unfolding equation
([[unfolding-computed-scrutinee]]), so nothing about it is provable at an
open tail.

The decoder therefore recurses on a **fuel** that `decode` sets to the byte
count (`lib/std/utf8.hthr`, `decode_at`), spending exactly as many steps as
bytes so the proofs' induction hypothesis is the bare recursive call. It
works, but it is an API shaped by a language limit, which the library is not
supposed to do ([[string-char-spec-types]] round 2, design §5.5).

Extend the course-of-values window to any inductive: a self-call on a
subterm reached through a chain of recursive-field projections of the
scrutinee, bounded by a constant depth, the way `Nat`'s window is. Customer:
rewrite `decode_at` as `decode` recursing on `rest2`/`rest3`/`rest4`
directly and delete the fuel.
