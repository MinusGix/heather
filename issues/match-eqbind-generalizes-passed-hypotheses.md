---
title: "`match h:` generalizes the hypotheses an arm passes with `h`, replacing the beside rule"
status: open
thread: Generalize h with its passed hypotheses
labels: [elaborator,matching,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-17
updated: 2026-11-17
---

Since [[case-split-refines-hypotheses-under-calls]], `match h:` on a computed
scrutinee refines the context like a plain `match`, except a hypothesis an
arm passes **beside `h` in one call** (`generalize::passed_beside`,
`docs/elaborator/goal-motive-synthesis-design.md` §4.7). The exception is
syntactic: it exists so that `lemma(…, slot, within, …)`, `trans(e, h)` and
`j(s, …, spare)` keep working, where the callee states both `h` and the
hypothesis about the test as written. It also bites the natural spelling:
`subst(compiled, linked)` leaves `compiled` unrefined, and the error shows
up at the `absurd(compiled)` of another arm
([[named-match-third-level-kernel-rejects]] point 2).

## Wanted

A principled rule in place of the syntactic one. The direction offered:
generalize `h` **together with** the hypotheses it is passed with, so each
arm sees `h : test = C(…)` and every hypothesis at its refined type, and a
callee stated about the test as written is met by transporting back along
`h` (dependent-match-compiler-design "slice 5", where a convoy's equation
becomes a real binder). The thread owning this is asked to aim past
adequacy: find the rule a reader would predict without knowing the
elaborator, and show it on the library's idioms.

## Done when

`passed_beside` is gone, the library's beside idioms check unchanged (or
simpler), a refusal to refine is reported where the hypothesis is used,
and the whole library re-elaborates.
