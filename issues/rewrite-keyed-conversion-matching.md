---
title: Find a rewrite's occurrences by head symbol, then conversion
status: closed
labels: [frontend,elaboration,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

`rewrite(h, e)` finds the equation's left side syntactically (`==` on
elaborated terms, implicit arguments included) in the goal as written and
one exposed layer (`docs/equation-rewrite-design.md` §2). It misses:

- an occurrence whose implicit arguments are spelled differently
  (`lib/std/bitvec/bitvec.hthr`'s `ofNat(toNat(x)) = ofNat(0)` site, which needed
  `sym` instead);
- an occurrence one δ/ι step away from the written goal — part of the 71 std
  `j` sites PR #93 left, whose motives state a reduct of the goal
  (`a.pow(Succ(k))` written as `a.pow(k) * a`).

Lean's answer is keyed matching: collect candidate subterms whose head
symbol is the pattern's, then compare arguments by conversion (at reducible
transparency). Here: the candidates are the goal's (and its exposed form's)
subterms with the same head global/constructor, capped like
`matching::STUCK_CANDIDATES`, each tested with one bounded conversion call;
every candidate that converts is abstracted in one pass
(`abstract_local_any`), as the match-motive synthesis's §4.4 rung does.
The motive's instance at `a` is then the goal only up to conversion, which
the kernel checks anyway.

Measure first: classify the 71 remaining sites into "would convert under
this rule", "needs deeper reduction", "dependent motive", so the round
claims a number.

## What it assumes from elsewhere

- **[[rewrite-lemma-instantiation]]** shares the candidate walk; the two can
  land together.

## Log

- 2026-10-21: done (`docs/equation-rewrite-design.md` §6.2). Occurrences are
  the left side plus every subterm under no binder with its global head and
  arity that converts to it (type checked too), capped at 256 candidates,
  abstracted in one pass; `at :=` numbers all spellings together. Measured
  over the `j` sites round 1 left: 13 more convert; the rest need reduction
  past one head step or mention the proof. The `bitvec.hthr` `ofNat(toNat(x))`
  site is `rewrite(none, refl)` again.
