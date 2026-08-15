---
title: calc: equational reasoning chains instead of trans/j towers
status: open
labels: [frontend,proofs,ergonomics,design]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 6, user-confirmed wanted
(2026-08-15): issues for "tactics we definitely want". The unowned half
of proof verbosity — [[congruence-by-anti-unification]] owns inferring
cong's function; nothing owns the chain itself. Today an equational proof
is a `trans`/`j` tower with fully-spelled motives:

```heather
trans(bin_succ_abs(binc(…)), cong_succ(trans(bin_succ_abs(…), cong_succ(ih))))
```

A calc form (Lean/Isabelle-style: a chain of `_ = rhs { by }` steps,
elaborated to the same trans/j tower) is the single biggest lever on
hand-override certificates — the users the cost basis exists for. Design
should decide how a step names its justification (term? future tactic?)
and how rewriting-under-a-context is spelled (the j-motive question —
this is where it meets [[congruence-by-anti-unification]] and, later,
[[grind-port]]).
