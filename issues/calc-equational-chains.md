---
title: calc: equational reasoning chains instead of trans/j towers
status: open
labels: [frontend,proofs,ergonomics,design]
created: 2026-08-15
updated: 2026-08-18
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

## Log

- 2026-08-18: Datum for this issue's value case, measured elsewhere and recorded here so a calc round does not over-claim: putting every step in checking position is NOT what unblocks the library's congruence sites. Of lib/std/int.hthr's 54 hand-spelled one-place contexts, 38 fail only because they sit in inference position (which calc would clear) and 16 fail with the expected type already in hand, because the congruence context is a fact about how the two sides COMPUTE and not how they are spelled -- and a calc step states its sides in the same unreduced terms the theorem does. See [[congruence-by-anti-unification]]'s 2026-08-18 entry. Calc's case rests on readability and on hand-override certificates, which is where it was made; it should not also be sold as this.
