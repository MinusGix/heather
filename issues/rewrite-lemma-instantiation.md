---
title: Instantiate a rewrite's equation by matching its left side against the goal
status: open
labels: [frontend,elaboration,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

`rewrite(h, e)` (`docs/equation-rewrite-design.md`) needs `h` fully applied:
`rewrite(k.add_comm(n), …)`. Lean's `rw [Nat.add_comm]` leaves the lemma's
arguments open and finds them by matching its left side, with those arguments
as pattern variables, against the goal's subterms — the first match in
traversal order fixes them, and every occurrence of that instance is
rewritten. This is what makes long chains pleasant to write.

Wanted: `rewrite(Nat::add_comm, e)` and partial applications
(`rewrite(k.add_comm, e)`), elaborated by inferring the proof's type as a
telescope ending in `a = b`, opening its explicit and implicit binders as
pattern variables, and matching `a` against goal subterms. Explicit `@`/named
arguments still pin variables. `at := k` numbers occurrences *of the chosen
instance*, as now. A left side that is a bare pattern variable (`x = …` with
`x` open) matches everything and is refused.

Matching should be first-order and syntactic on the instance's head (see
[[rewrite-keyed-conversion-matching]] for the conversion half), and the
pattern variables must all be fixed by the match or by the caller; a variable
the left side does not mention (only the right side does) is an error that
asks for it explicitly.

## What it assumes from elsewhere

- **[[equation-rewrite-in-goal]]** (closed) owns the form and its motive.
