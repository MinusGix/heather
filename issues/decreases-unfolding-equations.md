---
title: Unfolding equations for declarations defined by a measure
status: closed
labels: [frontend,elaboration,proofs,design]
created: 2026-09-05
updated: 2026-09-05
---

Filed off the [[termination-measures]] round (2026-09-05). A declaration
`fn f(x̄) -> T decreases e { body }` elaborates to a recursor on the bound
`Succ(e)`, applied at `lt_succ_self(e)` (docs/termination-measures-design.md
§2). At **closed** arguments it computes — `gcd(12, 8) = 4` is `refl` — and
at an argument whose measure is a *constructor* it steps once. At an open
argument it is stuck, and a recursive occurrence inside the unfolded body is
the recursor at the *bound's predecessor* with a *transported* proof, which is
not `f(ȳ)` — the same term at `Succ(e[ȳ])` and `lt_succ_self` — so a proof
about `f` by induction cannot rewrite `f(ȳ)` with its induction hypothesis.

Every well-founded-recursion story has this (Lean's `f.eq_1`, Coq's
`Function` equations). The fix is the same: a generated theorem

    f_unfold(x̄): f(x̄) = body[f]

proved once from *bound irrelevance* — `F(n, x̄, h) = F(m, x̄, h')` for any
two bounds, by induction on `n` — which is the one lemma the lowering owes
and can generate. Until then, a `theorem … decreases` about a *structural*
function works (the theorem's own recursion is by measure, the function it
talks about unfolds), and a theorem about a `decreases`-defined function is
stated at closed arguments or by hand.

## What it assumes from elsewhere
- **[[termination-measures]]** owns the lowering. Assumed here: only that a
  `decreases` declaration is one `elim_Nat` on `Succ(e)` whose step's ih is
  applied under a transported bound.

## Log

- 2026-09-05: Chartered (user, 2026-09-05) as Part A of one managed round, ahead of [[mutual-recursion-declarations]]: design pass first (docs/decreases-unfolding-design.md), then implementation; bound-irrelevance route as filed, generation by source re-spelling preferred if it probes clean. Customer: a measure-induction theorem about a decreases-defined function that cannot be proved today.
- 2026-09-05: LANDED (2026-09-05, managed round; docs/decreases-unfolding-design.md). The filed route needed one thing that did not exist — extensionality of the body functional in its ih — so the generator proves it as a congruence walk over the body (§1); the recursor is lifted to named globals f#body/f#rec (§2, amends the measures doc §1/§5); each obligation is lifted to its own opaque theorem f#obl_N referenced from body and companions, after §8 item 5 refuted 'omega is a function of the goal' (§4). fn only; one whole-body equation; silent skip with a named reason at the f_unfold reference. Residue: [[unfolding-computed-scrutinee]] (merge's shape); a self-call under a λ stays out (funext). Suite 2395 -> 2414 (coordinator run, 0 failed).
