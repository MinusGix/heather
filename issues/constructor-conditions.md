---
title: Constructors with conditions: quotients by normal forms as a kernel former
status: open
labels: [kernel,research,quotients,design]
area: kernel
created: 2026-10-23
updated: 2026-10-23
---

Research record, waiting for a client. From the Arend survey
(`docs/arend-survey.md` §3).

**The idea.** Arend lets a constructor carry *conditions*: equations saying
what it computes to at some arguments, such as `Int` with `pos(n)`,
`neg(n)` and `neg 0 ⇒ pos 0` (paper p. 7; Zhang and Isaev,
arXiv:2405.12994). A function out of the type must respect the conditions,
which the checker verifies definitionally (`f(neg 0) ≡ f(pos 0)`). Arend
uses this with interval arguments for HITs, but the interval-free part is
already useful on its own: it is a quotient by a terminating, confluent
rewrite, whose carrier is the normal forms, with ordinary pattern matching
on the raw constructors.

**Why it is a kernel former and not elaborator sugar.** The obvious
encoding is a smart constructor over the raw inductive. It loses the β
rule at neutral arguments: `neg(n)` for a neutral `n` is then a stuck
function call, not a constructor, so `match neg(n) { …, neg(k) => g(k) }`
does not reduce to `g(n)`. Arend keeps `neg n` a constructor and fires the
condition only when the arguments match it.

**Clients that would pull it.** Heather sidestepped `Int` by choosing the
Lean encoding (`issues/std-int-encoding.md`), so the clients are the next
quotient-shaped types with normal forms: polynomials without trailing
zeros (Arend's `Poly` with `padd pzero 0 = pzero`, and the quotient
`QPoly`), finite multisets as lists up to permutation (`PermSet`), and
reduced fractions if `Rat` ever wants `=` rather than `Rat::Same`.

**What it would take.** A former with per-constructor condition clauses;
conversion that fires a condition on canonical arguments; an eliminator
whose branches are checked against each condition; a soundness argument
(the groupoid model of `docs/no-uip-model.md` should interpret the type as
its normal forms, given termination and confluence); code-recursor
branches; and an export story (Lean has no such conversion, so exported
terms would see the normal-form carrier and explicit normalisation).

## What it assumes from elsewhere

- **[[setoid-roadmap-and-resumption]]** owns the paused setoid area.
  Assumed here: only that setoids remain the route for quotients without
  normal forms (Cauchy reals and the like), so this does not replace them.

## Log

- 2026-11-05: gardener: cites a file it shares with [[interval-paths-for-funext]] (`docs/no-uip-model.md`).
