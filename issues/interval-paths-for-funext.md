---
title: Interval type and paths as the route to function extensionality: trade-off on record
status: open
labels: [kernel,research,funext,design]
area: kernel
created: 2026-10-23
updated: 2026-10-23
---

Research record, not scheduled. From the Arend survey
(`docs/arend-survey.md` §2), which has the full argument; this issue owns
the decision and waits for a puller.

**The idea.** Arend's core (HoTT-I, Isaev) adds a primitive interval `I`
with `left`, `right` and one eliminator `coe(λx.A, a, i)`, with
`coe(…, left) ≡ a` and regularity (`coe(λx.A, a, i) ≡ a` when `x ∉ FV(A)`).
Paths are maps out of `I` with definitional endpoints. Function
extensionality is then a definition, `path(λi. λx. p x @ i)`, with a
computing inverse, and `J` is derived with definitional β.

**Why it is on record.** Heather does not assume funext
(`lib/std/itree.hthr:23`), and that is felt: tier-2 tree laws hold only up
to `Same` or depth-indexed equivalence, `Acc` is not provably a
proposition (`issues/kernel-v1-extensions.md`, log 2026-07-26), and
setoids carry what quotients would. The interval is compatible with the
no-UIP groupoid model (`docs/no-uip-model.md`): the groupoid `0 ≅ 1` is a
contractible interval, `Path` over it is `Id`, regularity and funext hold
strictly, and the strict propositions' construction is unaffected. It is
one of the few routes to funext the no-UIP decision leaves open.

**Why not now.**

1. Canonicity. Arend's paper says closed `Nat` terms need not evaluate
   (p. 3, p. 19), and `coe` in a family of path types has no rule (p. 21).
   Heather makes evaluation load-bearing (closed facts by evaluation, the
   compiler by kernel evaluation). Keeping canonicity needs structural
   `coe` rules for every former (Isaev's schemata, paper p. 25, cover only
   pairs, functions, paths and `Nat`, and their metatheory is open).
2. Regularity is a free-variable test that conversion must decide stably
   under reduction, which needs its own completeness argument against
   DeLaM ch. 06–08 and in heather-coq.
3. About seven new codes and code-recursor branches on top of 65.
4. Export: endpoint and regularity equations have no Lean or Rocq
   realisation, unlike `Wf` or irrelevance.

**A cheaper variant to weigh first**: an interval whose `coe` is admitted
at strict motives only, the analogue of the UIP-free `transp` that
`docs/sprop-design.md` keeps open. No funext, no canonicity cost. Its use
would have to come from somewhere else.

**What would pull this.** A milestone that is blocked on funext with no
workaround: a law that must hold as `=` (not `Same`) for a client that
cannot take a setoid, or bisimulation-to-equality for coinductive trees
(which would also need η for `M`, which the kernel does not have).

## What it assumes from elsewhere

- **`docs/no-uip-model.md`** owns the model. Assumed here: only that
  contexts are groupoids and `Ty 0` is sets and bijections.
- **`docs/export-fragment-design.md`** owns the export lens. Assumed here:
  only that each definitional rule needs a target realisation.
