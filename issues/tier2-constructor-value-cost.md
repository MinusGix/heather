---
title: Make a written tier-2 constructor value cost what a call does
status: open
labels: [elaboration,inductives,performance]
area: language
created: 2026-11-06
updated: 2026-11-06
---

A tier-2 constructor applied in an expression (`Pure(a)`, `Ask(r, k)` at
`Tac`; ITree's `Ret`/`Vis`) elaborates to its `W` encoding written out:
`(λ(c : C). ⟨sup(ℓ; λy. fst(c…)), …snd(c…)…⟩) child`
(docs/inductives/inductive-tier2-w-lowering.md §6, §14), with `⟦D⟧` and the positions
in its pair, `sup` and child annotations. The kernel gate checks those
annotations again at every occurrence. Measured on probes over `tactic`
(`--timings`, width one, 2026-11-06): `fn () → Tac<Nat> { Pure(1) }` is about
20k kernel steps, the same body through a one-line `fn pure<A>(a: A) →
Tac<A> { Pure(a) }` about 2.7k, and a plain `Option` constructor a few
hundred. A `match` whose wildcard arm covers `n` constructors copies the arm
`n` times, so a `Tac` value under `_` on `Head` (12 constructors) or `Req`
(29) is paid per copy: grind's `sides_of` was 2.5M steps.

[[grind-closure-cost]] worked around it in the library: tactics write
`pure(a)`, `ask(r)` and `ask_then(r, k)` (lib/std/tactic/tactic.hthr), and
read a big view through a plain function before matching. That halved the
cold elaboration of grind's closure. The workaround is a house rule that
every tactic author has to know, and every other tier-2 type (interaction
trees, codata carriers) still pays.

## Done when

A written tier-2 constructor value costs about what the call does: for
instance a per-constructor generated definition (`GenDef`, keyed by the
declaration's tag and the constructor's position, over `D#canon`'s
telescope plus the fields) that `build_ctor_w` references at the registered
profile, as §13 did for the leaf predicate. Readers that recognise a
constructor value by its spelling (the host's `View`/`HCtor`, `inj`/`absurd`
on tier 2, diagnostics) keep working on the reference. Then `pure`/`ask` in
tactic.hthr can stay as names but stop being a rule, and the comment above
them says so.

## What it assumes from elsewhere
- **[[tier2-type-code-functions]]** owns naming `⟦Tac<A>⟧` itself. Assumed
  here: only that the constructor's annotations shrink with it, which makes
  this smaller but not unnecessary (the probe's `Tac<Nat>` alone was ~8k
  steps against the constructor's ~20k).
