---
title: Carry divergence and behaviours through simulation diagrams
status: closed
labels: [relation,semantics,coinduction]
area: mathematics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/relation/transition.hthr` carries finite runs through simulation
diagrams (`StarDiagram::runs`), which needs nothing of the stutter order
`lt`. What a compiler correctness theorem also promises is that a
diverging source diverges in the target, and that a terminating target run
came from a terminating source run. Those need `lt` well-founded and an
infinite run.

## Scope

- Well-foundedness: an accessibility predicate `Acc(lt, i)` (an
  infinitary indexed family; [[indexed-infinitary-families]] says the kernel
  takes one) and `WellFounded(lt)`; that `Nat`'s `<` and `Succ(i) = j`
  are; that `Lex` of two well-founded orders is, and `Plus(lt)` of one is.
  Then `StarDiagram::compose`'s order is well-founded whenever its parts'
  are.
- Infinite runs: codata `Forever(R, a)` (a step, then forever again), as in
  CompCert's `Smallstep.forever`; the counted variant `ForeverN` with a
  well-founded index that may decrease without a step (CompCert's
  `forever_N`), which is what a star diagram carries.
- `StarDiagram::forever`: a source that runs forever from a matched state
  has a target that runs forever, given `lt` well-founded (coinduction over
  `ForeverN`, then `ForeverN` to `Forever` by well-founded induction on the
  index).
- Behaviours: terminates in a final state, diverges, goes wrong (stuck in a
  non-final state); a forward diagram into a deterministic target, with the
  source safe, preserves them both ways (`*Diagram::backward` is the step
  case already).

## Done when

A star diagram between two systems, with `lt` well-founded, maps each
source behaviour to the same target behaviour, and the composite of two
such diagrams does too.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** owns `StarDiagram` and its
  composite order. Assumed here: only those.
- **[[kernel-coinductive-types]]** owns codata (docs/kernel/kernel-coinduction-design.md). Assumed here: a corecursive
  proof of a codata predicate over a state type is accepted.
- **[[linux-sim-divergence]]** proved the tree-side exact converse
  (`LinuxSimCo`); this is the state-side counterpart.

## Log

- 2026-11-09: Done in lib/std/relation/transition.hthr. `Acc` (its `below`
  takes the smaller index with its proof, one argument, as the tier-2
  lowering asks) and `WellFounded`; `Acc::down` along runs, `Plus::last`,
  `WellFounded::plus`, `::lex` (nested: `Acc::lex_second` takes the outer
  hypothesis as a function), `::star_compose` (the composite diagram's order
  is well-founded when both parts' are), `::empty`, `::nat_pred`. Codata
  `Forever` and `ForeverN`; `StarDiagram::forever_n` (corecursive),
  `ForeverN::first_plus` (by `Acc`), `StarDiagram::forever`.
  `Forever::never_stuck`; `Terminates`, `StarDiagram::terminates`,
  `::terminates_exactly` and `::diverges_exactly` into a deterministic
  target. Going wrong is not carried: a forward diagram says nothing of a
  source that stops short, so sources are taken safe, as in CompCert. Probes
  carry divergence through the no-op pass and the composite.
