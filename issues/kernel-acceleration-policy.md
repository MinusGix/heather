---
title: Kernel acceleration policy: representations with adequacy and strategies, not definition shapes
status: open
labels: [kernel,design,evaluator,conversion,performance]
created: 2026-09-07
updated: 2026-09-07
---

The kernel now carries three different kinds of "acceleration", and the
2026-09-07 rounds ([[bitvec-closed-reduction-cost]], [[bitvec-bounded-add-sub]])
made the difference between them load-bearing. This issue records the policy
so that the next cliff is answered in the right class, and owns the
retirement of the one class that should not grow.

## The three kinds

- **Representation changes with an adequacy argument.** Saturated `Nat`
  runs ([[succinct-inductive-values]]): values mean the same, the reduction
  relation is unchanged up to a bisimulation, and the change applies to every
  value of the type rather than to definitions of a shape. This is the right
  kind. It is also the only kind that can eventually be *verified* rather
  than trusted (the "verified fancy kernel later" working note): once
  Heather-in-Heather can state adequacy, a representation trick proved there
  is a fast path the kernel may adopt.
- **Strategy changes with no semantic content.** δ-lazy conversion, glued
  neutrals, the same-head spine comparison, the newer-head single step, and
  transparent unfolding of a side with no defined head to meet. They perform
  the same unfoldings in the same order with the same fuel, so they need
  neither a representation nor an adequacy proof; the differential oracle
  against the syntax domain is the whole check. This kind is safe to keep
  adding.
- **Pattern-matching on definition shapes.** `nat_step_successors` (the
  successor algebra `su^p ih`) and `nat_step_synchronizes` (the two-counter
  fold) in `crates/kernel/src/eval.rs`, which unfold a glued scrutinee and
  scale or cancel runs only when the eliminator's step closure has exactly
  that spelling. They are fragile under respelling — `nat::sub` is not the
  synchronous shape, so `int::sub(OfNat(2^63), OfNat(2^64))` peels — and each
  one is a small trusted claim about a syntactic pattern. This is debt.

## Policy

- A new cliff is first attributed: is the cost the calculus's own (unary
  iteration over a magnitude is 2^63 steps in ch. 06, and no kernel makes it
  cheap without computing something else), a strategy artefact (replays,
  eviction thrash, missed sharing), or a representation gap (a canonical
  form large relative to the derivation)?
- Calculus-inherent cost is answered in the **library** — a definition
  whose reduction cost matches its meaning ([[bitvec-width-bounded-defaults]])
  — or by **reflection** ([[reflection-through-decide-instances]]), never by
  a kernel special case for that definition.
- Strategy artefacts are fixed in the kernel freely, gated by the
  differential suites and `scripts/bench --check`.
- Representation gaps get a representation change with its adequacy
  argument written down in `crates/kernel/DESIGN.md`, generic over the type.
- No new definition-shape cases. The two existing ones are retired when a
  general mechanism covers their customers: run arithmetic on `elim_Nat`
  itself (a fold over a run whose algebra is a run-endomorphism is one
  program application — the successor algebra generalizes to any algebra the
  representation can express) and run cancellation as a property of the
  order/subtraction *representation* rather than of one fold spelling. Until
  then they stay documented as exceptions, with the customers that keep them
  alive named beside them.
- Whatever is not accelerated is **refused honestly**: `OutOfFuel` with a
  reason, never a process abort ([[kernel-native-depth-budget]]). A slow
  definition is a visible design signal, which is what keeps the other rules
  optional rather than urgent.

## Acceptance

- The policy paragraph lives in `crates/kernel/DESIGN.md` beside the δ-lazy
  refinements, and the two shape cases carry a pointer to it and to their
  customers.
- Each of the two shape cases has a named replacement issue or is retired,
  with the customers ([[bitvec-ofnat-large-literals]]'s doubling chains,
  [[nat-order-large-run-comparison]]'s order facts) green on the general
  mechanism.

## What it assumes from elsewhere

- **[[succinct-inductive-values]]** owns the representation and would own
  the generalized run algebra.
- **[[kernel-native-depth-budget]]** owns honest refusal.
- **[[reflection-through-decide-instances]]** owns the library-side answer
  for closed facts too large to reduce.
