---
title: Kernel acceleration policy: representations with adequacy and strategies, not definition shapes
status: open
labels: [kernel,design,evaluator,conversion,performance]
created: 2026-09-07
updated: 2026-09-09
---

The kernel now carries three different kinds of "acceleration", and the
2026-09-07 rounds ([[bitvec-closed-reduction-cost]], [[bitvec-bounded-add-sub]])
made the difference between them load-bearing. This issue records a policy
proposal, not a ratified architectural restriction.
It owns evaluation of the classification and possible replacement of the existing
definition-shape accelerations. The user explicitly has not endorsed every claim
in the incoming architecture discussion.

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

## Proposed policy

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

## Open questions from merge review

- Separate meaning-preserving implementation acceleration from the number of
  steps in a reference evaluator. Which general run operations admit an adequacy
  proof, and what resource accounting should accelerated execution use?
- A strategy change still needs a correctness argument. Differential tests are
  strong regression evidence, not a proof that all conversion judgments agree.
  Representation changes are not the only changes that can be verified.
- A proved propositional equality does not automatically authorize a new rule of
  definitional equality. A certified representation evaluator must specify its
  scope, termination, coherence, dependent-type interaction, and handling of
  assumptions before it can be used by conversion. Proof-producing elaboration
  using the existing equality rules is a distinct, smaller trust-boundary option.
- A compiler-correctness theorem relates modeled executions; it does not alone
  certify a result observed from an actual native process. Native proof checking
  needs explicit treatment of loading, execution, returned evidence, and the
  remaining hardware/runtime assumptions. Do not equate this with an already
  established verified evaluator.
- The immediate priority is to make ordinary core operations efficient and
  predictable. Reproduced strategy/sharing defects deserve kernel fixes rather
  than forcing every caller to manually supply a favorable proof spelling.

## Log

- 2026-09-09: The two definition-shape cases are retired
  ([[nat-run-algebra-primitives]]): a fold step is classified by evaluating
  it on fresh neutrals (`eval/probe.rs`) and the class is iterated by the
  run arithmetic in `value/algebra.rs`. The policy paragraph in
  `crates/kernel/DESIGN.md` now records the division as the standing rule
  rather than a proposal under review, with the third kind gone.

- 2026-09-08: Merged as a proposal under review. These open questions preserve the
  useful distinctions without treating the accompanying discussion as settled
  policy. [[state-projection-conversion-cost]] supplies a concrete investigation;
  [[heather-checked-construction-api]] owns a bounded construction customer.
