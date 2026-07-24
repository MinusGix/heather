---
title: Design the Compile typeclass and certificate coupling
status: open
labels: [compiler, typeclass, design]
blocked-by: [ir-simulate-design]
created: 2026-07-22
updated: 2026-07-23
---

The certifying-compilation contract: a function is compilable iff it has a
`Compile` instance containing (a) IR production and (b) an `equiv` theorem
that the IR simulates to the same result as the kerneltime function. The
compiler consumes only proof-carrying instances — privileged operationally,
never logically.

Settled so far:

- Coupling via same-typeclass membership is sufficient (equiv need not
  literally reference a sibling field); producing IR standalone without a
  source function stays legitimate.
- Multiple targets: index the class by target — `Compile[Cpu] f`,
  `Compile[Gpu] f` — rather than allowing multiple instances of one class.
  Coherence per (f, target); target selection is instance resolution, not
  ambiguity-breaking.
- Instances are keyed on *syntax* (boxed code is intensional), so
  coherence is per-syntactic-definition and refactoring a function
  invalidates its instance. Deliberate choice, not an accident.

Open: whether "typeclass" is even the right notion here vs. something more
bespoke; revisit once the kernel exists.

## Log

- 2026-07-23: Surface-syntax round 1 leaning recorded (docs/sketches/surface-v1.md §6): dictionaries are first-class values (records over Σ), so trait-vs-typeclass is purely resolution policy; lean coherent-by-default (canonical instances suit certifying compilation and intensional instance keying), explicit named dictionaries as the multiple-structures escape. Full design still owned by this issue.
- 2026-07-23: Round-2 sketch adds: let instance C for T = v; scoped override — safe specifically because instances are certificate-carrying (semantics pinned by equiv proof; instance choice is operational, coherence = predictability not soundness). Resolution-from-main composes: compiler walks the call graph resolving in-scope instances per site. Also surfaces the elaboration-determinism requirement implied by keying on elaborated syntax (.code).
- 2026-07-23: Round-3 sketch: ctx-parametric instances (ir(ctx: CallCtx)) with forall-ctx equiv — specialization certified by one theorem, not per copy; artifact dedup keys on (function syntax, ctx descriptor); descriptor coarseness is the design lever (CallCtx shape is an [[ir-simulate-design]]-adjacent decision). Context facts may include caller proofs (e.g. bounds evidence) so ir() may optimize justified-by-theorem.
