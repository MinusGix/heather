---
title: Design the Compile typeclass and certificate coupling
status: open
labels: [compiler, typeclass, design]
blocked-by: [ir-simulate-design]
created: 2026-07-22
updated: 2026-07-22
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
