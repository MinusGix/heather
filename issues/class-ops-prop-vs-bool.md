---
title: Class operations across the kerneltime/runtime split: Prop laws, Bool programs, certificates between
status: open
labels: [design,traits,compiler,stdlib,delam]
created: 2026-08-07
updated: 2026-08-09
---

From reviewing `Cmp<A>` (`le : A -> A -> Bool` with `= True` laws,
2026-08-07). The question "should `le` return `Bool` or `Prop`?" dissolves
differently in Heather than in Lean, because a mathematical function and the
evidence that it has executable code are separate objects.

Current lean (2026-08-09): the public mathematical API should contain **one
propositional relation** — `le : A -> A -> Prop` (or plausibly `SProp` where
irrelevance is wanted). A raw mathematical instance need not be decidable. An
executable instance gives that same `le` a `Compile` instance whose runtime
representation and correctness theorem implement the decision. There need not
also be a public `leb : A -> A -> Bool`; in many Lean APIs that function is an
artifact of making computation visible in the mathematical interface.

This makes the default split:

- **Specification:** `le : A -> A -> Prop`, used by all mathematical laws and
  notation.
- **Execution evidence:** a `Compile` instance for that predicate, carrying
  whatever Boolean/runtime representation and semantic relation says that the
  result decides `le(x, y)`.
- **Optional reification:** a named Boolean/reflection object only where a
  mathematical consumer genuinely needs to manipulate the Boolean function
  itself (Boolean algebra, circuits, finite automata, short-circuit structure,
  reflection proofs), not merely in order to run the proposition.

The landed `Cmp` (Bool plus `= True`) remains an honest v1: it inlines the
specification into its decision procedure. A future migration should not be
designed until the questions below determine whether it becomes the
proposition-facing order class, a deliberately reified decided refinement, or
temporary compatibility surface.

Open sub-questions, recorded not answered:

1. **Logical decidability versus runtime compilability.** A value of
   `Decidable(p)` permits kerneltime case analysis into `p + not p`; a Compile
   instance supplies executable code and a correctness theorem. Does Compile
   canonically induce `Decidable`, does it only induce a runtime branching
   interface, or are those intentionally different claims?
2. **Representation of a compiled proposition.** Is `Prop` represented by
   `Bool` through the general Datarepr/refinement machinery, or does compiling
   a proposition need a predicate-specific certificate shape? Owned on the
   compilation side by [[datarepr-separation]] and
   [[compile-typeclass-design]].
3. **Source branching.** What evidence must `if p { ... } else { ... }` demand
   when `p : Prop`: logical `Decidable(p)`, executable `Compile(p)`, or a small
   interface both can provide?
4. **Explicit reflection.** If a library really needs `b : Bool` together with
   `b = True <-> p`, is that an ordinary record constructed from Compile, a
   class, or simply a theorem about a separately named Boolean function?
5. **Class dictionaries.** What does a Compile instance for a relation
   projected from a class dictionary look like: per concrete instance,
   parametrically from compiled fields, or attached to the dictionary value?
6. Whether `SProp` fields in classes interact with record lowering or
   elimination restrictions today.

## Log

- 2026-08-09: Direction corrected in the high-level library discussion. The
  preferred default is no parallel `leb`: state the mathematical relation once
  in Prop/SProp and let a Compile instance provide its executable decision.
  A reflected Bool function must justify itself as mathematical data. The
  remaining design seam is whether logical decidability and runtime
  compilability share one consumer interface or remain distinct evidence.
- 2026-08-09: Rider from the algebra.hthr cleanup review (2026-08-09): a symbol spelling for Cmp's le belongs to this issue, not to a designation today — <= already lexes and means Le, the proposition, at the non-associative comparison rung, so designating <= at a carrier to the Bool-valued le would make x <= y a Bool in one file and a Type in another. The right home is the bridge this issue designs: the spec-side class owns <=, and the decided refinement stays named (leb/le) until then.
