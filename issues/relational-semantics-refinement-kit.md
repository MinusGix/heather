---
title: Develop relations and refinement as a reusable semantics kit
status: open
labels: [stdlib,logic,semantics,design]
created: 2026-08-25
updated: 2026-08-25
---

Heather's current executable specifications, notably `ir_v1`, are functions
whose successful results are functional.  A machine contract also needs to
say that several outcomes are permitted: an architecturally undefined flag
may take either value while every unrelated location remains constrained.
This wants ordinary relations and refinement laws, not a global `Unknown`
value and not an architecture-specific nondeterminism monad.

Build a small reusable kit around relations such as `A -> B -> Type`.  It
should make the direction of refinement impossible to guess wrong, embed
deterministic functions without ceremony, express local choice/havoc, and
compose one-step relations into finite executions.  This is a mathematical
library first; it need not choose Heather's eventual user-visible effects
surface.

## Acceptance

- Define relation inclusion/equivalence, identity, converse, composition, and
  deterministic graph embeddings, with explicit names for may- and must-style
  refinement if both are retained.
- Prove reflexivity/transitivity, associativity/unit laws for composition, and
  monotonicity of composition under inclusion.
- Provide products/sums or framing combinators that lift a relation over one
  component without losing facts about the other components.
- Express finite nondeterministic choice and localized havoc relationally.
  Demonstrate that havocing one flag does not havoc a register beside it.
- Give a finite multi-step/fuel closure sufficient for sequential machine
  programs, with concatenation and per-step refinement theorems.
- Separate semantic outcomes such as normal return and fault from *coverage*
  such as an unsupported instruction; show in a toy model that they cannot be
  accidentally interchanged.
- Connect the kit to one deterministic `ir_v1`-shaped example and one genuinely
  nonfunctional example.  Record any proof ergonomics or expressiveness gap
  exposed by the comparison.

No set-valued executable representation is required initially.  Existential
outputs in a proposition are the specification; a simulator may later select
concrete witnesses as a separate executable view.

## What it assumes from elsewhere

- **[[effects-direction]]** owns coinductive traces, interaction trees, and the
  programming surface for effects.  This issue owns only finitary relational
  algebra and does not select the eventual external-effect story.
- **[[ir-simulate-design]]** owns the deterministic structured IR semantics.
  Assumed here: it is a customer for deterministic embedding, not something
  to rewrite around nondeterminism.

## Log

- 2026-08-25: Filed from the distinction between architectural choice,
  specified faults, and gaps in model coverage.  Keeping that distinction
  generic also serves protocol, concurrent-step, and optimizer semantics.
