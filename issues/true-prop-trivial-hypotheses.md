---
title: A real True, and what pays a definitionally-trivial hypothesis
status: open
labels: [design,stdlib,frontend,ergonomics]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 3 (2026-08-15). Naive/
trivial-`inv` reprs spell `inv` as `Zero = Zero`, so every generated
`refines` signature carries `h0: (Zero = Zero)` and every consumer passes
`refl`. Two separable halves:

1. **A real `True`** with a canonical inhabitant, so the spelling stops
   being a pun. Small, stdlib-shaped; relates to
   [[default-inhabited-nonempty]]'s ladder.
2. **Who pays a definitionally-trivial hypothesis.** Coordinator's
   recommendation (pending user verdict): keep the registry statement
   UNIFORM — `refines` always takes the `inv` hypotheses — because every
   consumer of the registry (reprgen's callee steps, the certgen
   composition, future dispatch) then handles one shape, and statement
   specialization would put a branch in every consumer to remove an
   argument that generators already pay invisibly. The human-facing noise
   is better addressed by auto-discharge (elaborator fills a hypothesis
   whose type is definitionally `True` / has a registered canonical
   inhabitant) as a general ergonomic feature, not a datarepr special
   case.
