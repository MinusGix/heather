---
title: Refinement between two semantically different IRs for the same function
status: open
labels: [ir,design]
created: 2026-08-01
updated: 2026-08-01
---

The full version of docs/ir-simulate-design.md §6's stress test, deferred out of the items 3–4 round (see [[ir-simulate-design]] 2026-07-31): the landed three-link chain relates one IR reached through zero, one and two `LetCall` wrappers, which is the honest small version. Relating two *semantically different* IRs — the theta-loop `add` to a recursive-`Apply` `add` — is a round of its own because it wants an env-independence lemma (the two IRs walk different environments, so the invariant cannot be transported slot-by-slot as `add_loop_runs` does).

Why it matters: this is the shape every real `translate`/optimization-pass certificate has ([[compile-typeclass-design]] versioning story) — two structurally unrelated programs, one refinement. The wrapper chain exercised composition; this exercises the part composition cannot reach.

Ingredients on hand: `Refines` is a named definition, `refines_of_bounded` bridges any bounded argument into the ∃-shape, and `ir_loop`/`add_body` already live in lib/ir_v1.hthr.
