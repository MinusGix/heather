---
title: Refinement between two semantically different IRs for the same function
status: closed
labels: [ir,design]
created: 2026-08-01
updated: 2026-08-01
---

The full version of docs/archive/ir-simulate-design.md §6's stress test, deferred out of the items 3–4 round (see [[ir-simulate-design]] 2026-07-31): the landed three-link chain relates one IR reached through zero, one and two `LetCall` wrappers, which is the honest small version. Relating two *semantically different* IRs — the theta-loop `add` to a recursive-`Apply` `add` — is a round of its own because it wants an env-independence lemma (the two IRs walk different environments, so the invariant cannot be transported slot-by-slot as `add_loop_runs` does).

Why it matters: this is the shape every real `translate`/optimization-pass certificate has ([[compile-typeclass-design]] versioning story) — two structurally unrelated programs, one refinement. The wrapper chain exercised composition; this exercises the part composition cannot reach.

Ingredients on hand: `Refines` is a named definition, `refines_of_bounded` bridges any bounded argument into the ∃-shape, and `ir_loop`/`add_body` already live in lib/certgen/ir_v1.hthr.

## Log

- 2026-08-01: Implemented (working tree, not yet committed): new CROSS-IR REFINEMENT section in lib/certgen/ir_v1.hthr (~L1180-1436). Recursive-Apply add (add_rec_body/add_rec_prog/ir_rec, fuel profile 2a+2 vs the loop's a+5), tail-quantified invariant add_rec_runs as the env-independence lemma (arms are lexical, so the induction only closes with the caller tail universally quantified), both refinement directions via RefinesNat2 + conv_functional. Notable: unrestricted Refines between the two IRs is FALSE and refuted in-file (no_full_refines, junk-env witness); the general RefinesOn(dom: Val -> Type, ...) is blocked, filed as [[record-types-as-type-valued-functions]]. heather check ok (capped, ~41s), scripts/test ir_v1 2/2 pass.
- 2026-08-01: Closed at commit 2212204.
