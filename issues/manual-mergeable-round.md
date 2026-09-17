---
title: Check the manual Mergeable foundation and showcase
status: closed
labels: [stdlib,relations,algebra,setoids,testing]
created: 2026-09-04
updated: 2026-09-17
---

Implement the bounded first round agreed after the client-first design:
heterogeneous respectful functions, named relation-indexed algebraic laws,
lists compared by membership, and the explicit `merge_twice` proof.

## Acceptance

- Define the shared function relator and identity/application/composition rules.
  Make existing `PreservesRelation` a specialization without changing clients.
- Compose `Mergeable` from equivalence, binary compatibility, associativity,
  commutativity, and idempotence; retain independent named-law use.
- Supply a generic List instance for equality of members and append. Reuse
  existing membership proofs; do not require decidability or deduplication.
- Check `merge_twice` through explicit compatibility, at open list inputs and
  an identity-based control. Pin exact parent proof reuse.
- Refuse using membership commutativity as identity commutativity. Include a
  checked refutation of length compatibility and a truly heterogeneous
  function-relation composition example.
- Check the realized showcase in the test suite, document its gaps against
  the idealized version, and run plain Furnace `scripts/test` for final validation.

No automatic lifting, compact binder syntax, relational calc extension, quotient
former, general subtype machinery, or wholesale algebra migration belongs to
this bounded round. Their existing owners retain those deliverables.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns the broader relational API; this round
  implements its function-relator foundation only.
- **[[relation-indexed-algebra]]** owns migration and the eventual full hierarchy.
- **[[setoid-core-api]]** owns the broader manual setoid acceptance, including
  rational and function-valued customers not required for this slice.
- **[[algebraic-theory-composition]]** owns canonical parent dictionaries.
- **[[finite-set-client-design]]** owns the wider finite-set client progression.
- **[[setoid-auto-lifting]]** owns the generator that will reproduce these proofs.

## Log

- 2026-09-04: Started the user-authorized manual implementation round. The
  initial library and test drafts are in place; verification is in progress.
- 2026-09-04: LANDED. `std/relation_props` supplies Respectful and its
  identity/application/composition rules; PreservesRelation is its definitional
  specialization. `std/algebra_rel` supplies the named laws, composed Mergeable,
  and explicit merge_twice proof. `std/list_setoid` proves and registers the
  generic membership/append instance. `docs/showcase/mergeable.hthr` is checked
  by the new four-test target, including an identity control and a checked
  length-compatibility refutation. Exact parent-proof reuse and refusal at the
  wrong relation are tested. Implementation gaps are in
  `docs/manual-mergeable-round.md`; no kernel/frontend changes were necessary.
- 2026-09-04: Final validation: focused new + existing relation targets 9/9;
  plain `furnace run -- scripts/test` completed with 2,319 passed, 0 failed,
  and 5 ignored (433 seconds total including warmups). Rust formatting,
  document links, tracker lint, and `git diff --check` pass. This bounded scope
  is complete; the broader owners listed above retain their remaining work.
- 2026-09-04: **[[iff-in-type-valued-body]]** now owns the parenthesized connective parsing gap; the completed round retains its checked Iff workaround.
- 2026-09-17: [[iff-in-type-valued-body]] closed the parenthesized-connective row: `std/list_setoid` now writes `(a: A) → (Mem(a, xs) ↔ Mem(a, ys))` and the round doc's gap table records it. The round's own Iff workaround is gone; nothing else in the round moved.
