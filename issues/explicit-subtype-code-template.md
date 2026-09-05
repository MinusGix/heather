---
title: Emit an explicit subtype operation and projection proof from Heather templates
status: closed
labels: [metaprogramming,subtypes,transfer]
created: 2026-09-05
updated: 2026-09-05
---

First executable slice of [[subtype-transfer-and-evidence]] and
[[setoid-auto-lifting]], following `docs/smart-subtype-inheritance.md`.

## Acceptance

- Provide an explicit entry point for a named context-only Heather code
  template. Respect module visibility and local shadowing, rescope globals,
  reject unsupported signatures, and kernel-check emitted code.
- Write the binary wrapper in Heather with explicit ambient/target types,
  invariant, projection, constructor, source operation, and closure evidence.
- Emit a companion projection proof from an actual constructor/projection law.
- Check positive addition against the manual wrapper, with an ordinary ambient
  associativity proof. Missing closure evidence must be resumable; incorrect
  evidence and an unjustified positive zero must be refused.
- Keep automatic closure search, reflection-based ingredient discovery,
  conditional API suggestions, evidence-policy adaptation, and whole-instance
  generation in the parent issues.

## Log

- 2026-09-05: Started the explicit template slice. `docs/explicit-subtype-lift-round.md`
  describes `emit_code`, the two templates, and their checked-client target.
- 2026-09-05: Complete. `lib/subtype_code.hthr` emits the binary wrapper and
  projection certificate; `docs/showcase/lift_positive.hthr` checks positive
  addition, agreement with the manual wrapper, and ambient associativity.
  Regressions cover resumable closure evidence, wrong evidence, positive zero,
  a constructor that changes values, template scope and signature checks, and
  preservation of the template/payload call boundary in lint advice. Focused
  quotation/relational tests: 77 passed before the final lint correction. Final
  plain `furnace run -- scripts/test`: 2,374 passed, 0 failed, 5 ignored.
  The final CLI showcase check passed with only existing library warnings.
