---
title: Package the subtype representation and exercise Omega closure
status: closed
labels: [stdlib,subtypes,transfer,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

Follow [[explicit-subtype-code-template]] with a reusable representation
interface. Details: `docs/packaged-subtype-round.md`.

## Acceptance

- Package the projection, constructor, invariant evidence, and actual
  constructor/projection law. Keep the predicate as an explicit index.
- Reuse the same package for the generated operation and projection theorem;
  infer carrier types and the named invariant from the package at client calls.
- Retain resumable closure goals and rejection of invalid representation laws.
- Check an Omega-generated positivity proof as the lifted operation's closure,
  and refuse a false positivity goal.
- Track the exposed gaps separately: [[omega-local-proof-aliases]],
  [[omega-certificate-imports]], and [[lambda-predicate-index-inference]].

## Log

- 2026-09-05: Implemented the package and concise wrappers in `lib/subtype.hthr`.
  The first focused round checked both showcases and an Omega refusal control.
- 2026-09-05: Complete. The final focused target passed all 46 tests, including
  packaged closure repair and the Omega-backed operation/projection theorem.
  Both showcases passed through the CLI. Final plain Furnace suite: 2,375
  passed, 0 failed, 5 ignored. The three linked follow-ups remain open.
