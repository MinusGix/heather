---
title: A subtype for unsigned P3109 data at the API boundary
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-26
updated: 2026-11-26
---

An unsigned P3109 format is the nonnegative half of a signed envelope
(docs/library/float-p3109-design.md D2): `Format::p3109(K, P, Unsigned, d)`
admits negative `Finite` values, and the projection and codes keep unsigned
results nonnegative (`project_unsigned_nonneg`, `decode_datum`). That kept
every theorem intact, but a user can build a negative float of an unsigned
format by hand.

Add a thin subtype at the API boundary, a float with `Float::Unsigned`
proof, with `decode`/`encode`/`project_unsigned` typed through it, so the
boundary rules the junk out while the proofs stay on the envelope.
