---
title: Seeing through a quote in the instance matcher: only with a bounded arm
status: open
labels: [elaboration,representation,performance,design]
created: 2026-09-15
updated: 2026-09-16
---

docs/closed-argument-and-parameter-domain-spelling-design.md §5.2: the name arm of `see_through` (unspell a registered reference to the registry's copy) is safe because the copy is what the walk was going to compare anyway; adding `decoded` for a code literal (`El («Nat»)` against `Nat`, the `identity-match-El/Nat` decline on `Certified` and `Exists`) was built and refused — a quote can be a multi-megabyte literal and decoding it on every mismatch node overflowed the stack on every workload. If a later table puts the quote pair on top, the shape to try is a bounded arm: decode only against a small former (a primitive, a `Ty`) or under an explicit node budget, never an unbounded decode on a mismatch. The pinned negative in the slice's tests is the one that changes. Triggered when `identity-match-El/Nat` (or the `El⌜⌝` head pairs) is a top row after [[elaborator-canonical-type-spelling]]'s name slice.
- 2026-09-16: Trigger fired: on `complete_post` the `El⌜⌝` pairs are 95 947 of 110 851 misses and 5.5 of 7.3 s (docs/complete-post-attribution-design.md §1.2). Not chartered yet: the elaborator-side slice (quote the respelled type, [[elaborator-canonical-type-spelling]]) is tried first, and this arm becomes the owner only if that spike finds `emit_ty` does not reach the open components (design §5.1). Still bounded, never an unbounded decode.
