---
title: Infer relation and operation indices from relational theorem goals
status: open
labels: [elaboration,relations,inference,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

A compact Mergeable(≈, ⊔) theorem checks, but calling merge_twice_auto(known, incoming) at SameMembers((known ++ incoming) ++ incoming, known ++ incoming) leaves an unresolved relation/operation index and cannot resolve the dictionary. Reproducer: relational_notation_uses_scoped_indices_and_reports_missing_inference in lib_setoid_mergeable. Infer only indices determined by the expected relation and operation applications or scoped evidence; never pick a default relation from the carrier. Cover concrete list use, locally constrained use, two relations/operations on one carrier, and an underdetermined call that still requests an explicit choice. Diagnostics should name the mathematical indices instead of generated #constraint/#op names.
