---
title: Keep large setoid dictionaries practical to project from
status: open
labels: [frontend,traits,performance,setoids]
created: 2026-09-05
updated: 2026-09-05
---

The first flat `FiniteSets<S,A>` interface checked, but the abstract
`empty_right` client exhausted the 4 GiB test limit. Grouping operations in a
tagged `SetOperations` parent progressed through 18 declarations, then exhausted
the same limit at `generated_member_after_update` (about 283 seconds).

Supplying `ops: SetOperations<S,A>` as a value index to `FiniteSets` avoids
repeated preceding-field projections inside law types. All 19 abstract client
declarations then checked and reached the backend in about four seconds. This
is the chosen library layout, not a general fix to dependent dictionary cost.

Keep this issue open for a measured compiler improvement: preserve all laws,
compare flat/tagged/indexed versions under ordinary resource rails, and reduce
annotation/projection growth without relying on clients to discover the cheap
layout. Reproducer/customer: `docs/showcase/finite_set_client.hthr`.
Related: [[finite-set-client-design]], [[scoped-multi-parameter-type-projection]],
[[application-annotation-sharing-cost]].
