---
title: Make Omega certificate dependencies independent of incidental caller imports
status: open
labels: [tactics,omega,modules,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

The subtype positivity probe exposed extra imports needed by reconstruction.
With `import nat; import omega;`, the ordinary theorem
`sum_positive(n, m: Nat, positive: 0 < n): 0 < n + m { omega }`
fails on generated `Not`. Adding `logic` advances to an unavailable
`int::zero_le_ofNat`. The checked probe imports `logic`, `int`, and `list`
as well as `nat` and `omega`, following existing Omega clients.

Let the certificate builder resolve its own library dependencies without
requiring source-level imports solely for generated proof syntax. Preserve
normal visibility for user expressions and resistance to caller name
collisions; do not globally open all transitive imports.

Acceptance: the Nat theorem checks with its source-level imports alone;
ordinary scope rules remain intact; misleading generated-name errors are
replaced by actionable diagnostics when the certificate library is absent.

Probe: `docs/showcase/positive_omega.hthr`. Related:
[[omega-linear-arithmetic]], [[omega-local-proof-aliases]].
