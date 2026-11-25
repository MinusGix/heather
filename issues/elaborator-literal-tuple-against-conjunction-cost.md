---
title: Checking a literal tuple against a literal conjunction is superlinear in the elaborator
status: open
labels: [elaborator,performance]
area: tactics
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-residual-discharge-restated]]. A discharge written in source as a literal conjunction `∥P∥ ∧ (… ∧ True)` with N components and a literal anonymous tuple `⟨p, ⟨…, trivial⟩⟩` ascribed to it elaborates in time superlinear in N: 13, 58, 274, 1850 ms at N = 32, 64, 128, 256 (fresh store per run), while the kernel's work on the same declaration is linear (8.3k to 60.5k steps, gate 7 to 56 ms). The same statement and proof written as recursive definitions elaborate in negligible time (76 ms total at N = 512). The generated probes are in the log of [[ownership-site-facts-into-the-checker]].

## Wanted

Measure where the elaborator spends it (checking each tuple component against the conjunction's whnf? re-normalising the expected type per component?) and make it linear, or record why a generator should never write such a term in source.

## Done when

A literal tuple ascribed to a literal conjunction of 256 components elaborates in time linear in its size at 128, 256 and 512 (the surface nesting limit allowing).
