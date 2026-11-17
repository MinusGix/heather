---
title: bv_decide: a rewriting pass before bit-blasting
status: open
labels: [bitvec,solver,tactics,perf]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

Lean's `bv_decide` runs `bv_normalize` first: constants folded, masks and shifts normalized, `x ^ x = 0`, `x - x = 0`, `x & x = x`, and so on. Many goals close there with no solver at all, and the rest blast to fewer clauses. In Heather the rules are equations about `BitVec` proved once and applied by `simp` before the reader runs, or the same identities applied to `BVExpr` with one soundness theorem (`BVExpr::normalize` with `eval` preserved).

Parent: [[lrat-certified-bitvector-decision]].
