---
title: bv_decide: a rewriting pass before bit-blasting
status: closed
labels: [bitvec,solver,tactics,perf]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

Lean's `bv_decide` runs `bv_normalize` first: constants folded, masks and shifts normalized, `x ^ x = 0`, `x - x = 0`, `x & x = x`, and so on. Many goals close there with no solver at all, and the rest blast to fewer clauses. In Heather the rules are equations about `BitVec` proved once and applied by `simp` before the reader runs, or the same identities applied to `BVExpr` with one soundness theorem (`BVExpr::normalize` with `eval` preserved).

Parent: [[lrat-certified-bitvector-decision]].

## Log

- 2026-11-17: built, `lib/std/tactic/bv_normalize.hthr` (`BVPred::norm`, `BVPred::norm_eval`, `BVPred::norm_unsat_sound`), and `bv_decide` refutes the normalized predicate. The rules are the `BVExpr` route: one soundness theorem, no `simp`. A chain of `+` (with `a - b` as `a + -b`), `*`, `&`, `|` or `bxor` is flattened, sorted by a structural order (a negation next to what it negates, constants first) and merged: constants folded for `+` and `*`, `x & x`, `x | x` to `x`, `x bxor x` and `t + -t` cancelled, units dropped; `~~x` and `--x` cancel; `PEq` with one expression on both sides is `PConst(True)`, and `!`, `&&`, `||` absorb constants. 64-bit `x + y = y + x` went from about 22 s to 0.1 s, three-byte reassociation from 18 s to 0.1 s, 64-bit `x * y = y * x` (out of reach before) is 0.07 s. Probes: `lib/_tests/std/tactic/bv_normalize_tests.hthr`.
  Not yet: masks and shifts (`(x << 4) >> 4`, `x & 0xFF` of a zero extension), bitwise constant folding (`ofNat(a) & ofNat(b)`), negated constants (width-dependent), `x + x` as `x << 1`, `x < x` false, and moving an equation to `a - b = 0`. Add rules as merge cases in `AC::merge` or as cases of `BVExpr::norm`, each with its lemma in `AC::merge_ok`/`BVExpr::norm_eval`.
