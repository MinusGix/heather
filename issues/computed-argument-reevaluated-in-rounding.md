---
title: A computed Nat argument is re-evaluated at each use inside a rounding
status: closed
labels: [kernel,performance,floating-point]
area: kernel
milestone: [math-float]
created: 2026-10-22
updated: 2026-10-22
---

Found closing [[kernel-wide-run-comparison]]. At binary32, rounding `1/3` to
nearest by `refl` still runs out of fuel, and the cost is not any one
operation: it is the half-unit count being computed again at each place the
rounding uses it.

## Measurements (exact step counts, `--timings`)

```heather
// h = binary32().rat_h(Rat(1, 3)) ≈ 2^148
binary32().rat_h(Rat(1, 3)) = …                                  // 55,178 steps
binary32().round_signed(NearestEven, False, <h as a literal>, True) // 167,554 steps
binary32().round_signed(NearestEven, False, binary32().rat_h(Rat(1, 3)), True) // OutOfFuel at 797,080
```

Passing the same count through a function that matches on it first
(`match h { Zero => …, Succ(k) => round_signed(…, Succ(k), True) }`) checks
in 461,198 steps. So the count is re-evaluated roughly ten times when it
reaches `round_h` as an unevaluated argument: `round_h`, `nearest_h`,
`near_at`, `mid_h`, `down`, `up`, `e_of` and `m_of` each mention `h`, and
each use appears to force it anew rather than once. The same holds for a
`DivMod` field (`match d { MkDivMod(q, r) => round_signed(…, q, …) }`:
773,874 steps) and for `Finite::div` at binary32, whose quotient is also an
unreduced `Rat` (`2^45 / (3 · 2^45)` for `1/3`), and whose `rat_h` and
`rat_st` each run the long division.

## Questions

- Where is the sharing lost: δ-unfolding substituting the argument term into
  a definition's body, the bounded term cache evicting it (64K entries; the
  long division creates many closures), or a glued neutral being re-unfolded?
  Probe with a `value-metrics` build.
- If it is the kernel's, the fix is strategy, not representation. If it is
  how the library is written, `round_rat` and `Finite::div` could match the
  long division once and pass its parts, and `div` could reduce its quotient.

## Done when

`binary32().round_rat(NearestEven, Rat(1, 3))` and `one32().div(three32())`
evaluate by `refl` inside the default fuel, and the float-arith tests carry
them.

## Log

- 2026-10-22: closed. The sharing was lost in the kernel's bounded force
  cache (`ValueArena`, first-in first-out over 64K closures), not in the
  library. With the cache unbounded both done-when theorems check, in
  318,124 and 354,288 steps. Evicted closures were almost never forced
  again: the loss was one level removed. The count's closure
  (`rat_h(F, x)`, and in `div` an argument of the long division) forces
  cheaply to a *glued* neutral, whose unfolding is a closure that
  evaluation made and only the neutral reaches. The 64K thunks made while
  forcing that unfolding (110K steps in `div`) pushed the neutral out
  before the unfolding finished; the next reader forced the count's
  closure again, got a fresh neutral glued to a fresh unfolding, and ran
  the long division again. Two cache-policy changes
  (`crates/kernel/src/value.rs`, `ValueArena::cache_tm`; DESIGN.md's arena
  paragraph):
  1. **Tombs.** An evicted glued neutral leaves its unfolding keyed by its
     closure; that closure's next force is glued to the old unfolding
     (`ValueArena::reglue`). Sound by closure identity, the memo's own
     argument: the closure denotes what it denoted before.
  2. **A costly tier.** A value whose force spent at least `COSTLY_FORCE`
     (256) fuel goes to a second FIFO with its own bound, which cheap
     entries never push out.
  Each alone checks both, at 445,820 / 530,446 steps (tombs) or not at all
  (tier); together they reach the unbounded counts. No library change:
  `round_rat` and `Finite::div` are as they were. The float-arith binary32
  tests now carry `third_near` and `div_third`.
