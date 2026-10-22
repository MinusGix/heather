---
title: A computed Nat argument is re-evaluated at each use inside a rounding
status: open
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
