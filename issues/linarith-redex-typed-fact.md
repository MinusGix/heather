---
title: linarith rejects a pattern-bound fact whose type is not yet reduced
status: closed
labels: [tactics,linarith]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

The `linarith` counterpart of the closed [[omega-redex-typed-fact-ignored]].
Probe on master 5e26232:

```heather
theorem r2(dd: Rat, hdd: 0 < dd): ∃ k: Nat, Rat::inv_pow2(k) + Rat::inv_pow2(k) < dd + dd {
    match dd.archimedean_inv_pow2(hdd) {
        Exists(k, small) => Exists(k, linarith(small)),
    }
}
```

The error is "`linarith` combines `<`, `<=`, `≈` and `¬(x < y)` facts at
`Rat`; `small` is `Lt(inv_pow2(k), dd)`". The fact is a `<` at `Rat`. Its
type, as the pattern binds it, is the `Exists` predicate applied to `k`, and
`linarith` does not reduce it before reading. Restating it with
`let sm: (Rat::inv_pow2(k) < dd) = small;` works. That is the workaround in
`Format::off_grid_of_apart` (lib/std/num/float/round_real.hthr).

Fix as omega's was: read a fact's type through its contractum.

## Log

- 2026-10-31: Fixed. `linarith`'s `Reading::of` and omega_cert's `integral_sides`/`integral_order` now read a fact through its head β-contractum (`spelling::beta_head_ty`, shared with omega's `push_conjuncts`), at a field, at Int/Nat and in nlinarith. Probes in lib/_tests/std/tactic/linarith_tests.hthr; the restating `let sm` in `Format::off_grid_of_apart` is gone.
