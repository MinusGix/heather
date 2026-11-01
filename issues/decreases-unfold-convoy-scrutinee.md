---
title: No unfolding equation for a decreases body that matches with `match h:` on a call
status: open
labels: [frontend,elaboration,proofs,termination]
area: language
milestone: [nh-front]
code: crates/elab/src/measure.rs:1885 @ 40b9f3f
created: 2026-11-01
updated: 2026-11-01
---

Found by the `rt` pins (`lib/_tests/native/runtime/rt_tests.hthr`, V3 of
`docs/runtime-fn-setups-design.md` §12). The native examples' measured loop

```heather
fn count_down(n, acc: BitVec(64)) → BitVec(64) decreases n.toNat() {
    match h: n.eq_bit(BitVec::ofNat(0)) {
        True => acc,
        False => count_down(n.sub(BitVec::ofNat(1)), acc.add(n)),
    }
    on ?dec1 := bitvec_nat::toNat_sub_one_lt(n, h);
}
```

checks, but `count_down_unfold` is refused:

> no unfolding equation for `count_down`: the lifted `count_down#obl_1` was
> refused (this has type `__dec_scrut_158 = False`, but `eq_bit(n, ofNat(0))
> = False` is expected here)

The walk gives a `match` on a non-variable scrutinee a shared scrutinee
`let __dec_scrut_N = …;` (`measure.rs`, the `ExprKind::Match` arm), and
`lift_obligation` then quantifies the lifted `f#obl_N` over the let as an
ordinary parameter. In the body the let is an alias, so `h : __dec_scrut_N =
False` *is* `eq_bit(n, 0) = False` and the writer's `on` proof checks; in the
lifted theorem the alias is opaque, so it does not.

## Why it matters

A `runtime fn` that `decreases` pins its body by `refl` with the self-call
answered by the function itself (the body as written, convoy included, is
`count_down_body_reflects`), and `f(xs) = body[f]` is exactly `f_unfold`. So
every measured runtime fn whose loop test is a `match h:` on a comparison,
which is all of them, has no pin until this is fixed.

## Fix sketch

When a selected binder is a let alias (the walk's own `__dec_scrut_N`, or a
written block `let`), substitute its value into the lifted declaration's
parameter types and statement instead of quantifying over it, or keep it as
a `let` in the lifted body and parameter telescope. Done when
`count_down_unfold` exists and `rt_tests.hthr`'s measured pin goes through
to `count_down` itself.
