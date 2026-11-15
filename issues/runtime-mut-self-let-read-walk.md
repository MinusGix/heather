---
title: No companions for a measured mut self fn that binds a read with let before a branch
status: closed
labels: [frontend,elaboration,proofs,termination]
area: language
milestone: [nh-front]
created: 2026-11-15
updated: 2026-11-15
---

Found by the end-to-end sort demo (thread "Build an end-to-end demo program"). Insertion
sort's inner loop, written to read the byte below once:

```heather
runtime fn List::insert_below(mut self s: List<u8>, n, j, x: u64) → u64 decreases j.toNat() {
    if h: 0 < j {
        let below = s.byte_within(n, j - 1);
        if larger: x < below.zero_extend(56) { s.put_within(n, j, below); s.insert_below(n, j - 1, x) }
        else { s.put_within(n, j, x.truncate(8, 56)); j }
    } else { s.put_within(n, j, x.truncate(8, 56)); j }
}
```

had no `f::ext` (so no runtime fn: "it has no `ext` companion") and no
`f_unfold` ("a marked call this walk cannot read"). Writing
`s.byte_within(n, j - 1)` at both uses was accepted.

## Causes (three, in the order the walk met them)

1. `let below = s.byte_within(…)` is a claimed call on the mutable receiver,
   so it rebinds `s` (to itself, `byte_within` not being `mut self`). The walk
   substituted the block's `let`s into its result, which put that value where
   the arm's own `s.put_within(…);` names its receiver as a place.
2. The inner test is `decide_bit<x < below.zero_extend(56)>()`; `subst` did
   not reach type arguments, so `below` was left free in `f#ext`. (The demo
   branch carried a local fix for this in `inline_lets`, commit 39ee9bc,
   issue `decreases-let-before-plain-if-companions`.)
3. With the `let` substituted, the inner test's equation read `j`, so the
   lifted obligation the walk re-emitted selected it as a hypothesis that
   `f#body`'s never had: `f#obl_1` applied to too many arguments.

## Fix (2026-11-15)

`measure.rs`: a claimed call's rebinding is spelled as a plain `let`
(`rebind_marked`, `explicit_rebinds`) before anything is substituted; `subst`
substitutes into type arguments; and the walk keeps a `let` in the rewrite's
scope as `f#body` has it, substituting it only into the terms it builds
(`Respell::let_env`). docs/language/recursion/decreases-unfolding-design.md §3
(amendment of 2026-11-15) has the account.

Probes: `Counter::scan` in `lib/_tests/std/core/decreases_unfolding_tests.hthr`;
`List::insert_below` and `List::sift_let` (with a `let` shadowing the measured
index) in `lib/_tests/native/runtime/runtime_span_tests.hthr`, each run by
`program_run` at a literal.

Related: [[measured-loop-inner-if-companions]], [[decreases-mut-call-statement-companions]].
