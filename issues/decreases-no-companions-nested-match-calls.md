---
title: No ext, irrel or unfolding for a decreases body that branches under its match h: arm
status: closed
labels: [frontend,elaboration,proofs,termination]
area: language
milestone: [nh-front]
created: 2026-11-11
updated: 2026-11-12
---

Found by U3c step 2 of [[native-one-compiler]], writing a loop that counts a
span's newlines. A `decreases` body whose loop test is a `match h:` gets its
companions (`f::ext`, `f::irrel`, `f_unfold`) only when the arm's self-call
is the arm itself. A branch in the arm with a self-call under it loses all
three, whatever the inner branch is:

```heather
fn two_var(length, i, acc: BitVec(64), flip: Bool) → BitVec(64) decreases length.sub(i).toNat() {
    match h: i.unsigned_lt_bit(length) {
        False => acc,
        True => match flip {
            True => two_var(length, i.add(BitVec::ofNat(1)), acc.add(BitVec::ofNat(1)), False),
            False => two_var(length, i.add(BitVec::ofNat(1)), acc, True),
        },
    }
    on ?dec1 := { let below = bitvec_omega::unsigned_true(64, i, length, h); bv_omega };
    on ?dec2 := { let below = bitvec_omega::unsigned_true(64, i, length, h); bv_omega };
}
```

The function checks. `two_var::ext` is

> `two_var` has no member `ext`: its access points are `rec`, `body`

and `two_var_unfold` is

> no unfolding equation for `two_var`: a `match` holding a recursive call
> inside an argument, see docs/decreases-unfolding-design.md §3

The same with the inner branch a `match g:` on a computed scrutinee, or an
`if`. Nothing here is inside an argument as written: the inner `match` is
the outer arm. It is below the anchor only because the outer convoy's arm
is a `λ h => …` (§3: "The match must be at the anchor … Below the anchor
(inside an argument) it is still refused").

The form that keeps its companions has one self-call, the branch moved into
its arguments:

```heather
        True => two_var(length, i.add(BitVec::ofNat(1)), match flip { True => acc.add(BitVec::ofNat(1)), False => acc }, flip.not()),
```

## Why it matters

A measured `runtime fn` is proved from `f::ext` and `f::irrel`
(`runtime_measured_instance`), so a loop with two ways round, or one way
round and an early way out under the same test, is not a `runtime fn`
today: a scanner that stops at a dead state, a search that returns on a
hit. The lowering takes such a body (`count_split_body` in
`lib/_tests/native/runtime/rt_span_loops_tests.hthr` lowers, is accepted by
the function compiler and runs); what is missing is the function's own
theorem. Writers can fold the branch into the call's arguments or into the
loop test, and each is a rewrite the language should not ask for.

## Fix sketch

`Respell::match_spelled` (crates/elab/src/measure.rs) proves a match at the
anchor by the match again at a motive spelling both sides. An arm of a
convoy is the anchor's own result under the equation's binder, so the walk
can continue into it with the binder in scope and treat a match there as at
the anchor: the motive needs the result type, which is the anchor's. The
message should also name the case when it still refuses: a branch under a
`match h:` arm is not "inside an argument" to the reader.

Done when `two_var::ext`, `two_var::irrel` and `two_var_unfold` exist, and a
two-call counting loop over a span has a Heather function beside it in
`rt_span_loops_tests.hthr`.

## Log

- 2026-11-12: Fixed on master by #579 (2026-11-12): a match in an arm the walk spells out is spelled out again. On PR #551's branch after merging it, the runtime generator takes both forms as they stand: `clear_line` (an exit inside the loop) and `clear_text` (two calls of its own under a branch) in `lib/_tests/native/runtime/runtime_span_tests.hthr`, each stated at every file and accepted by the function compiler. `scan_from` keeps its exit after the loop, since `scan_token_longest` is proved over that form.
