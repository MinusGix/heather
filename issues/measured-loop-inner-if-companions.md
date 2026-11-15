---
title: No companions for a measured loop whose inner test is a plain if under the loop's test
status: closed
labels: [frontend,elaboration,proofs,termination]
area: language
milestone: [nh-front]
created: 2026-11-15
updated: 2026-11-15
---

Found writing an insertion-sort probe in the read-then-store thread
(`rt-file-read-before-store`). A measured `mut self` span loop whose inner
test is a plain `if` under the outer `if h:`

```heather
runtime fn List::sift(mut self s: List<u8>, n, j, key: u64) → u64 decreases j.toNat() {
    if h: 0 < j {
        if key < s.byte_within(n, j - 1).zero_extend(56) {
            s.put_within(n, j, s.byte_within(n, j - 1)); s.sift(n, j - 1, key)
        } else { j }
    } else { j }
}
```

lost its `ext`: "a `match` below another `match`'s arm whose recursive call's
obligation reads the inner scrutinee's equation: bind it as `match g: …`".
Only `match less: …` certified.

## Cause

`Respell::match_below_anchor` counted the inner test as an `AutoEqs`
candidate wherever an arm recurses; `Rewrite` counts only a scrutinee it gives
an alias (one whose type it can write, `Rewrite::auto_candidate`). Here the
rewrite gave none, so `f#body` binds no equation, and the walk refused on a
candidate number that was not `f#body`'s.

## Fix (2026-11-15)

The walk counts by the rewrite's rule. Where a candidate is admitted (the
rewrite aliased the scrutinee and the obligation reads its equation),
`f#body` matches with an equation the source lacks; `match_spelled_eqs`
spells each side with its own (both for `f#ext`, the left only for
`f_unfold`), so that refusal is gone.

Probes: `below_bound`, `below_shadowed`, `Counter::scan_below` in
`lib/_tests/std/core/decreases_unfolding_tests.hthr`; `List::sift` and
`List::sift_let` in `lib/_tests/native/runtime/runtime_span_tests.hthr`.

Related: [[runtime-mut-self-let-read-walk]], [[decreases-no-companions-nested-match-calls]].
