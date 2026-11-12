---
title: A runtime fn's if h: i < 64 over a word is refused by the generator: Or has no runtime layout
status: closed
labels: [native,runtime-fn,bitvec]
area: heather-in-heather
milestone: nh-front
created: 2026-11-12
updated: 2026-11-12
---

A `runtime fn` whose loop tests a word with the proposition `if h: i < 64` is refused by the generator, while the same loop written `match h: i.unsigned_lt_bit(64)` compiles (2026-11-12):

```heather
runtime fn count_up_if_rt(i, acc: BitVec(64)) → BitVec(64) decreases (64 - i).toNat() {
    if h: i < 64 { count_up_if_rt(i + 1, acc + i) } else { acc }
}
```

> error: `runtime fn count_up_if_rt`: the generator failed: rt: `Or` has no runtime layout under the reflected fragment

The measure discharges now ([[decreases-word-measures-by-hand]]: `bv_omega` reads `h: i < 64`, the literal's `toNat` evaluated), so the refusal is the generator's alone: `if h: p` decides `p` through its `Decide` instance, and the reflector meets the decision (`a.unsigned_lt(b) ∨ ¬a.unsigned_lt(b)`) instead of the bit it is decided by. A plain `fn` of the same shape elaborates and evaluates (`count_up_if` in `lib/_tests/std/tactic/bitvec_omega_tests.hthr`).

## Done when

`count_up_if_rt` above certifies (`agrees`), with a probe beside the `match h:` loops in `lib/_tests/native/runtime/runtime_loop_tests.hthr`, so the loops of `lib/native/crypto` can write their test as `if i < 64`.

## Log

- 2026-11-12: Done (Minus chose the reading): if h: P elaborates as a convoyed match on decide_bit<P>(), with h read from the instance's reflects through bool's decide_true/decide_false, bound only in a branch that names it. count_up_if in runtime_loop_tests certifies. Motive synthesis now abstracts the scrutinee as written beside its stuck spelling (matching::with_scrutinee), so a proof casing a convoy-defined function's own test works; imperative_statements_tests larger_is_right/left and larger_bit_is_right. Limit: a function whose branch uses h cannot be proved about by casing the test, [[if-evidence-proof-by-cases]].
