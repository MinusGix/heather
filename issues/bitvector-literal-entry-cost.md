---
title: A bitvector literal is born structural and packed on every use: the remaining floor under closed machine-word items
status: open
labels: [kernel,elaboration,representation,performance,bitvec]
created: 2026-09-13
updated: 2026-09-13
---

Filed from K1 round 3 (docs/native-bitvector-values-design.md §2, §13, 2026-09-13). With the transducer class in, a closed width-64 operation on literals still costs thousands of evaluator steps, and the unmoved part is the literal: probe A3 (`from_bits(64, L).bits = L`, no operation) is 3 481 steps before and after the whole line, and `bxor` on two literals against a literal answer (A1, 8 742 steps after) is three such literals plus a fold that now costs a few hundred. A `[Bool; n]` literal is elaborated as a chain of `n` `Term::Pair`s of `Inl`/`Inr` over tag nests, is checked component by component, and is packed into a word by `pack_bit_prefix`/`pack_word` — a forced walk of `n` pairs at ~20 steps per bit — at every conversion and every fold that consumes it (the packed word is not memoized on the value: the term cache makes the walk evaluation-free but not step-free). `ofNat` is `Opaque` (a `List` fold, the inverse direction) and is what the x86 model's literals actually go through.

The lever is at entry, not in the evaluator: a literal should be born a word. Candidates: a packed vector-literal term (the elaborator already emits packed literal *lengths*, 2228869) that the evaluator reads straight into a `BitRun` and the kernel's typing rule checks in O(1) per bit against the `Vec` type; or an `ofNat` whose reduction over a closed argument is recognized by the same probe method (a fold on a run producing a word, arity 0 peeled). The first is a trusted-base change at the term level and wants its own adequacy note beside `crates/kernel/DESIGN.md`'s native-bitvector paragraph; the second is the `bitvec-ofnat-large-literals` shape revisited. Size the payoff from the x86 line's literal traffic (every immediate, every address), not from the certificate's refl families.

Related: [[kernel-native-bitvector-values]], [[bitvector-fold-eagerness-at-demand-driven-consumers]], [[bitvec-ofnat-large-literals]] (closed).
