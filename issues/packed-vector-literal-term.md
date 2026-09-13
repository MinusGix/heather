---
title: A packed vector-literal term: designed and deferred behind a customer
status: open
labels: [kernel,elaboration,representation,bitvec,design]
created: 2026-09-13
updated: 2026-09-13
---

Designed in docs/bitvector-literal-entry-design.md §3 (K1 round 4 design pass, 2026-09-13) and deferred by its §5.2: a term the elaborator emits for a closed `[Bool; n]` literal that the evaluator reads straight into a `Val::BitRun`, with an O(1)-per-bit typing rule against the `Vec` type — about 250 lines across elab, the kernel's typing and evaluator entry, quoting, and the oracle, with the adequacy clause drafted in that doc's §6 and the tests laid out on the four axes of docs/testing-generated-terms.md (§3.5; the open-element-type item comes first, §8.6). It removes the largest floor in the *probe* table (a written-out width-64 literal costs ~3.6 ms of gate and 3.3k steps; the same value born packed is 47 µs and 0 steps, probe P5) but has **no customer**: `lib/` contains zero `[Bool; n]` literals and 281 `ofNat` sites, the reflector cannot emit one, and `function_ir_source.rs:320` requires constants to be `bitvec::ofNat(64, literal)`. Landing it as a performance change would measure flat on the certificate, which is round 2's mistake.

Triggers, either of which reopens it for implementation: a hand-written `[Bool; n]` literal on a measured path, or round 3's `BitRun`↔`Pair` oracle arm wanted reachable from the generator (§3.4 — today it is not). Check `size_of::<Term>()` before and after; box the payload rather than widen every term (§8.5).

Related: [[bitvector-literal-entry-cost]] (the round it came from), [[kernel-native-bitvector-values]] (the line), [[bitvec-ofnat-large-literals]] (closed).
