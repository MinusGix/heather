---
title: A classified bitvector fold computes its whole word where the structural chain computed one forced bit
status: open
labels: [kernel,evaluator,performance,bitvec,design]
area: kernel
created: 2026-09-13
updated: 2026-09-13
---

Filed from K1 round 3 (docs/native-bitvector-values-design.md §13, 2026-09-13). A classified width fold (`eval/transduce.rs`) packs its arguments and produces all `width` bits at once; the structural cons-chain it replaces produced only the bits its consumer forced. On the reused_callee certificate the `read_literal` family (32 items) went 0.682 → 1.398 s for exactly this reason: its consumer is a memory walk whose address comparison short-circuits at the first differing bit, so the structural path forced one bit and the native path packed two 64-bit literal arguments. It is the whole of that round's +0.28 % gap; every other family fell.

A `BitRun` is its whole width by construction, so the producer cannot be made lazier as it stands. The question this leaves open is a design one: at what width, or under what demand, should a classified fold fire? Candidates, none taken (the round's bar forbade tuning): fire only when every peeled argument is already a word (a literal that is not yet packed stays structural); fire in fixed chunks with a run tail; let the consumer's projection depth drive packing. Decide it against a workload whose consumers are demand-driven, not against this certificate alone.

Related: [[kernel-native-bitvector-values]] (the line), [[bitvector-literal-entry-cost]] (the same literals, packed per use).

## Log

- 2026-09-13: 2026-09-13, after K1 round 4: the 'fire only when every peeled argument is already a word' candidate is still not a real discriminator — nothing produces a word at entry (the Nat-state ofNat arm was refused on cost, docs/bitvector-literal-entry-design.md §10.7), so that rule would still switch the class off almost everywhere. read_literal after the ofNat respelling: 1.215 → 1.105 s; the family's inputs are now cheaper structural chains, and the firing half of this issue is unchanged.
