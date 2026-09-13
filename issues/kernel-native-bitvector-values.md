---
title: Native closed-bitvector values in the evaluator, with an adequacy argument
status: open
labels: [kernel,evaluator,representation,bitvec,performance,design]
created: 2026-09-12
updated: 2026-09-13
---

Filed from the 2026-09-12 certificate-wide attribution ([[function-ir-x86-proof-scaling]] log): 15.7 s of the reused_callee certificate's 41.8 s kernel time is the Id/Id bucket, and its unit is one closed width-64 bitvector operation costing ~250 evaluator steps per bit (`is_zero_bits(64, bxor(64, a, b))` 16.8 k steps / 38 ms; `bitvec::add` 30.1 k / 54 ms). Every memory read walks the stack-write chain with one such compare per link, so the cost is multiplicative in chain length and appears everywhere machine words are computed at closed values, not only in this certificate.

The lever is a representation change of the [[kernel-acceleration-policy]]'s preferred kind, the [[succinct-inductive-values]] runs precedent: a `Val` constructor holding a closed bitvector of width ≤ 64 (or 128) as a machine word, generic over the type (whatever `BitVec n` is spelled as in the library — the adequacy argument must say which canonical form it stands for), with the primitive fold/eliminator on that value computing natively and falling back to the structural form on any open or over-width argument. Adequacy: values mean the same, reduction unchanged up to bisimulation; written down in `crates/kernel/DESIGN.md` before the code, as runs were. No definition-shape matching: the accelerated operations are the eliminator applied to a native value, not `bxor` by name.

Questions the design round must answer before code:

- Which library spelling of bitvectors is the one the value stands for (bit-list Wf, Σ-encoded, or the packed literal of [[bitvec-ofnat-large-literals]]), and how a literal enters native form (construction from a constructor chain of bits at δ, as run saturation does for `su`).
- Which eliminator applications compute natively: the structural fold with a run-endomorphism algebra (the run generalization already proposed for `elim_Nat`) covers head/tail traversals; xor/and/add need the two-argument fold to be recognized as an algebra, not as a named definition.
- How the native value survives the differential oracle against the syntax domain (runs have `nat_run` bisimulation tests; the same shape here).
- Ordering against [[kernel-arena-terms-frozen-prefix]]: a `Val` constructor is value-domain and orthogonal to term indexing, so it should survive that rewrite, but it is one more variant that rewrite must carry — decide which lands first.

Alternatives that do not need this: (K2) fewer compares per read on the library/generator side — a word-granular exclusion lemma so a read skips an 8-byte write in one compare instead of eight, and a contract route that does not compare two whole memories (read_literal_28_* compares state_28.memory with state_18.memory, 188 k steps vs 15 k). K2 is a spelling fix worth doing on its own merits and does not compete with this issue.

## Log

- 2026-09-12: Repriced by the K2 design pass (2026-09-12): on the reused_callee certificate the closed compares in the read chain are 0.7 ms each (addresses differ in their low bits, so is_zero_bits settles early) and the Id/Id bucket's big items were file-list walks ([[call-memory-read-file-walk]]), not compares. What is genuinely this issue's shape there is byte_page + byte_wrap: 298 closed 48/64-bit compares proved by refl, 4.1 s of kernel, each at a different address so no re-spelling applies. Size the payoff from those rows, not from the earlier 15.7 s figure.
- 2026-09-13: 2026-09-13 repriced again after the type-code quote fix (function-ir-x86-proof-scaling log): the closed-refl families of the reused_callee certificate are 8.4 s of a 27.8 s kernel gate (30%), 630 items at 13–44 ms each — byte_page 167 × 13 ms (48-bit window test), byte_wrap 131 × 16 ms (64-bit carry), stack_allowed 36 × 44 ms (eight 52-bit page tests), store_offset 48 × 19 ms (64-bit add), write_literal 48 × 13 ms, read_address 32 × 16 ms. That is the payoff to size this issue from: each such item is one closed machine-word operation the native value would settle in a handful of steps.
