---
title: The layer's cat implements tr_spec(identity)
status: closed
labels: [native,itree,proofs]
area: heather-in-heather
milestone: [hih-pl-source]
created: 2026-10-22
updated: 2026-10-23
---

Round S3.1 (`lib/native/native_source.hthr`) wrote `cat` in the effectful layer and
ran it against a scripted world by evaluation
(`crates/elab/tests/fixtures/native_source_cat.hthr`). The claim users care
about is `Program::Implements(cat(c).denote(), tr_spec(λ b => b))`, for every
capacity `0 < c < 2^63`. It is not proved yet.

## Shape of the proof

cat is two nested `iter`s (read, then write until sent) under one fuel.
`filter_spec` is one `iter` over `FilterAt` (`Reading` or `Writing(pending)`).
The simulation relates:
- cat's state before a read to `Reading(Stateless())`;
- cat inside its write loop, with sent count `from` and read count `n`, to
  `Writing(Stateless(), span(buffer, from, n - from))`.

This needs [[itree-iter-simulation]] generalised to a body that is itself a
loop, or cat's inner loop folded into one `iter` step by a lemma about the
layer's `Repeat`.

The word facts are small but have to be stated. A read count is at most
`c < 2^63`, so it is non-negative as a signed word and its `Equal` to zero is
`n = 0`. An errno is between 1 and 4095, so `errno_word` is signed-negative.
`from + count` stays at most `n`, so the 64-bit `Add`/`Sub` don't wrap. Each
of these should be a lemma about `count_word`/`errno_word`, not an unfolding
at a literal width.

## Log

- 2026-10-22: The single-level loop rule landed ([[itree-iter-simulation]], `lib/std/os/linux/linux_trees_sim.hthr`'s `Program::implements_iter`), so this is no longer blocked on it. What it does not give is a source pass that is several spec passes: cat's write loop. This round's proof needs one of the two routes above (a nested-loop rule, or folding the inner `iter` into the outer body by a lemma about the layer's `Repeat`).
- 2026-10-23: 2026-10-23: DONE. `lib/native/native_cat_spec.hthr` proves `cat_implements` (`Program::Implements(cat(c).denote(), tr_spec(λ b => b))` for `0 < c < 2^63`) and `cat_sends` (stdout is stdin along every valid run exiting 0). Route: simulation up to a continuation (`ITree::SimK`, `simk_iter` with an invariant indexed by the fuel left, `Program::simulates_at`; docs/itrees/itree-simulation-design.md §6–7), so the inner loop is the loop rule again with the rest of the outer pass as its continuation; no nested-loop rule needed. Statement kit for native source proofs: `lib/native/native_source_sim.hthr`. cat moved to `lib/native/native_cat.hthr`. Word facts in `lib/std/bitvec/bitvec_signed.hthr` (sign bit, signed test against zero, negated errno), list facts in list.hthr.
