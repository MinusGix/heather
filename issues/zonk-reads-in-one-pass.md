---
title: Zonk walks every term twice and compares: decide "still blocked" in one pass
status: open
labels: [elaborator,kernel,performance]
area: language
created: 2026-11-09
updated: 2026-11-10
---

The elaborator decides "does this term still mention an unsolved slot" by
substituting the slots away **twice**, with two different placeholders for
the unsolved ones, and comparing the two results structurally
(`unification::zonked`/`zonked_tm`, `host.rs`'s `committed_ty`/`committed_tm`
and `cx`, `goals.rs`, `lib.rs`'s goal lift, `rewrite.rs`'s `instantiate`,
`strengthen_ty`/`strengthen_tm` for the local namespace). The device is
exact and cannot drift from the syntax, which is why it spread. It costs two
full `apply_global` walks, two copies, and an equality walk, on every call,
solved or not.

After [[empty-substitution-tail-decoration]], `zonked_tm` and `zonked`
together are the largest single caller of global substitution on a cold
`calc_parser` check (stack samples, Log).

## Tried (2026-11-09): the kernel reports which entries it read

`Type::apply_global_reading(σ, read)` / `Term::…`: the same traversal, with
`read[k]` set when `σ.entries[k]` is substituted for an occurrence (one
`Option<&mut [bool]>` on `SubstGlobal`, set in `resolve`). The elaborator
makes the first pass with it; when no unsolved slot's entry was read, no
placeholder is anywhere in the result and the second pass would build the
same term, so it returns. Only when an unsolved entry *was* read does it run
the second placeholder and compare, which keeps the test exactly the old one
(an occurrence can be read and then discarded inside a local substitution
its payload ignores; the old test does not block on that, and neither does
this).

Result, cold width-one `calc_parser`, three interleaved samples
(`scripts/perf ab`): 41 counters identical (no behaviour change),
`syntax_eq_nodes` -7.6%, `subst_memo_hits` -11%, wall inside the sample
spread. **Not landed**: the solved case was the cheaper half. The calls that
cost are the ones that answer "still blocked", and those still pay both
walks.

## What would pay

- **Make "blocked" the one-pass answer.** That needs the read to be exact:
  distinguish a placeholder that survives into the result from one that is
  discarded. A flag on the mapper while it is inside the local substitution
  of a payload-bound occurrence would do it, at the price of a second
  semantics to trust in the one-pass path. Measure how often a discarded
  read happens at all first (a counter in the fallback); if never, the test
  can be redefined as syntactic mention, which is what its doc comments
  already claim it is.
- **Or remove the question**: under [[psi-references-by-level]] the slots
  are the levels past Ψ's last, and "mentions an unsolved slot" is a bound
  read off the root.

The patch is ~80 lines (`crates/kernel/src/subst.rs`, `unification.rs`,
`host.rs`).

## Log

- 2026-11-09: Stack samples as in [[psi-references-by-level]]'s log: `zonked_tm` and `zonked` are 28 of the 37 samples whose stack shows `apply_global`. A/B of the read-tracking patch (`scripts/perf ab`, before = branch with the allocator, after = plus the patch, cold width-one `calc_parser`, three interleaved samples): wall 31.6/34.7/34.3 s to 33.4/33.1/32.8 s (spread exceeds the delta), `syntax_eq_nodes` 17,725,681 to 16,380,793, `syntax_eq_memo_hits` 862,665 to 839,494, `subst_memo_hits` 24.77 M to 21.98 M, 41 other counters identical.
- 2026-11-10: [[psi-references-by-level]] was built as constants plus index variables, not levels, and with it a per-node memo of the largest free global variable (`subst::global_var_bound_tm`, `bounds.rs` §The global namespace). The third option above is now available in that form: a scratch world's slots are the variables, so "mentions an unsolved slot" is bounded by a read off the root, and both `apply_global` calls already skip every subtree with no free variable. Re-size before working on this: on the cold showcase `subst_memo_hits` fell 24.8 M → 4.2 M and `syntax_eq_nodes` 17.7 M → 7.1 M with that change alone, so the 2026-11-09 numbers here no longer describe the cost.
