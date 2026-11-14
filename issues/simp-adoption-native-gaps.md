---
title: What simp lacked on the native proof chains
status: open
labels: [tactics,simp,native]
area: tactics
created: 2026-11-12
updated: 2026-11-14
---

The simp adoption round (2026-11-12, Minus chose it over more features)
converted chains in `lib/native/runtime/rt_loop.hthr` to `simp_only`:
`Tm::moves_to_words` (frame lemma, `set_here`, the induction hypothesis
and `words_agree` in one call, its premise discharged from a local),
`Tm::lower_leaf_sound`'s `at_n0` (`set_other`, the frame lemma and
`set_here`, unapplied, premises from locals) and
`Tm::lower_again_sound`'s `moved`. Fixed on the way: a computed
constructor's fields (a `sup_f`'s label payload) were not contracted, so
the computed goal was unspellable; and a definition named among the laws
is now unfolded (docs/simp-design.md §14). Naming a matched (non-recursive)
arm's children by their patterns as well was tried and reverted: it
changed what `omega` read in `CReal::archimedean`.

What stopped a whole proof from being one call, and what became of it:

1. ~~**A definition whose body is a match on a non-constructor**~~ (fixed
   2026-11-12, second pass): such a body unfolds when its scrutinee spells,
   the laws rewrite the scrutinee, and the match selects its arm; a
   comparison of two closed words computes. `Tm::lower_leaf_sound`'s and
   `Tm::lower_again_sound`'s final chains are one call each.
2. ~~**Fields of a literal constructor as raw projections**~~ (fixed): a
   matched arm that does not spell is contracted to the fields written.
3. ~~**Arm goals spelling a pattern's child raw**~~ (fixed): the display
   reads a projection the child's `nth` alias computes to as the pattern's
   name.
4. Papercut: `let x: a ≠ b = …` is a parse error (`expected =, found Ne`);
   `let x: (a ≠ b) = …` works.

A default set for `Valuation` (`Valuation()` is a function returning a type,
so `name_of` may not key it) is not tried yet.


Second pass (2026-11-12): also converted `Fun::fuel_zero_sound`,
`Fun::meas_zero_sound` and `Fun::meas_pass_sound` (whole final chains) and
`Fun::fuel_pass_sound`'s four Valuation lets (side conditions by
`discharge := omega(…)`), which needed laws inside a stuck match's arms,
β under a function literal, an equation's step chaining as `=` at any
carrier, and `Tm::leave_pointwise` (docs/simp-design.md §14.1).

Still open:

5. **A law whose left side has a variable head** (`left: (v) →
   finish(LoopEnd(words_of(v, ns), False)) = …`) is not matched where it
   sits in a match's arm; the proof passes it applied (`left(pv2)`).
6. **A side condition from list membership** (`id ≠ n` from `Mem(id, ns)`
   and `absent(n, ns)`, as `words_agree`'s pointwise premise needs) has no
   discharger, so `nexts_same`-style lets stay hand chains.
7. **`Fun::fuel_pass_sound`'s final chain** stays: the pass's `Sub` node's
   value computes through width casts that the proof's own `pred` does not
   have, so the computed valuation is not the proof's `pv1`.

Not tried yet: the rest of the Valuation sites (`native_structured_meaning`,
`native_compile_nodes`, `rt_lower`, `function_ir_pass`).

## The stream proofs (2026-11-14)

The second adoption round converted the chains of
`lib/native/crypto/sha256_stream_agreement.hthr` (546 → 443 lines, a
quarter fewer bytes; the restated `pushed`/`padded` helpers are gone) and
of `lib/std/crypto/sha2_stream.hthr` (473 → 455), and added the per-type
defaults `List::windows`, `Vec::entries`, `BitVec::nat`, `Stored::bytes`,
`Part::fields` and `Valuation::reads`, each with a `simp_check` theorem.
What simp gained on the way is docs/simp-design.md §15.

Still by hand, and why:

8. **`Sha2::pieces` at a successor, in context.** `pieces(size, Succ(k), xs)`
   computes to `Cons(xs.take(size), …)` whose tail does not spell when laws
   about `xs.drop(size)` are in the call, though the same goal alone
   computes cleanly (probes with literal and neutral sizes, under a λ).
   Blocks `Sha2::pieces_prefix`, `Sha2::pieces_add` and
   `Sha2::words_joined`'s `cut` and final step. Suspect: the frozen terms
   of the call's own laws stop the recursion's tail from being named.
9. **A record's function field applied does not compute.**
   `Sha2::sha256().words(bytes)` is a field of a record value that is a λ;
   the read is not taken through to the λ's body, so `Sha2::words_whole`
   and `Sha2::pad_is` keep `cong_fn` over the count.
10. **A hypothesis about a spelling the goal has computed past.**
    `took.said` is about `took.feed.message()`, which the goal has computed
    to `joined(full) ++ tail`; the law's left side is not computed the way
    the goal is, so `Sha256::finish_hash` keeps its `trans`/`cong_fn`.
    Computing a law's left side as the goal is would close it, at the cost
    of laws whose left side is a definition's call (they would unfold).
11. **An unapplied law at a field of a let-bound mutation.**
    `Sha256::put_hash` does not match at `P.hash` in `zeroed_block` (`P`
    is a `let` of `Sha256::put(…).after`); it is passed applied.
12. **A wrapper over a recursion at a successor.** `Sha256::zeroed(s, i,
    Succ(m))` does not compute to its step (the wrapper's body calls the
    recursion at the count); the proof states the step as `refl` and passes
    it as a law.
13. **Arithmetic side conditions.** The default discharger reads the locals;
    every law with an arithmetic premise needs `discharge := omega(…)` with
    the facts listed (`block_put`, `filled_block`, `len_block`).
14. **Law order is the caller's.** In `hash_long`, `List::append_assoc` at
    the list of blocks (`(full ++ [first]) ++ [second]`) fires before
    `List::joined_snoc` unless `joined_snoc` is listed first, and the
    results do not join. A set's check would catch this pair; a call's own
    list is not checked.
15. **A window at a length equal by hypothesis, not by spelling.**
    `close_short`'s `front` passes `56 = head.len()` as a law so
    `take_append_len` meets it. A general `List::take_append`/
    `drop_append` with an arithmetic premise belongs in `list_window`
    (`take_append_le`/`drop_append_le` sit in `native_arena`).
16. **Not tried this round:** `zeroed_block`'s zero arm (a block equal to
    `T` from `take(T.len()) = T` and equal lengths), `block_with_byte`'s
    index arithmetic (`4 * q + r = i`), and `sha2_stream`'s byte and word
    spelling lemmas (`word_of_bytes`, `spelled_update`, `be_bytes_*`),
    which go through `truncate`, `drop_low_byte` and `Nat::shr`, none of
    which `BitVec::nat` holds.

### A default discharger, past tactics

What it would take for a theorem body, or a `found` condition, to be
closed with no tactic written:

- **An arithmetic discharger for side conditions.** `omega` over the
  hypotheses in scope (locals of a comparison or equation type over `Nat`,
  `Int`, `BitVec`'s `toNat`), as the fallback after the locals. The cost is
  the problem: `omega` over closed terms is expensive (proof-patterns), and
  a default set tries each law at each step, so a failing `omega` at every
  blocked law is a cost at every call. It needs a budget (atoms, steps) and
  a memo of side conditions refused within one run.
- **For a theorem body:** a surface for "closed by the defaults", e.g. a
  body left out (`theorem t(…): a = b;`) meaning `by simp()` with that
  discharger. This changes the surface, so it is Minus's decision; the
  recommendation is to keep `{ by simp() }` explicit and make the
  discharger above its default, which needs no syntax.
- **For a `found` condition** (docs on strict conditions): the found-proof
  search tries locals and search rules. Adding `simp` with the type's
  defaults as a last resort is an inference change on a hot path; it would
  need to be limited to an equation or a comparison whose types have a
  default set, budgeted, and measured with `scripts/perf ab`.
- **Shared by all three:** sets resolved once per module rather than per
  call (each `by simp()` resolves every law of every default set it picks),
  and a report that names the set and the side condition that blocked.

None of these was built: the discharger is an elaborator behaviour change
that wants its own measured round, and the other two are surface or
inference changes.

## Log

- 2026-11-12: Three theorems of `lib/native/runtime/rt_loop.hthr` that #577 converted to `simp_only` went back to their written chains when PR #551 merged master: their statements there are over a file (`Fun::GuardedBy`), and the converted proofs are of the statements without one. Converting them again over the new statements is the small piece left here from that merge; the chains are the same shape, with the file as one more fixed argument.
- 2026-11-12: The same on the merge of #582 into PR #551: `Fun::fuel_zero_sound`, `Fun::meas_zero_sound`, `Fun::meas_pass_sound` and the two tail lemmas (`Tm::lower_again_sound`, `Tm::lower_leaf_sound`) were converted on master over the statements without a file, and PR #551's are over one, with the state split into kept and moved words. The merge converted two again over the new statements (`Fun::fuel_zero_sound`, `Fun::meas_zero_sound`): the only change is that the fact about the body's value is restated over `StructuredRegion::eval_over`, the spelling the unfolded pass has, since a law whose left side spells `eval(…, buffers := …)` is not met after `Region::eval` is unfolded. Three keep their written chains: `Tm::lower_again_sound` and `Tm::lower_leaf_sound` (their statements split the state into kept and moved words, so the converted proof is of another shape), and `Fun::meas_pass_sound`, tried and left: with `state_same` and `left` at the split state as laws, the left side reaches the stuck match on the flag, and the right stays at `Tm::leave(eval(…), …, λ x => out(into(…)))`, with `Valuation::set_other`'s side condition reported undischarged against `node_output(Const(64, t.next, 1)).id` (the id spelled through the node, not as `t.next`, so `omega(flag_lt)` does not read it). That last is a gap of its own: a side condition whose term is a closed projection of a literal node is not reduced before the discharger sees it.
- 2026-11-14: The stream proofs round (section above): simp computes calls, conjunctions and field reads that spell, freezes an applied law's terms, matches under λ, records and constructors; six default sets; two modules converted chain by chain.
- 2026-11-14: Minus decided: keep `{ by simp() }` explicit; no body-less theorems closed by default. The default-discharger work, if done, is simp's arithmetic discharger.
