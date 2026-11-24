---
title: Rebuild while and for on the one loop combinator, and the native loops on one node
status: open
labels: [loops, elaborator, native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-19
updated: 2026-11-24
---

Design: `docs/language/loop-combinator-design.md`. Rounds 1 and 2 (the
combinator `lib/std/core/loop.hthr`, `Loop::rule`, `Loop::unique`; `while`
outside a `runtime fn` on it) are built, and round 3's stages 3a to 3d (one
loop node in the runtime terms and one over a span; several words, a span
only read, a join in a pass, §6.4). Left, each a PR for Minus (§8):

3. The rest of round 3 (§6.5): a user's tail recursion on the node (the
   fork there, recommended: the elaborator writes it as the loop), loops
   with an `invariant` and loops whose locals are not all words; then
   `Tm::lower_tail`, `Fun::Guarded` and the companions go.
4. `rt_held_loop`, `rt_bytes_loop` and `rt_io_loop` onto it (the readers'
   `FFun::reads_guarded` and `reads_guarded_over` with them).
5. The port ledger's remaining loop rows (`break`/`return` in a `for`).

## What it assumes from elsewhere
- **[[span-caller-of-fact-taking-loop]]** owns the refused caller of a loop
  with facts. Assumed here: only that passing the facts in the initial
  state retires it once round 3 lands.

## Log
- 2026-11-19: round 1 built; the binary search's theorem re-proved by
  `Loop::rule` at about the example's length (the cost check the design
  asked for).
- 2026-11-19: round 2's `while` built: outside a `runtime fn` it is
  `Loop(…).run` over `f::State` with `f::step`; the whole library passes.
  A `mut self` method's loops and a counted `for` are still lifted (next).
- 2026-11-24: 2026-11-24: a `while` whose measure is assigned through an `if` is refused though every arm decreases it ([[while-decrease-through-branches]]): the search does not split the branch. Found by the hash table rows of the ledger (docs/native/rung2-spans-design.md §2).
- 2026-11-24: [[while-decrease-through-branches]] is fixed: the decreases closer splits a stuck if in the obligation and searches each arm, so a while whose measure is assigned through an if is accepted.
- 2026-11-24: stage 3d built (docs/language/loop-combinator-design.md §6.4): a span loop's state of several words is a record the span's program holds (only a loop's minted `f#State`; other records beside a span keep their refusals), a loop that only reads its `mut self` span carries it unchanged, the test's fact reaches a body of several words, and a statement `if` that joins inside a pass has the rest of the pass written into each arm. The ledger's `Bytes::port_set_put` and `Bytes::port_count_clear_word` compile with runs by `refl`. §6.5 writes the fork for a user's tail recursion on the node (recommended: the elaborator writes it as the loop, as a `while`), for Minus.
- 2026-11-24: 2026-11-24: §6.5's fork decided by Minus: the pin is always the function's unfolding equation, pointwise (Setup::Pinned the only pin, by refl where the body is the reflection's meaning and by uniqueness of a well-founded fixpoint where f recurses), f is what the user wrote, and tail-call elimination is a lowering. Stages 3e–3h in the design note.
- 2026-11-24: stages 3e and 3f built (docs/language/loop-combinator-design.md §6.6), on Minus's decision in §6.5. 3e: `Setup::Pinned` is the one pin of the plain and own-callee routes, `FFun::Pinned` the span and `Bytes(n)` routes'; laid records and `Io` were already pointwise. One congruence per statement form (`Ty::answers_words_alike`, `FTm::answers_alike`), none per function. 3f: `fixpoint_unique` in `loop.hthr`, `Loop::unique` its case. Next is 3g, whose shape question (an enum state on `Iterate`, or a node with `Again`/`Done` leaves) §6.6 writes down.
- 2026-11-24: 3g built (docs/language/loop-combinator-design.md §6.7 findings, §6.8 as built); Minus accepted §6.7's amendment (lower_tail/tail_sound stay as the node's pass; 3h deletes tail mode as a function's mode). The node: Tm::Loop(inits, body) with Again(res, args) leaves, its body seeing only its state; its meaning through Tm::sem_in, a term under its innermost loop's label (the meaning cannot call tail_sem), and Loop::rounds, the fuel recursion, with one more pass when the passes run out (an answering loop cannot answer the state). One lowering for a value and a pass (Tm::lower_in), proved by one induction (Tm::lower_in_sound); the node's region is a FunctionIR loop and a one-pass loop for the extra pass (Tm::loop_sound), proved by induction over the passes. The pin lemma is Loop::rounds_agree, the fuel side of fixpoint_unique. A measured recursion lent nothing, of 64-bit words, calling itself only last, now compiles as the node (Fun::as_node, runtime_node_instance), its pin from f::ext and f::irrel through Setup::node_means; count_down and friends compile, triangle to certified x86. Finding: the ledger's tail calls are on the span and laid-record routes (round 4), not Tm. Two conversion traps recorded in §6.8 (comparing two loop meanings, and a cast of one against the meaning).
