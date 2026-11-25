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
- 2026-11-24: Minus's answers to the 3g report. (1) The node goes into `FTm` (round 4) before 3h. (2) The pass budget is a proof, not code (`docs/compilation-vision.md` principle 13). Checked where the counter lives: in the code all the way down, in FunctionIR's `Loop` (bound, count and exhausted ports), the allocator's count test and decrement, and the x86 proofs through the total evaluator. The extra pass cannot go while the counter stays, because a u64 measure can need `2^64` passes. The change is planned in design §6.9 (a relational loop meaning, termination as a hypothesis, the counted loop as a helper), several rounds; its order against 3h and round 4 was asked of Minus. (3) A pass that answers several words is built: `Ty::Answer`, `Tm::leaves`, the extra pass reading the state back with `Ty::read_words`. The loop's exit still moves one word until (2). `while` onto the node (its state spelled as words, its pin a rewrite inside f's body) is written in §6.9. (4) The rule against reducing a node's meaning past its head is in `docs/proof-patterns.md` §4. Merged the session branch `ccr-a42b8144-7er7yg` (multi-word span results, the arena, proof tooling).
- 2026-11-24: stopped before `while` onto the node. Its record answer needs the multi-word exit in the exhaustion branch, and its pin is off by one (the node with the extra pass is `Loop::steps(N + 1)`), both shaped around the branch (2) deletes. Minus chose to change the primitive first: rounds A (FunctionIR `Loop` relational, evaluator, passes, counted users on a helper), B (native structured layer, termination a hypothesis), C (allocator, emitter, decoder, producers, linked), D (the node without its extra pass, then `while`, the `FTm` node, 3h). Design §6.9.
- 2026-11-24: round A built (design §6.9). `Until`, FunctionIR's loop with no bound, stands beside the counted `Loop`. Its meaning is a relation that ends only by its exit; its evaluator's fuel is the meaning's (`2^64`), not the code's. Running out is not defined, so termination rides `defined_over` as the soundness theorems' hypothesis, and `until_defined_of_measure` discharges it once from a decreasing measure. Every FunctionIR module and pass has its case; the native layers refuse it until round B; its producers move in round C. One probe at the kernel's budget (`uneven_shallow_exits`) is now stage theorems.
- 2026-11-25: round B built (design §6.9): `Until` emits on the function path and the statement path with machine proofs and no counter. A statement holding one stayed refused for want of a termination argument. Minus decided: every loop carries its measure (the FunctionIR `Until` at both levels and the node `Tm::Loop`), its decrease proved where the loop is built, so definedness is generic and no theorem gains a hypothesis; the counted loop becomes a helper whose counter is its measure.
- 2026-11-25: round C begun (design §6.9 "Round C as built so far"). `Until` carries its measure (a seventh field). `function_ir_counted` decides a counted pass by evaluation and proves its ending (`counts_halts`), so statements take a counted `Until` with no hypothesis anywhere. Round B's statement code had a backward `Jcc`, which never lays out; it was hidden behind `scopes`' refusal and is now laid out as the counted loop's. `native_build`'s `Passes` is a counted `Until`. Next: the runtime producers, by rebuilding `Loop` as a derived form over `Until` (the plan is in §6.9).
- 2026-11-25: C3 held for a decision. Every runtime producer of `Loop` (Iterate, the node, rt_loop's fuel and measured loops, the measured FFun path, FTm::Loop) is replaced or deleted in round D, so porting them in round C builds them twice. Proposed: close round C as built, have round D's node lower straight to a measure-carrying `Until`, and delete `Loop` with the allocator's counter pieces after 3h. §6.9 also records the limit that a measure is a parameter position.
- 2026-11-25: Minus approved the order: round C closed as built (9720631); round D next (the node carries its measure and lowers to a measure-carrying `Until`, then `while`, the FTm node, 3h); `Loop` and its allocator pieces are deleted after 3h.
