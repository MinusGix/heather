---
title: "`cases h` stops at a recursive stage, keeps a refuted `guard` case, and cannot be used in a recursion's arm"
status: closed
thread: Make compiler correctness proofs elegant
labels: [tactics,elaborator,matching,proofs]
area: tactics
milestone: [lang-proof-modularity]
created: 2026-11-17
updated: 2026-11-17
---

`Stmt::emits_runs` in `lib/native/native_compile_correct.hthr` inverts
`emitted: s.emits(…) = Some(c)` by hand in each arm of its `match s`: a tower
of `match fit: … { False => λ none => absurd(none), True => (match y_is: … `
for `Branch` and `Repeat`, and written `as λ` motives for `Arg` and
`Perform`. Each arm is what [[cases-on-hypothesis-tactic]] is for. Trying
`cases emitted as …;` in all five found one arm it reads (`Exit`) and four
it does not. The attempt, as one lemma per kind of statement, is
`/mnt/project-files/compile-proofs/emits_runs_arms_by_cases_attempt.hthr`
(`Target::branch_runs`, `repeat_runs`, `exit_runs`, `arg_runs`,
`perform_runs`).

1. **Not in a structural recursion's arm.** In `emits_runs` itself, in the
   `Branch(condition, yes, no)` arm, `cases emitted` is refused: "`emitted`
   is not stuck on any test of the call it states". The same hypothesis as a
   parameter of a lemma outside the recursion is read (`Target::exit_runs`
   checks). The hand proof's `match fit: layout.word_fits(condition)` in the
   same arm does find the test. A `λ`-bound `emitted` whose type came from
   unfolding `t.EmitsRun(Exit(status), call, perform)` is refused the same
   way, outside any recursion.
2. **A recursive stage ends the inversion silently.** `Target::branch_runs`,
   `emitted: Branch(condition, yes, no).emits(…) = Some(c)`, `cases emitted
   as fit, y_is(y), n_is(nc);`: `fit` is taken, and then `emitted` reads
   `match app@(…elimWf…) { None => None, Some(v) => match app@(…) { … } } =
   Some(c)`: the recursive calls `yes.emits(…)` and `no.emits(…)` are the
   eliminator's applications, not calls, and no further split is taken. The
   names `y_is(y)` and `n_is(nc)` are dropped without a word, so the refusal
   is `unbound name else_label` at the first use of `y`. `Repeat` the same.
   Wanted: the recursive call spelled as the call (as `induct`'s cases have
   it, `docs/tactics/functional-induction-design.md` §1.1), and a refusal
   at the `cases` when names are left over.
3. **A refuted `guard` case survives.** `Target::perform_runs`, `emitted:
   Perform(index, args, results).emits(…) = Some(c)` where `emits` is
   `layout.call_fits(…).guard(Some(…))`: after `cases emitted as fit;` the
   rest of the block is checked with `fit: call_fits(…) = False` and
   `emitted` as written, unrefined. The `False` case should have closed by
   `absurd`.
4. **A stage that is another function's call is refused.**
   `Target::arg_runs`, `emits` is `p.arg(layout, out, index, buf, len,
   names)` whose body tests `layout.words_fit([index, len])` and then
   `layout.capacities.nth(buf)`: "the split on the test `emitted` is stuck
   on did not refine `emitted` (a hypothesis passed beside the split's
   equation in one call is kept as written)", though the block passes
   `emitted` nowhere.

## Done when

`Stmt::emits_runs`'s `Branch`, `Repeat`, `Exit`, `Arg` and `Perform` arms
are each one `cases emitted as …;` and the arm's proof, in place.

## Log

- 2026-11-17: filed from the adoption round after PR #753.

## Log

- 2026-11-17 (thread "Refine hypotheses through calls in case splits"): fixed by `cases` splitting `Π(h). goal` itself with the blocker search's motive and applying the split to `h` (docs/tactics/goal-combinators.md, `cases h`). (1) A λ-bound `h` whose type comes from unfolding `EmitsRun` is decoded to its equation first, and recursion arms work. (2) In each case `h` is the reduct the test was found in, so `yes.emits(…)` reads as the call and is split and named. (3) and (4) came from the motive-less match's §4.7 reading and passed-beside rule, which `cases` no longer goes through. `Stmt::emits_runs`' Branch, Repeat, Exit, Arg and Perform arms are `cases emitted as …;`, and `/mnt/project-files/compile-proofs/emits_runs_arms_by_cases_attempt.hthr` checks clean.

