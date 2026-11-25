---
title: A function's promise has a precondition and no postcondition
status: closed
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`lib/lang/ownership/call_check.hthr`'s `FnSafe(sig, pre, mean, run)` lets a callee assume `pre` of its words, and promises only that its run agrees with its meaning ([[ownership-checker-call-and-write-view]], log of 2026-11-25). It says nothing about *what* the meaning answers. So a caller whose residual depends on a callee's answer cannot discharge it: `Checks.discharge` is quantified over every world, and nothing ties the world's answer to a fact.

The case that will meet it first: a callee answers an index or a window it found, and the caller writes there beside a view it holds. The residual `Apart(…, Var(z), …)` reads the word `z` the call bound; proving it needs the callee's promise that `z` is, say, past the view.

## Shape of the fix

A postcondition beside the precondition, as a proof parameter of the kernel type (§15.8: "residual preconditions are not extra data"): `post(ws, answer)`, which the callee proves of its meaning and the caller assumes at the call. The world's meaning stays abstract; `FnSafe` gains `post(ws, mo)`. The checker's data does not change: a residual reads the word the call bound, and its proof is the caller's, from the callee's `post`.

## Done when

A caller with a residual over a callee's answer is accepted, its residual discharged from the callee's postcondition and nothing else of it, with a `¬` control where the postcondition is dropped.

## Log

- 2026-11-25: Done, in `lib/lang/ownership/call_check.hthr` as item 4 of [[ownership-checker-loans-and-joins]]. `FnSafe(sig, pre, post, mean, run)`: `post: List<Nat> → Nat → Type`, of the call's words and its answer; `Safe` has `posted: post(mo.word)`. The checker's data is unchanged: a residual over a word a call bound is the ordinary `Due(Spans(…, Var(z), …))`. Its proof is the caller's, under `Posted(w, sigs, pres, posts, body)`: every function the body calls answers what its postcondition says wherever its precondition holds, which `check_sound` derives from the callees' `FnSafe` (`fn_safe_answers`: lend the callee a file holding only the argument). `check_sound` takes the residuals' discharge and the function's own `post_ok` under `Posted`; `Checks` has both fields; `prog_sound` takes `IdleOk` (the depth-zero answer, 0, meets every postcondition).

  The program: `ident(w, k)` answers `k` with postcondition `z = ws[0]`; `after_call` (`let t = &x[0..k]; let w = &mut x[k..k+m]; let z = ident(w, k); dead(w); x[z] := 5; t[0]`): `after_checked` (the residual `Spans(0, k, z, 1)` over the call's word), `after_owed` (discharged from `Posted` at `ident` and the prefix of the words: word 2 is the call's answer), `ident_safe`/`after_safe` (any world, citing only `ident`'s `FnSafe`), `after_sound` (every depth from two), `after_runs`/`after_means`. Control: `zero` answers 0 and is checked (`zero_checked`), so it keeps every part of a promise but `ident`'s postcondition (`zero_breaks_post`), and with it the residual fails (`after_without_post`) and the runs differ, 5 against 3 (`after_without_post_control`).

  One limit, recorded in §15.6: `prog_sound`'s depth-zero world answers 0, so a postcondition 0 does not meet (as `ident`'s) needs the depths composed from `check_sound` by hand (`after_sound`), and a recursive program with such a postcondition needs the termination the meaning assumes, which a world by depth does not state. Not filed: it belongs to whatever replaces the toy's world with the real meaning.
