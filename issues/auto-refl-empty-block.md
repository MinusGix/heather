---
title: Auto-refl MVP: an empty proof block discharges by refl
status: closed
labels: [frontend,elaboration,syntax]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round): the one slice of
[[surface-proof-automation]] that issue marks as independent of the
goal-holes engine. `theorem two_two(): 2 + 2 == 4 {}` passes: in checking
position, an empty block gets ONE speculative `refl` attempt, kept iff the
kernel accepts, else the goal stays open. Conservative reading only (the
empty block is the trigger; `refl` never becomes a silent no-op elsewhere).

Scope here: parser accepts `{}` as a proof block; one checking-position
elaborator hook; tests including the negative control (an empty block on a
non-refl goal reports the open goal, not a panic or a silent pass).

## Design (2026-08-05)

**Surface and AST.** `Block` (crates/syntax/src/ast.rs) requires a result
expression, and a declaration body *is* a `Block`, so `{}` cannot be represented
as "a block with no result" without making every consumer handle `Option`.
Instead the parser fills the empty braces with one synthetic result expression,
`ExprKind::AutoRefl`, spanned at the braces. That keeps every downstream reader
(motive synthesis, `count_holes`, the block's `on` discharges) working
unchanged, and it makes the trigger *syntactic and one node wide*, which is what
"conservative reading" means here: `refl` itself is untouched, and no other
position grows a default.

**The one hook, in checking position.** `AutoRefl` gets an arm in
`elab_check_hinted`: `whnf` the expected type; if it is an `Id`, build
`Term::Refl` from its left endpoint and ask the kernel *now* whether the two
endpoints are convertible (`conv::conv_term` at `Layer::Prog`, against
`goal_psi()` so a statement mentioning an outstanding goal is still well-scoped).
Kept iff that succeeds. This is a real kernel gate rather than a deferred one:
the decl-final `check_term` would also catch a bad guess, but it would report a
`Kernel` error about a term nobody wrote, which is the worst diagnostic in the
system.

**Failure is an open goal, not an error.** Any other outcome — the expected type
is not an equation, or the endpoints do not converge — falls through to
`new_goal`, i.e. exactly what `?` does. So the message is [[goal-holes]]'
unfilled-goal listing, with the goal's statement and context printed, and an
`on` in the same block can even discharge it. Two consequences worth stating:
`count_holes` must count `AutoRefl` (the pre-count is documented as an upper
bound, so counting one that turns out to be refl-discharged is free), and in
*inference* position `AutoRefl` is an error naming the rule, since there is no
goal to close and no type to guess — which is the "ignored for values" property
falling out rather than being enforced.

**Failure modes and negative controls.**
- Empty block on a non-equation goal (`fn f() -> Nat {}`): open goal listing,
  not a panic and not a pass. Negative control.
- Empty block on a *false* equation (`2 + 2 == 5`): open goal listing. The
  speculative `Refl` is discarded before it can reach the kernel's decl-final
  check, so the error names the goal, not a `TypeError`.
- Empty block on an equation between open terms that are convertible anyway
  (`(n: Nat): add(n, 0) = n {}` — `add` recurses on its second argument, so this
  one is definitional): accepted. This is the *open-term* axis of
  docs/testing-generated-terms.md and the reason the check is a conversion call
  rather than a syntactic equality.
- The trigger must not fire for a block that has statements but no result
  (`{ let x = 1; }`) — that stays a parse error, since `{}` is the whole
  trigger.
- Speculation must never be silent when it succeeds *wrongly*: it cannot, since
  what it emits is `Refl` at a type the kernel just accepted.

## What it assumes from elsewhere
- **[[surface-proof-automation]]** owns the design (conservative-vs-aggressive
  decision, the future solver slot, `apply`). Assumed here: only the MVP
  mechanism as specified there — nothing about `apply` or multi-goal defer.

## Log

- 2026-08-05: LANDED, as designed above. Parser fills empty braces with one synthetic result node, ExprKind::AutoRefl (crates/syntax/src/ast.rs, block_body in parser.rs), read *before* the statement loop so the trigger is exactly `{}` and `{ let x = 1; }` stays the resultless-block parse error. One checking-position arm in elab_check_hinted: whnf the expected type, and if it is an Id, run conv::conv_term on its two endpoints against goal_psi() at Layer::Prog — kept iff that succeeds, otherwise new_goal, i.e. the same object `?` raises. count_holes counts AutoRefl (the pre-count is documented as an upper bound, so a slot reserved for a speculation that succeeded is free). Inference position is an error naming the rule. Tests: crates/elab/tests/auto_refl.rs, 10 tests. Positives: a closed computation; an OPEN definitional equation (add(n,0)=n, since add recurses on its second argument) — the axis that says the gate is a conversion and not a numeral comparison; an annotated let and an @-call argument; a match arm under a motive. Negatives: a false equation and a true-but-not-definitional one (add(0,n)=n) both leave the goal open with the goal listing, not a kernel error; a value goal leaves it open too (this is 'ignored for values' falling out); an undischarged speculation is a real goal an `on` closes; `refl` itself is NOT made tolerant. TWO NOTES FOR REVIEW. (a) `{}` in an ordinary argument position of an implicit-taking callee does not work — sym({}) fails — because such an argument is elaborated in inference mode until every meta its domain mentions is solved. That is pre-existing and shared with `refl` and `?`, not new here, but it does limit where the feature fires. (b) One existing test changed meaning: let_and_blocks.rs's rejection (e) asserted that an empty block has no result expression. It is still a rejection — the goal is listed — but with a different message; the test now asserts the goal listing, and a second case pins that a block with statements and no result is still the parse error.
