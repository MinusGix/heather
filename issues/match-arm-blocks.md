---
title: A match arm is an expression, so `let` cannot be used inside one
status: closed
labels: [frontend,syntax,elaboration,ergonomics]
created: 2026-08-02
updated: 2026-08-02
---

Noticed while writing the tabulate suite's checking-position fixture (the
quotation-stage port round, 2026-08-02): an arm's right-hand side is parsed
with `expr()`, not as a block, so `Succ(k) => { let y = f(x); g(y) }` has no
spelling — any arm that wants a local binding must inline it or hoist it to a
helper `fn`. The tabulate suite used argument position instead.

Related but distinct from [[annotated-let-swallows-the-equals]] (that one is
about the annotation's `=`; this one is about arms not admitting statements
at all). Together they make `let` unusually weak: not writable annotated, not
writable in arms.

Wanted: either arms accept a block expression, or a general
`{ stmt*; expr }` block-expression form both sites share. The latter likely
subsumes [[nested-goal-discharge]]'s wish for a hole inside an `on`
right-hand side — check when designing.

## Log

- 2026-08-02: RESOLVED by docs/language/let-and-blocks-design.md §4. Two corrections to how this was filed. (1) SMALLER than filed. This reads as a head-on grammar collision needing a lookahead disambiguator on the model of group_is_type. It is not: a record literal is a POSTFIX form on a name head (parser.rs:1090-1102 -- it fires only when the already-parsed expression is a Var or a TyApp over a Var), and a PREFIX `{` in expression position was a parse error in every production, falling to atom's 'expected an expression'. So the disambiguation is POSITIONAL, exactly the argument docs/language/surface-fin-indexing-design.md §5.1 made for postfix `[`, and group_is_type is the wrong precedent -- it exists because in TYPE position a leading `(` genuinely opens either reading, and nothing analogous holds for `{`. Three collision checks done rather than asserted: `match m { … }` (scrutinee parsed with no_record_lit, m is an Ident atom, unchanged), `D { x: 1 }` in an arm (still the postfix literal), `fn f() -> T { … }` (decl() calls block() directly). One consequence worth naming: the block form is INDEPENDENT of no_record_lit, so retiring docs/language/surface-records.md §6.1's provisional braced literal would not touch it. (2) The real work was elsewhere, and this issue does not mention it: an elab_stmts refactor (the let-alias loop lifted out of elab_decl_inner so a declaration body and a block expression cannot drift in what a `let` means) and four exhaustive walks -- count_holes, scan_splices, expr_mentions, and elab_check_hinted/elab_infer's own arms. count_holes is load-bearing: a shallow arm that visited the block's result but not its stmts reproduces 'internal: more goals than the pre-count reserved' exactly as predicted, verified by deliberately breaking it. What landed: ExprKind::Block(Box<Block>) over the EXISTING Block node, recognized at a prefix `{` in atom, delegating to block() verbatim, and CHECKING- and inference-transparent (a block in an arm under a dependent motive is checked at the arm's type, not inferred and converted). Arms get blocks because every expression position does -- call arguments, let values, vector elements, lambda bodies, match scrutinees -- which was the argument for the general form over an arm-local one. THE SPECULATION IS ANSWERED AND IT IS NO: a shared block form does NOT subsume [[nested-goal-discharge]], and cannot. That refusal is not a grammar limitation but lib.rs:838-843 (new_goal refusing while frozen), lib.rs:924 (solve_goals setting frozen before the first discharge) and the strengthen_global(&t, goal_base) on every solution, which is sound EXACTLY BECAUSE no goal occurrence survives in a payload. Lifting it needs discharge in dependency order -- a graph over 'goal A's solution mentions goal B', cycle rejection, reverse-topological substitution -- which is an elaboration algorithm no amount of grammar produces. The relationship runs the OTHER WAY: a block expression must DECLINE `on` discharges precisely because accepting them would mint a nested goal scope, and it does, with a parse error naming that issue. Nothing is lost by the refusal: a hole inside an arm-level block is an ordinary goal in the declaration's list with the arm's binders and the block's aliases captured in its Cx, discharged by the declaration's own trailing `on` -- tested in crates/elab/tests/let_and_blocks.rs. Also deferred with a reason rather than by omission: INTERLEAVED statements (block_body's all-lets-first shape stands), because an expression statement in a language with no effects is a no-op, and the form becomes meaningful exactly when [[effects-direction]] decides what a statement is.
