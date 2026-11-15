---
title: A type's arguments that mention a bound variable print as <…>
status: closed
labels: [diagnostics]
area: language
created: 2026-11-11
updated: 2026-11-12
---

`Or<Mem(a, xs), Mem(a, ys)>` prints in full at the goal's own scope and as
`Or<…>` below a binder whose variable an argument mentions:

    (x: A) -> Or<…> -> Or<…>
    Exists<…>(λ (x: A) => Or<…>)

`Inductives::display_targs` (`crates/elab/src/inductive.rs`) recovers the
arguments by strengthening each candidate back to the display's root
context, where it re-lowers the declaration to verify them; an argument
that mentions the binder does not strengthen, and the honest ellipsis is
printed. A `simp_show` result under a `∀` or an `∃` is mostly such types
(`docs/tactics/simp-design.md` §12, §13), and the route's own lines, which are
spelled in the binder's context, show what the result line hides.

Wanted: the recovery and its re-lowering run in the context the display
walk is standing in (the root context extended by the binders crossed),
so the arguments need no strengthening.

Done when the two lines above print their `Or`'s arguments.

## Log

- 2026-11-12: Fixed: the display walk keeps the types of the binders it crosses (Speller::here), and display_targs recovers and re-lowers in that extended context, so arguments that mention a crossed binder need no strengthening. Probes in lib/_tests/std/tactic/simp_tests.hthr (below_forall_result, below_exists_result). Exists<…> stays elided: Exists has a value parameter, which display_targs declines by design.
