---
title: Rewrite every instance of an unapplied law in one walk
status: open
labels: [tactics,proofs,performance,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-26
updated: 2026-11-11
---

`rewrite(h, e)` with an unapplied law instantiates it once, at the first node
that matches, and rewrites every occurrence of *that* instance
(`docs/equation-rewrite-design.md` §6.1, Lean's `rw`). Rewriting `g(f(f(…f(a))))`
to `g(a)` by `h: (x) → f(x) = x` is therefore n rewrites, each a walk of the
goal, and the bench families with linear lower bounds read n² for that reason
alone: `rewrite/fa`, `rewrite/repeat-mod`, and `rewrite/let-addr0` since its
abstraction stopped being a tree walk (§9.5).

mengine (and Lean's `simp only [h]`, Rocq's `rewrite_strat`) rewrite every
instance in one walk: each node is matched against the law on its own, and a
node whose arguments were already rewritten is matched in its rewritten form.
The relation walk (§9.3) already visits each node once, children first, and
keeps one result per node; matching the law at every node instead of
comparing with one instance is the change, for `=` and relations alike.

Design questions this owns: the spelling (a named argument on `rewrite`, or
another entry point, since `rw` semantics are what the library relies on), and
termination: a law whose right side matches its own left side
(commutativity) must not loop, so a rewritten node is not matched again.

## Log

- 2026-11-08: 2026-11-08: [[simp-tactic]] builds on this walk with a set of laws in place of one.
- 2026-11-11: `simp_only(h)` ([[simp-tactic]], `crates/elab/src/rewrite/simp.rs`) is the entry point that rewrites every instance of an unapplied law, and it detects a commuting law's loop. Its cost is still one walk and one `J` (or one relation plan) per instance: the driver calls the existing step until nothing fires. The one-walk matcher this issue asks for would go under it without changing the surface.
