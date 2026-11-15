---
title: Rewrite a hypothesis's type along an equation
status: closed
labels: [frontend,elaboration,proofs,ergonomics,design]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

Lean's `rw [h] at hyp`: from `hyp : P(a)` and `h : a = b`, a proof of
`P(b)`. In this surface that is a term in **inference** position — the
transport of `hyp` — rather than a goal to prove: abstract `a` in `hyp`'s
type, and `J(h; y q. M; hyp) : M[b/y]`, no `sym` needed.

The design question is the spelling. Candidates: a second form
(`rewrite_at(h, hyp)`), a named argument on the existing one
(`rewrite(h, in := hyp)` returning the transported term — but then it is not
a checking-position form), or a `let`-statement form
(`let hyp' = rewrite(h) in hyp;`). Pick with a real customer in hand; `let`
heavy proofs in `int.hthr`'s division section are candidates.

## Log

- 2026-10-21: Done: spelling `rewrite(h, …, in := hyp)`, an inference form (Rocq's `rewrite h in H`), chosen against the library's `let x = j(p, λ y _ => M, hyp);` customers (float/round.hthr, function_ir_loop_trace.hthr, x86_64_asm.hthr, …): one form and one rule set with the goal form, no new grammar, `at :=` kept for occurrences. Step is J(h; y q. M; hyp) with no sym. Design: docs/tactics/equation-rewrite-design.md §7.
