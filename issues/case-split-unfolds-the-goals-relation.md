---
title: A named case split hands its arms the goal unfolded past its relation
status: open
labels: [elaboration,proofs,relations]
area: language
created: 2026-11-11
updated: 2026-11-11
---

In `Regex::deriv_simp_same` (`lib/std/text/regex/regex_dfa.hthr`) the goal
of the `Seq(a, b)` arm is `Seq(a, b).deriv_simp(c) ≈ Seq(a, b).deriv(c)`,
and `deriv_simp` at `Seq` is a match on `a.nullable()`. The proof splits on
it, `match ha: a.nullable() { True => …, False => … }`, and each arm's goal
arrives as

    (x: List<Nat>) -> Iff<…>

that is, `≈` (`Regex::Same`) unfolded to its definition, with the stuck
match somewhere inside. The split found its scrutinee by reducing the goal
and kept the reduct. A tactic that reads the goal as `R(l, r)` (`simp_only`,
`rewrite` along `≈`, `rel_cong`) sees no relation there, so each arm
restates the goal in a one-step `calc`:

    True => calc {
        Regex::alt(Regex::seq(a.deriv_simp(c), b), b.deriv_simp(c))
            ≈ Alt(Seq(a.deriv(c), b), b.deriv(c)) := simp_only(…),
    },

Wanted: the split's arms get the goal as written with only the scrutinee's
match computed, `Regex::alt(Regex::seq(a.deriv_simp(c), b), b.deriv_simp(c))
≈ Seq(a, b).deriv(c)`: reduce inside the arguments of the goal's head
(`goal_combinators::simplify_goal` does this for a `split_all`) before
reducing the head itself. An inference change: the whole library
re-elaborates before it merges (CLAUDE.md).

Done when the two arms of `deriv_simp_same` are bare `simp_only(…)` calls.
