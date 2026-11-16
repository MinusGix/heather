---
title: Instantiate an unapplied law whose left side is headed by a class operation
status: closed
labels: [tactics,rewriting]
area: tactics
milestone: [tac-general]
created: 2026-10-28
updated: 2026-10-28
---

`rewrite(Semiring::mul_range_l, …)` at an open semiring finds no instance:
the law's left side `c * ∑ k < n, f(k)` is headed by the class's `*`, a
pattern variable of its telescope (the section's operation), and §6.1's key
(`same_key` in `crates/elab/src/rewrite.rs`) refuses a pattern-variable
head, so no goal node is ever tried. At a concrete carrier the same law has
the same pattern head. A second gap in the same matcher: a body pattern
`λ k. f(k)` binds nothing (it is deferred, and `f` occurs only under the λ);
η makes it the pattern variable `f`.

Under a binder ([[rewrite-setoid-under-binders]]) this is what bites: the
law's arguments mention the bound index, so they cannot be given by hand,
and `big_operator.hthr`'s `range_cong(…, λ i hi => law(f(i), …))` proofs
cannot become `rewrite(law, …)`.

Wanted: key such a pattern by the operation's *instance* (the class
argument the goal's node carries) or let the first argument that is not a
pattern variable decide, with the 256-candidate cap; and η-contract
`λ z. x(z)` patterns.

## Log

- 2026-10-28: Done (docs/tactics/equation-rewrite-design.md §6.1). `same_key` keys a pattern headed by one of its own variables by its first argument that is no variable (refusing an all-variable pattern, as before); `match_pattern` resolves a class-dictionary argument left unbound once the arguments before it are, and refuses the candidate when nothing resolves (`c + ∑ …` binds `*` to `+`); a `λ z. g(z)` pattern matches as `g` (η) against the candidate's η-contraction or the λ itself. Works at an open semiring and at `Rat`, at the root and below a binder. `big_operator.hthr`'s `range_mul_range` and `range_cauchy` are now one `rewrite(Semiring::…, …)` each; its other `range_cong` proofs consult the bound `k < n` and stay. Probes in `big_operator_tests.hthr`, with a wrong-operation negative control.
