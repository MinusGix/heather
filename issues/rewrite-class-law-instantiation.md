---
title: Instantiate an unapplied law whose left side is headed by a class operation
status: open
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
