---
title: A quoted component's code is still walked once per node of the enclosing proof: the block that the respelled quote leaves behind
status: open
labels: [elaboration,kernel,representation,performance]
created: 2026-09-16
updated: 2026-09-16
---

docs/complete-post-attribution-design.md §10: quoting the respelled type removed 87 % of `complete_post`'s misses and 31× its evaluator steps but only 36 % of its conversion queries (5.73 M → 3.68 M), and the item is halved (20.6 → 10.9 s), not divided by six. The blocks per binder-dependent component of a declared `→ Type` former still add exactly (`Le` +0.86 M, an equation +1.29 M, the open relation applied +1.72 M queries over a 0.68 M base), and the kernel gate is a flat ~1.9–2.0 µs per query, so what remains is traversal of a code that now *names* its sub-lowerings rather than copying them. A component built from primitives had nothing to rename and keeps its whole block: `close_body`, `expr_body`, `factor_body` are unmoved at ~1.0–2.6 M queries each. `t_cp18` (the same component twice) over-adds 1.25× in queries on both sides, unexplained.

Attribute the remaining block the same way (`probes/t_cp2`/`t_cp9`/`t_cp12`/`t_cp17` are the subtraction table; trace by site, not head pair, since the misses are now a remainder): which walk asks ~1 M queries for one equation's code, and whether it is the kernel re-checking the code's formation at every occurrence of the component in the proof's annotations or the elaborator writing the component once per node. A kernel memo is not chartered without a trace showing the same syntax at the same Γ repeating (design §6). Related: [[elaborator-canonical-type-spelling]], [[quote-see-through-bounded-arm]], [[parser-certified-composition-cost]], [[fn-statement-level-trees]].
