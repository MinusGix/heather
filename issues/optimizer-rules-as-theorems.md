---
title: Write optimizer rules as theorems about words, registered from anywhere
status: open
labels: [native,optimizer,readability,metaprogramming]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

Design: `docs/native/optimizer-rules-design.md` (a proposal; §11 lists what Minus decides before any of it is built).

Today a rule is a clause over node constructors and ids, a soundness proof over a valuation, a line of `rules()` unpacking a list of numbers, and a recogniser in `function_ir_learn.hthr` naming it by its place in the table. Wanted: a rule is an ordinary theorem about words under a `rule` prefix, and the clause, its soundness, its guard, its registration and its recogniser come from the statement.

Steps (design §10), each landing alone with the same code out of the optimizer:

1. Fact forms and the operator table as library definitions, and the generated soundness as a tactic used by hand on today's clauses.
2. `rule theorem`: the generator, registered by name (`registered(Rule)`); port rules 0 to 44; plans name rules by key.
3. The matcher in `learn`; single-rule recognisers ported onto it; strategies (word load, word store, guards) as registered learners.
4. The report (`compile-x86 --explain-optimizer`) and `rule_check`.
5. By demand: domains for ranges and bits, orders as a graph with a path certificate, tagged library theorems replacing composite rules, saturation, open fact forms.

Checked so far: `lib/_tests/native/function_ir/function_ir_rule_words_tests.hthr` states four of today's rules as theorems about words and proves today's clauses sound from them by the moves the generator would write.
