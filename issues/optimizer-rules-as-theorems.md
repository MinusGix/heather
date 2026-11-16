---
title: Write optimizer rules as theorems about words, registered from anywhere
status: open
labels: [native,optimizer,readability,metaprogramming]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

Design: `docs/native/optimizer-rules-design.md` (Minus agreed the surface, the report and the direction on 2026-11-16, §11).

Today a rule is a clause over node constructors and ids, a soundness proof over a valuation, a line of `rules()` unpacking a list of numbers, and a recogniser in `function_ir_learn.hthr` naming it by its place in the table. Wanted: a rule is an ordinary theorem about words under a `rule` prefix, and the clause, its soundness, its guard, its registration and its recogniser come from the statement.

Steps (design §10), each landing alone with the same code out of the optimizer:

1. Fact forms and the operator table as library definitions, and the generated soundness as a tactic used by hand on today's clauses.
2. `rule theorem`: the generator, registered by name (`registered(Rule)`); port rules 0 to 44; plans name rules by key.
3. The matcher in `learn`; single-rule recognisers ported onto it; strategies (word load, word store, guards) as registered learners.
4. The report (`compile-x86 --explain-optimizer`) and `rule_check`.
5. Saturation for the equation rules on `lib/std/data/egraph.hthr`.
6. Domains (ranges first, joins where paths meet, the loop check).
7. Open fact forms, the order graph, tagged library theorems replacing composite rules, rules found by machine.

Built (design §12): `rule_sound` (`function_ir_rule_sound.hthr`), the `rule` prefix generator (`function_ir_rule.hthr`, publishing `name_rule: Rule`), and all 45 rules of `function_ir_rules.hthr` stated as `rule theorem`s. Tests: `lib/_tests/native/function_ir/function_ir_rule_tests.hthr` (the generator) and `function_ir_rule_words_tests.hthr` (`rule_sound` by hand).

Left of step 2: registration by name, which needs the tactic host to publish a `register def` (a new `DeclForm`, an elaborator change); with it plans name rules by key and `rules()` goes.

Found on the way: a tactic failure whose message prints a very large goal can run the checker out of memory while the message is read back; the generator avoids `whnf` on statements for that reason.

Related: [[optimizer-as-refinement]], [[optimizer-search-answers-memo]].
