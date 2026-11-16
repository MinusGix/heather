---
title: Split nat, int and ordered_field so their theories can be proved by the tactics built on them
status: open
labels: [stdlib,modules,tactics,cleanup]
area: mathematics
created: 2026-11-08
updated: 2026-11-10
---

The arithmetic tactics import the theories they automate, so those theories
are proved without them:

| module | lines | tactic that imports it |
|---|---|---|
| lib/std/num/nat.hthr | ~2,500 | `omega` (imports bool, int, list, logic, nat) |
| lib/std/num/int.hthr | ~2,000 | `omega` |
| lib/std/algebra/ordered_field.hthr | ~1,200 | `linarith` (imports ordered_field, ring, omega) |
| lib/std/algebra/semiring.hthr | ~440 | `ring` |

In nat.hthr, `Nat::lt_of_le_of_ne` (14 lines), `Nat::le_add` (`n <= m → n +
(m - n) = m`, 15 lines) and `Nat::lt_trichotomy` (20 lines) are recursions
over linear facts that `omega` states in one line anywhere downstream
(some of them may be lemmas `omega`'s certificate cites, which is what the
split below has to find out). `Nat::max_le` is three nested case analyses
"because the goal mentions all three values and the hypotheses have to be
convoyed past two of them"; `omega` cannot help there yet either, since it
reads `max` as an atom ([[omega-reads-min-max]]).
`ordered_field.hthr` is where the hand `le_respects(…, same_refl(), …)`
chains concentrate (127 setoid-plumbing lines). And when a fact is wanted
*with* automation it moves out of its home: real_fn.hthr opens with
"The bound lemmas at the top (`OrderedField::half`, `below_both`, `shrink`,
…) are facts about an ordered field and would live in `ordered_field.hthr`,
but their proofs are `linarith` and `nlinarith` calls and the `linarith` kit
imports `ordered_field`; they live here … until that edge is cut." That
contradicts the project rule that a type's facts live in its own file.

## Direction

Split each module into the part its tactic's certificate needs and the
rest, and keep one name for clients through `export` (lib/std/parser/parser.hthr
re-exports `parser_core` and `parser_combinators` this way):

- `nat_core` / `int_core`: the definitions and exactly the lemmas `omega`'s
  soundness cites; `nat` / `int` import `omega` and export the core.
- `ordered_field_core`: classes, instances' laws and the lemmas
  `linarith`/`ring` certificates cite; `ordered_field` imports `linarith` and
  holds the theory, including real_fn's misplaced bound lemmas.

Then reprove by tactic only where it shortens a proof; this issue is the
layering, not a rewrite. Watch the `// lib-closure:` lists
(`scripts/lib-closures --fix`) and the image cut-off: a client importing
`nat` now also replays `omega`'s closure, which may cost more than it saves
for small clients; measure with `scripts/perf ab --source-patch` before
landing.

## Acceptance

- `import nat;` and `import ordered_field;` mean what they mean today to
  every client (no client edits beyond lib-closure regeneration).
- real_fn.hthr's bound lemmas live in ordered_field's theory half.
- A probe in `lib/_tests` uses `omega` inside the `Nat` theory module.

## Related

[[feature-implicit-module-dependencies]], [[std-prelude-facade]];
docs/surveys/stdlib-math-awkwardness-survey.md §4.

## Log

- 2026-11-10: 2026-11-10: the common prelude now imports ordered_field (issues/linarith-rat-without-ordered-field-import.md), so nat, int, omega, semiring, order and ordered_field are inside the prelude's closure. A split here keeps whatever the prelude's import reaches free of the prelude itself; a theory module that moves after its tactic leaves that closure and sees the prelude again.
