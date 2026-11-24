---
title: omega fails on a generated local in scope (`unexpected character '#'`) instead of skipping it
status: closed
labels: [tactics,omega]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found proving the word map's specification ([[runtime-hash-map-spec]]).
In the last arm of a `match` on a `Nat` (`Succ(Succ(Succ(Succ(q)))) => λ
(big: q + 4 < 4) => false_elim(omega(big))`, inside a nested match whose
motive was synthesized), `omega` fails with "`omega` got stuck: unexpected
character '#'": a local in scope has a generated name (`#…`), and the text
`omega` renders its context to does not parse back. Naming the facts
(`omega(big)`) does not help, since `omega` reads every hypothesis in scope
([[omega-listed-facts-only]]). The proof moved the step to a lemma
(`WordMap::past_slots(q, big): False { omega }`).

In the same proof, `omega` inside a larger `let`/`λ` context also answered
"Omega could not spell a natural expression" for `jj.toNat() < 4` from
`jj.toNat() = s` and `s < 4` (`WordMap::remove_reached` transports it with
`j` instead).

## Wanted

`omega` skips (or renders under a spellable alias) a local whose name or
type it cannot spell, instead of failing the call; the refusal names the
local it could not spell.

## Log

- 2026-11-24: Fixed (branch `claude/proof-tooling-omega`). A generated binder (`#p1`, the variable a nested pattern binds and the written `q` aliases) is named `__omega_hidden_N` in `omega`'s source context, as a shadowed one is, and is still not read as a fact itself. A term with no spelling of its own is spelled again with each subterm that is a visible `let`'s value written as the `let`'s name (`spell_term_source_aliased`), so `jj.toNat()` for `let jj = reached.witness` spells; a term nothing names is refused with the term quoted and the advice to bind it. `WordMap::past_slots` and `WordMap::remove_reached` are gone (`false_elim(omega(big))` in both `match` arms; `remove_present` proves `jj.toNat() < 4` by `omega(js, s4)`). Design: docs/tactics/omega-measure-reduction-design.md §26. Probe: `lib/_tests/std/tactic/omega_tests.hthr` ("Locals with no spelling"); the word map's own `locate` and `remove_present` are the in-context cases.
