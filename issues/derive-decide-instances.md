---
title: Derive Decide for definitions built from decidable parts
status: open
labels: [stdlib,elaboration,traits,decidability,ergonomics]
area: tactics
created: 2026-09-18
updated: 2026-09-18
---

`Decide` should be derivable for a definition whose body is built from
decidable things, so that `scalar` in `lib/std/text/char.hthr` needs no
hand-written `scalar_dec` ([[string-char-spec-types]]).

The connective instances already exist (`logic.hthr`: `Decide<P ∧ Q>`,
`Decide<P ∨ Q>`, `Decide<¬P>` over decidable `P`, `Q`), and `nat` has
`Decide<Le(n, m)>` and `Decide<n = m>`. What is missing is that resolution
does not look through a definition: at the goal `scalar(97)` the candidates
are tried against the *name* and rejected (probe 2026-09-18: `nat::Le::Decide`
"could not infer the implicit argument `n`"), where one unfolding would expose
`Lt(97, 0x110000) ∧ ¬(…)` and the connective ladder would finish it.

Two shapes to cost:

- **Resolution unfolds the goal's head** when no instance matches the name:
  one δ-step, then retry. Cheap and general, but `Lt` is `Le ∘ Succ`, so
  `Decide<Lt(n, m)>` also wants either its own instance or the same
  unfolding one level down.
- **A `derive Decide` on the definition** that synthesizes the instance from
  the body's shape at declaration time, failing with the first undecidable
  subterm named. Explicit and auditable; the derived instance is an ordinary
  one, so it also settles *which* procedure runs (the point of
  `docs/tactics/reflection-through-decide-instances-design.md`).

Either way the derived decision must still *reduce* (it is a `fn`, not a
`theorem`), or `decide` at a closed fact stops being `refl`.

## Log

- 2026-11-05: gardener: cites a file it shares with [[decidable-relations-and-comparison]] (`docs/tactics/reflection-through-decide-instances-design.md`); [[resolution-candidate-fan-out]] (`docs/tactics/reflection-through-decide-instances-design.md`); [[sequence-parser-source]] (`lib/std/text/char.hthr`).
