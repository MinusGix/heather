---
title: Early cutoff across an interface definition's body
status: open
labels: [caching,elaboration,performance]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-02
updated: 2026-11-02
---

`docs/interface-definitions-design.md` §8. Outside its module an interface
definition's body is withheld from the elaborator and from the gate except
at closed calls, and each gluing is recorded (`heather_kernel::withheld::record`).
So a client declaration that never glued `f` observed only `f`'s type and
its equations' statements.

The slice replay does not use this yet. A consumer citing `twice_unfold_Succ`
is re-elaborated and re-gated when `twice`'s `Zero` arm changes, while an
edit to an unrelated plain `fn` replays it (probe in §8).

## Scope

- In the observation set a declaration records, count a withheld global by
  its type alone unless the declaration's gluing record names it.
- Keep a glued global observed by its body, so a closed `refl` over `f`
  is re-checked when `f` changes.

## Done when

The §8 probe replays the consumer after the `Zero`-arm edit, and a closed
`refl` over the edited arm is still re-checked.

## Log

- 2026-11-02: Filed from the interface-definitions build.
- 2026-11-05: gardener: cites a file it shares with [[interface-definitions]] (`docs/interface-definitions-design.md`).
