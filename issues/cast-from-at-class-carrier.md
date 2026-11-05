---
title: cast_from and cast_to at a class carrier
status: open
labels: [tactics,casting]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

Split from [[cast-reading-at-class-carrier]], which landed `ring`,
`linarith` and `nlinarith` at a class carrier (docs/casting-design.md §16).

`cast_from` / `cast_to` (lib/std/tactic/cast.hthr) still find their carrier
in `cast_carriers()` by global names (`Rat::Same`, `Rat::le_respects`, …):
`CastCarrier` holds `GlobalRef`s, `cast_sides` views the relation as an
`HGlobal`, and the carried proof is a raw `App(Global(C.trans), …)`. At a
class carrier each of those fails:

- the relations and operations are locals (`HLocal` heads), so the carrier
  would be read off the dictionary in scope, as `mono_class_carrier` does;
- the lemmas (`rel_sym`, `rel_trans`, `StrictOrder::le_respects`,
  `OrderedAddGroup::add_respects`, `OrderedField::mul_respects`) take the
  dictionary, and the Tac host's raw application never resolves an
  instance hole: they would be `apply`'d under `focus`, with the
  dictionary as a premise, as `mono_push_applied` does.

So `CastAt` generalises from `GlobalRef`s to keys/`Expr`s, and its proof
steps go through `apply`. The pushes themselves already work at `K`: the
edges are the local morphism's (`mono` reads them).

Wanted when a generic proof carries a cast fact by name rather than by
`mono`; none does yet.

## Log

- 2026-11-05: gardener: cites a file it shares with [[cast-carrier-reader]] (`lib/std/tactic/cast.hthr`).
