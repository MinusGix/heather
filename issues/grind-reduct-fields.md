---
title: grind: a constructor reduct's fields are not the terms the goal writes
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-05
updated: 2026-11-08
---

grind reads a fact's side by its head normal form once the graph as
written proves nothing (docs/grind-design.md §14.4). A constructor reduct's
fields are then the reduct's spelling of them, not the terms the goal or
the other facts write, so injectivity adds an edge to a node nothing else
meets:

- `obs(E, CTau(t)) = OTau(u)` gives `u = …`, where `…` is the kernel's
  spelling of `t` through the codata encoding, an atom whose key (`KOther`)
  is never compared with the local `t`.
- `linux_world_co`'s `Io::pass_tau`, `OTau`/`OVis` arms: the field is
  convertible with `pass_reading(s, io)`, an application node, and the goal
  `x2 = pass_reading(s, io)` stays open. Those arms stay by hand.

Options: compare a reduct's `KOther` field atoms by `Defeq` against every
node of the field's type (costly: a `Defeq` per node); or ask the host for
the field equation spelled with the sides as written (`Inj` already
computes the sides; the field of `obs(E, CTau(t))` could be read off the
source's spine when the source is a constructor application under a
projection); or put the goal's sides' head normal forms beside them too and
compare stuck forms (tried: it broke the `OVis` arm that closed without it,
so not as is).

Probe: `reduct_field_spelled` (was `reduct_field_unread`) in `lib/_tests/std/tactic/grind_codata_tests.hthr`.

## What it assumes from elsewhere
- **[[grind-constructor-facts]]** owns the reducts. Assumed here: only that
  injectivity is asked about the sides as written and its fields are read
  from the reduct.

## Log
- 2026-11-08: The codata probe closes now (renamed `reduct_field_spelled`):
  when the sides stay apart grind reads the next spelling of each stuck
  term under them (docs/grind-design.md §15.1), and the spelling meets the
  reduct's field. `Io::pass_tau`'s arms were not retried.
