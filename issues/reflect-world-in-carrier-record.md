---
title: Reflect a carrier record holding the world as its fields
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-08
updated: 2026-11-08
---

A `runtime fn` that calls an interface-generic function at an `Io`-backed
carrier (`greet(Buffered(io, []))`, `docs/language/effects-locality-design.md` §5.2)
hands the reflector a world inside a record. The effectful reflector
(`lib/native/runtime/rt_io_reflect.hthr`) refuses that: the world may never
be stored in a record other than the `Mutated` a `mut self` method returns
and loop state (`docs/language/effects-capabilities-design.md` §5, §8.3).

## Scope

- Read a carrier record as its fields, as pure `rt` already lays records
  out (`docs/native/runtime-fn-setups-design.md` §16.7): the world field joins the
  `.after` chain and the other fields are ordinary variables, so a method
  that rebuilds the record (`Buffered(c.inner, c.pending ++ m)`) reflects
  as a `Let` of the new field and no copy of the world.
- Linearity unchanged: a record holding the world is used exactly once, as
  the world is; a copy of the record is refused at the call as a copied
  world is.
- Specialisation: reflect a generic callee at the concrete carrier
  (unfolding the instance's members), with `ETm` callees left to
  [[rt-effectful-callees]].
- `ETm::lower_reads` holds unchanged; the probe is the buffered `greet`
  lowered, run at a piped world, and read as its surface function.

## What it assumes from elsewhere

- **[[effect-interfaces-over-carriers]]** owns the surface. Assumed here:
  only that carriers are records with the world in one field.
- **[[effects-uniqueness-surface]]** owns the reflector and its refusals.
