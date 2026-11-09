---
title: Read sets over any carrier with decidable membership in the sets tactic
status: closed
labels: [tactics,sets,native,memory]
area: tactics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

`sets` ([[finite-set-membership-solver]], [[set-solver-boolean-spellings]])
read only lists, through `Mem`, and found operations in a registry of
`SetOpEntry`s naming a connective and an `Iff` law. Span footprints
([[address-interval-sets]], [[span-footprint-automation]] part 1) and any
other structure whose membership is a Boolean (bitsets, interval maps,
characteristic functions) could not be read without a second solver.

Minus (2026-11-09): sets over any decidable membership, through a class
hierarchy, and goals saying a relation is false.

## Design

- `lib/std/data/set/dec_set.hthr`: `DecSet<S, A> { has, empty, has_empty }`
  and one class per operation, indexed by the membership and the operation
  (docs/operation-indexed-classes-design.md): `SetUnion`, `SetInter`,
  `SetMinus` (a binary operation whose membership is "or", "and", "and
  not"), `SetInsert` (`has_here`, `has_other`: `Cons` is one), `SetFilter`,
  and `SetReflects<S, A>(has, P)` for a proposition membership decides
  (`Mem`). Each law is a Boolean equation, so instances are used by
  rewriting and evaluation alike; the list instances derive theirs from the
  `Mem` laws through `set_reflects_same` (two bits reflecting one
  proposition are equal).
- `set_solve` over a carrier: `SetExpr { SAtom, SEmpty, SIns, SFilt, SBin }`,
  operations `SetOpFn { OpBin(f, conn), OpIns(f), OpFilt(f) }` with their
  laws as one `set_ops_lawful` conjunction (the instances' fields, as they
  are), agreement `C.has(e.denote, x) = e.eval(bits)` as a Boolean equation,
  element equations as facts of their own (`FEq`, `FNe`, goal `GEq`) rather
  than singleton membership, and a new goal `GSame(a, b)`: `x` is in `a`
  exactly when in `b`.
- The tactic finds the carrier from the goal's types (`Synth` on
  `DecSet<S, A>`), an operation by the types of its last two arguments and
  `Synth` on its class (a constructor through `Ctors`), the empty set by
  conversion, and reads any call `f(…, s, x)` that converts to `has(s, x)`
  and any proposition `P(…, x, s)` with a `SetReflects` instance. A
  problem is about one carrier; literals about another are skipped. A
  `False` goal or an equation is tried at each element a literal is about,
  at that literal's carrier, else at lists of the element type.
- Relation-false: `f(a, b) = False` for a registered relation is `f(a,
  b).IsTrue() → False`, proved as any other goal (the elim law reads the
  truth as an inclusion, and an element on the wrong side contradicts it).
- `SetOpEntry` is gone: native's `union`/`minus` are `SetUnion`/`SetMinus`
  instances, spans and span sets have `DecSet` instances
  (`Span::meet` is an intersection), and `span_set_rels.hthr` registers
  `within`, `apart`, `disjoint` as relations.

Instances come from a module's direct imports, so a client imports
`dec_set` beside `set_tactic` (and the module of any other instances it
reads, as before).

## Log

- 2026-11-09: Built as above; probes in `lib/_tests/std/tactic/set_tactic_tests.hthr`
  over lists spelled by `has`, span sets (union/inter/minus/empty, `within`,
  `disjoint` true and false, membership equations), a span's `meet`, and a
  client-defined carrier with an insertion. The tactic reads every
  hypothesis once per goal (`sets_shapes`), and a literal read off a call's
  last two arguments is kept only when some carrier holds such sets
  (`a.Inside(m)` is an inclusion, not a membership).
