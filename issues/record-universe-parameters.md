---
title: Let records declare type parameters at a universe
status: closed
labels: [frontend,elaboration,syntax]
area: language
created: 2026-11-09
updated: 2026-11-09
---

A class may declare its carrier at a universe, `class Frame<A: Type<1>>`: the
carrier becomes the record's leading value parameter, as a kinded carrier
(`Bind<M: Type → Type>`) does, and dot sugar, resolution and the `T::C(…)`
spelling handle it (docs/library/frame-locale-design.md §3). A `record` cannot:
`record FrameHom<A: Type<1>, B: Type<1>>(…)` is a parse error ("expected `>`
to close the type parameters"), because a record's type parameters are plain
`Type<0>` names.

So `lib/std/locale/frame.hthr`'s `FrameHom`, `LocaleMap` and `Nucleus` take
their carriers as value parameters, `FrameHom(A, B, map, …)`, and every
mention spells the carriers out where the type-parameter form would infer
them.

Wanted: a record's `<A: Type<n>>` lowered the class's way (a leading value
parameter, bound as a type parameter for the rest of the telescope), with the
angle-bracket spelling `FrameHom<A, B>(map, …)` read back as for a kinded
class (`kinded_class_ty`).

## Log

- 2026-11-09: Filed from frame-and-locale-foundations.
- 2026-11-09: Done. The parser reads a record's `<A: Type<n>>` as a leading value parameter (they lead any plain type parameters), and `R<A, B>(v, …)` reads the surplus angle arguments back as those values (`universe_lead` in elab/inductive.rs). FrameHom, LocaleMap and Nucleus moved onto it; probes in lib/_tests/lang/universe_parameter_tests.hthr, parser tests in crates/syntax/tests/record_universe_params.rs.
