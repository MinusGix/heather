---
title: Respell type names that take type arguments, and codata
status: open
labels: [diagnostics]
area: heather-in-heather
created: 2026-11-06
updated: 2026-11-06
---

[[type-name-display-respelling]] respells an instance by the name the
program wrote only when the name expands to a declaration with **no type
parameters** that is not codata (docs/elaborator/surface-type-display-design.md §5.1):
`u8`, `i(n)`, `def Byte: Type = BitVec(8)`. Two shapes stay spelled as their
expansion:

- a name over a declaration with type parameters, `def Bytes: Type =
  List<u8>`, or a name that takes a type, `def Partial: Type → Type = λ B =>
  CoTree<B>(Events::none())` (which [[partial-fn-use-site-refusal]] wants to
  read `Partial(Nat)`);
- codata instances, whose display goes through the `Type::M` branch and its
  named-signature reading rather than the inductive instance branch.

The table reads a name off the definition's body; for these the entry would
carry type-argument codes (matched against `display_targs`, or the
`TyCodeFn` application's leading codes) and, for a type-taking name, a
pattern over its own parameter. `Partial` would match only where the program
wrote it, so it needs [[partial-fn-use-site-refusal]]'s knowledge that a
call's result type came from a `partial fn` too, or a rule that a library
name is offered without being written.

## Done when

`List<u8>` under `def Bytes` and `CoTree<Nat>(none)` under `Partial` respell,
with probes beside lib/_tests/std/bitvec/type_names_tests.hthr.
