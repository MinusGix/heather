---
title: CoTree/ITree as a type constructor (codata with a value parameter after the slot)
status: closed
labels: [elaboration,unification,traits,codata]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-03
---

`pick({M: Type → Type}, x: M(Nat))` at `t: CoTree<Nat>(E)` says "could not
infer the implicit argument `M`" (probed 2026-11-02,
docs/lambda-carrier-instances-design.md §2). So the ITree carrier for
binding statements, `λ (R: Type) => CoTree<R>(E)`, is neither inferred nor
accepted as an instance head.

Two gaps:

- `constructor_spelling` (gendefs.rs), the route for a declaration with no
  code function, declines codata and any declaration with value parameters.
  CoTree has both.
- The slot machinery (§7.2) builds the constructor from a registered code
  function. Codata registers none, and the value parameter `E` follows the
  slot `R` in the spine. The default slot rule already picks `R`, the last
  *type* parameter, so no `varies` is needed. The constructor is
  `λ R. ⌜CoTree<El R>(E)⌝` over the inline lowering, as `Tac`'s is.

## Done when

`twice` (the probe in `lib/_tests/std/core/type_constructor_tests.hthr`)
computes at a `CoTree<Nat>(E)` value through a `Bind` instance at
`λ (R: Type) => CoTree<R>(E)`, and a binding statement chains two
`CoTree` computations.

## Log

- 2026-11-03: Built with partial-fn-surface. `constructor_spelling` (gendefs.rs) now reads codata and value parameters after the slot: the value arguments are fixed inside the constructor λ (`generic_former_lambda_with_values`), and it declines when a value parameter's type mentions a type parameter. `check_lambda_carrier` and `head_name` (traits.rs) accept `λ (R: Type) => D<…, R>(v̄)` when the binder is not in `v̄`. Instances `Bind`/`Pointed`/`Iterate` at `λ (R: Type) => CoTree<R>(E)` are in coitree.hthr. Done-when probes are in lib/_tests/std/itree/partial_fn_tests.hthr (`twice` at a `CoTree<Nat>(E)` value, `chain` of two trees by binding statements), not in type_constructor_tests, so that the core probes keep their imports.
