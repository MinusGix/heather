---
title: "Standard modules designate their operations before proving their laws"
status: closed
labels: [stdlib,ergonomics,proofs]
created: 2026-08-19
updated: 2026-08-19
---

The core standard modules currently prove most laws in the explicit spelling
of their operations even though the public API designates operators for those
same operations. For example, `std/nat` states

```heather
theorem add_left_zero(x: Nat): add(0, x) = x
```

rather than the surface form a downstream user writes:

```heather
theorem add_left_zero(x: Nat): 0 + x = x
```

The reason is declaration locality, not an expressiveness gap. The `+` and `*`
rows for `Nat`, `&&` and `||` for `Bool`, and `++` for `List<A>` are centralized
late in `std/algebra`; all four `Int` rows sit at the end of `std/int`. A module
therefore cannot use its own public notation while developing the laws that
justify it.

## Round

Move each designation into the module that defines its operation, immediately
after the operation is available, and use the notation in subsequent theorem
statements and proof expressions. Keep an operation's declared name where it is
being passed as a first-class function, a lemma is being cited, an instance key
needs a declaration head, or a dependent motive benefits from exposing the
relation being convoyed: this is a surface-spelling pass, not an attempt to
erase useful names.

The logical connectives are the companion case. They are parser forms rather
than designation rows, so no ownership move is required; once each connective
has been declared, its subsequent kit should use the corresponding `¬`, `∧`,
`∨`, `↔`, `∃`, and `∀` surface.

## Acceptance

- `nat`, `bool`, `list`, and `int` own their operation designations beside the
  declarations rather than receiving them from `algebra` or EOF.
- Their laws use the same operator spelling expected of downstream proofs.
- `logic` uses its connective notation after each declaration becomes
  available.
- Existing imports, instance resolution, computation, and generated terms are
  unchanged, verified by the full suite.

## What it assumes from elsewhere

- **[[surface-operators]]** owns operator resolution. Assumed here:
  only that moving an identical row between modules does not change the
  operation selected from an operand's resolved carrier.
- **[[std-logic-module]]** owns connective grammar. Assumed here: only
  that its notation elaborates to the same declared connective applications.

## Log

- 2026-08-19: Filed for the user-requested cleanup round after the `<`
  designation parser fix made designation locality visible: `Nat` and `Int`
  could finally own `<`, while their older arithmetic rows were still remote.
- 2026-08-19: Implemented. The five rows
  centralized in `algebra` moved to their defining modules (`Nat` `+/*`, Bool
  `&&/||`, generic List `++`); Nat and Int's order rows moved from the ends of
  their files to immediately after `Lt`. The existing law kits now state their
  public API in operators/connectives across `nat`, `bool`, `list`, `int`, and
  `logic`, with representative `calc` chains and induction motives migrated as
  well. No theorem or operation changed.

  One boundary was found by checking rather than guessed: an instance head
  such as `Decide<a <= b>` is refused as having no head type name, because the
  operator-headed surface survives until canonical instance naming. Those
  structural keys keep `Decide<Le(a, b)>`; connective notation does not have
  this limitation because it is parser-desugared directly to `And`/`Or`, rather
  than resolved through the designation table. This is why the round is
  deliberately idiomatic rather than mechanically exhaustive.
- 2026-08-19: Closed after the full suite passed: 1,927 passed, 0 failed. The
  first complete runs exposed two test-only assumptions about the old ownership
  boundary: fixtures redeclared standard rows, and two controls expected
  standard symbols to be absent or fresh. The fixtures now inherit the rows
  from their defining modules and reserve local declarations for deliberately
  nonstandard mappings. No elaboration or public API behavior changed.
- 2026-08-19: Follow-up consistency and enforcement are owned by
  [[stdlib-surface-style-lint]]. The I-prime review confirmed operator notation
  works inside dependent motives too; remaining explicit `add`/`Le`/`Lt`
  spellings must be classified as structural exceptions or cleaned, not
  mistaken for an expressiveness gap.
