---
title: Preserve parameter expected types while elaborating named arguments
status: open
labels: [frontend,elaboration,syntax,proofs,ergonomics]
created: 2026-08-31
updated: 2026-08-31
---

Named arguments are reordered into declaration order, but some payloads are
still elaborated in synthesis position instead of against the selected
parameter's instantiated domain. The FunctionIR certificate generator exposed
three equivalent symptoms:

- `head := ⟨output, ⟨left, right⟩⟩` reports that anonymous constructor notation
  has no expected type;
- `found := Exists(origin, proof)` cannot infer the value parameter that the
  parameter type fixes; and
- implicit declaration parameters such as a list head or directory entry are
  not recovered from the named proof argument or the call's expected result.

The current workaround adds typed helper theorems and spells data parameters
explicitly. That is useful generated staging, but it contradicts the named
argument design's checking-position rule.

## Acceptance

- A named argument payload is checked against the selected parameter domain
  after earlier declaration-order arguments have been applied and zonked.
- Anonymous constructors, `Exists(...)`, `refl`, lambdas, and holes behave the
  same in positional and named arguments at the same parameter.
- Free written order remains supported and diagnostics still point to the
  written named argument.
- Existing no-named-argument and partial-application controls remain unchanged.

## What it assumes from elsewhere

- **[[named-arguments]]** owns ordering and application semantics. Assumed
  here: named payloads are elaborated in declaration order and should use the
  ordinary explicit-argument checking path.
- **[[implicit-value-inference-through-constructor-fields]]** owns nominal
  inference beneath constructor fields. Assumed here: this issue does not need
  such inference when the selected parameter already supplies the complete
  expected type.
