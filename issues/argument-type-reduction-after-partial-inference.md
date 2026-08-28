---
title: Retry reducible argument types after partial implicit inference
status: open
labels: [frontend,elaboration,inference,proofs]
created: 2026-08-28
updated: 2026-08-28
---

`Elaborator::unify_arg_ty` reads implicit arguments structurally from an
explicit argument's inferred type. If that first read learns nothing, it also
reads the type's weak-head normal form; [[motive-application-hides-hypothesis-type]]
landed that guarded retry. It deliberately does not normalize after *any*
progress, preserving the old path for calls that already elaborated.

Certified lookup found the missing mixed case. Given

```heather
success: lookup(...) = Some(value)
```

and a helper whose domain is

```heather
Some(left) = Some(right)
```

the syntactic read learns `right := value` from the visible right endpoint.
The left endpoint would become `Some(entry.value)` after reducing `lookup`, but
the partial progress suppresses the weak-head retry, so `left` remains
unsolved. The current library therefore writes the computed left endpoint and
infers only the field-carried right one:

```heather
lookup_some_injective(entry.value, success)
```

This is an elaboration refusal, never a soundness gap; the kernel gates every
fully instantiated call.

## Acceptance

- Let reducible argument-type evidence fill implicits left unsolved by a
  partially successful structural read, including the lookup shape above.
- Preserve the no-guessing boundary: a value not mentioned by the argument
  type or the expected type remains an inference error naming that value.
- Do not simply change the hot-path trigger from "learned nothing" to "anything
  remains unsolved". A call whose later arguments or expected type already
  finish inference should not begin normalizing earlier argument types.
  Prefer a final recovery pass over recorded incomplete reads, after ordinary
  argument and expected-type evidence is exhausted.
- Keep reduction opportunistic and fuel-bounded; failure to reduce retains the
  ordinary per-implicit inference diagnostic.
- Measure the meta/nested-inference frontend family and the complete elaborator
  suite. No kernel or fuel-policy change belongs here.

## What it assumes from elsewhere

- **[[motive-application-hides-hypothesis-type]]** owns the existing
  no-progress weak-head retry. Assumed here: its learn-only and opportunistic
  reduction discipline remains the model.
- **[[elab-unifier-completeness]]** owns general unification. Assumed here:
  nothing; both endpoints here are first-order once the subject type reduces.
- **[[implicit-value-inference-through-constructor-fields]]** owns nominal
  constructor structure hidden inside proof-field types. Assumed here: nothing;
  this issue begins only after ordinary structural inference has already learned
  one endpoint and reduction is needed to expose the other.

## Log

- 2026-08-28: Filed from the certified-lookup cleanup. A rigid abstract field
  application already infers values that occur only in the field type, and a
  generic regression test now pins that capability. The remaining lookup case
  is specifically partial-progress plus reduction: one endpoint is learned
  syntactically and the other is exposed only by reducing `lookup`. It was left
  explicit rather than widening every partly successful call's inference path.
