# Standard-library source style

`lib/std` demonstrates Heather's public surface as well as providing APIs.
Prefer the spelling a downstream program should copy.

## Calls and notation

- Supply arguments from one call site in one list: `f(x, y)` rather than
  `f(x)(y)`. A curried declaration does not require curried call syntax;
  over-application carries the remaining arguments into the returned function.
- Keep staged application when the intermediate function is intentionally
  returned, stored, or passed. For example, a partial polymorphic call may need
  explicit type arguments that a later value would otherwise infer.
- After a module designates an operator, use it in public signatures, motives,
  and proofs: `x + y`, `x <= y`, and `xs ++ ys`.
- Likewise prefer `¬P`, `P ∧ Q`, `P ∨ Q`, `P ↔ Q`, `∃ x, P`, and
  `∀ x, P` over calls to the connective declarations.
- Write prefix notation tightly: `¬P` and `¬(a = b)`, not `¬ (a = b)`.
- Use argument slots for a short, one-use eta wrapper when the expected
  function type makes ownership clear: `false_elim(·)` rather than
  `λ p => false_elim(p)`. Keep a named lambda when its binder is reused,
  ignored, or helps explain the proof.
- Keep a named operation when it is used as a first-class value, an instance
  key, or a deliberately qualified disambiguation. Definitions may also expose
  their underlying calls when that makes reduction or termination clearer.

## Comments

- A module comment says what the module provides and records only the
  representation choices a user needs to understand its behavior.
- A declaration comment states meaning, argument order, reduction behavior,
  failure behavior, or a non-obvious law orientation.
- An implementation comment explains a proof or computation that is not clear
  from the body.
- Migration history, round-by-round evidence, and obsolete limitations belong
  in the issue or design document that owns them, not beside the current API.

These are semantic rules, not textual substitutions. In particular, a lint
must understand intentional partial application and resolved operator
designations rather than matching declaration names with regular expressions.
