---
title: Infer implicit values through nominal constructor fields
status: open
labels: [frontend,elaboration,inference,inductives,proofs]
area: language
created: 2026-08-28
updated: 2026-08-28
---

An explicit proof field can determine a hidden value even when that value occurs
only beneath an inductive constructor in the field's type. The representative
shape is a callee expecting

```heather
proof: Some(hidden) = Some(actual)
```

with an argument whose inferred type contains the same nominal `Some` on both
sides. At the source level, matching constructor heads make `hidden` as plainly
recoverable as a value beneath an ordinary rigid type application.

The nearby abstract case already works: for

```heather
Valid: K -> V -> Type
valid: Valid(entry.key, entry.value)
```

an implicit `key` and `value` appearing only in `valid`'s field type are both
inferred. `crates/elab/tests/lib_std_certified_lookup.rs` pins that boundary.
The gap begins when nominal inductive structure has been lowered into the
kernel's shared `Pair`/`Inl`/`Inr` representation.

## Rejected widening

Teaching first-order unification to recurse whenever two raw `Pair`, `Inl`, or
`Inr` terms have the same kernel tag makes the motivating micro-case pass, but
is not a valid account of source constructors. Those encodings are structural
machinery shared by unrelated nominal declarations, so matching their tags is
not evidence that two source constructors have the same identity.

The experiment was reverted rather than landed on kernel checking alone. The
complete-suite validation was also inconclusive: three exact-term conversion
controls fail identically at current `master` with the experiment absent, now
owned by [[generated-term-oracle-controls-not-convertible]]. They therefore
cannot honestly be cited as regressions caused by this rule. A future attempt
needs the nominal guard above and a green oracle baseline before it can claim
that elaborated witnesses are unchanged.

## Acceptance

- Infer hidden values beneath matching constructors only when both sides are
  known to be the same nominal declaration and constructor, not merely the
  same raw kernel encoding.
- Establish where that identity comes from before changing unification: retain
  declaration/constructor provenance through lowering, or read back a guarded
  nominal view from elaborator metadata.
- Keep the rule learn-only. Every result remains kernel checked, but elaboration
  must not select a different convertible witness opportunistically.
- Add positive tests for `Option` and a user-defined constructor, plus negative
  controls for two declarations with isomorphic lowerings and for a phantom
  hidden value that occurs nowhere in the field or expected type.
- Restore [[generated-term-oracle-controls-not-convertible]] first, retain
  those controls as exact-term regressions, and run the complete elaborator
  suite before landing.

## What it assumes from elsewhere

- **[[argument-type-reduction-after-partial-inference]]** owns the distinct
  case where a syntactic read makes partial progress and reduction would expose
  another implicit. Assumed here: the constructor-bearing argument type is
  already visible; no reduction policy change belongs in this issue.
- **[[elab-unifier-completeness]]** owns general higher-order completeness.
  Assumed here: nothing; this is a deliberately first-order, nominally guarded
  recovery rule.

## Log

- 2026-08-28: Filed after a certified-lookup inference probe. Abstract rigid
  field applications already work. Raw `Pair`/`Inl`/`Inr` congruence made the
  desired constructor example pass, but lacked nominal justification and was
  reverted. Three oracle failures discovered during validation reproduce with
  the experiment absent, so they are recorded separately rather than falsely
  attributed to this change.
