---
title: "Standard-library surface style: n-ary calls, designated operators, and a lint"
status: open
labels: [stdlib,ergonomics,tooling,lint]
created: 2026-08-19
updated: 2026-08-19
---

Heather's surface now accepts substantially better spellings than parts of the
standard library use. Two recurring examples are:

```heather
nat::lt_trichotomy(m)(n)             // accepted, but needlessly exposes currying
le_isucc(add(a, OfNat(k)))(add(b, OfNat(k)), ih)
match m as λ z => nat::Lt(n, z) -> Lt(NegSucc(z), NegSucc(n)) { ... }
```

The preferred surface is:

```heather
nat::lt_trichotomy(m, n)
le_isucc(a + OfNat(k), b + OfNat(k), ih)
match m as λ z => n < z -> NegSucc(z) < NegSucc(n) { ... }
```

All three preferred forms already elaborate today. Over-application spills a
single argument list across a curried Pi result ([[call-site-overapplication]]),
and carrier designations resolve operators inside written motives. This is
therefore a style/enforcement issue, not an expressiveness issue.

## Style rules

1. When all arguments are supplied at one call site, prefer one n-ary argument
   list: `f(a, b)` over `f(a)(b)`. Preserve staged application when the partial
   result is itself meaningful, stored, passed, or returned.
2. After a defining module has installed a designation, prefer its operator in
   theorem statements, proof expressions, and motives: `a + b`, `a < b`,
   `xs ++ ys`. Keep the named operation when it is passed as a first-class
   value, cited as a declaration/instance key, deliberately qualified to
   resolve an API ambiguity, or structurally exposed for elaboration.
3. A local exception should be explainable in those semantic terms, not merely
   “the old spelling also checks.”

These rules should be written into a small project style guide and enforced on
`lib/std` by a lint included in the ordinary test workflow. Start warning-only
against an explicit baseline; make it gating after the existing library is
clean.

## Implementation constraint

Operator syntax is currently parser-desugared to the same call AST as a named
call, so a post-parse walker cannot always tell which spelling the author used.
The lint must either preserve written-form provenance (related to
[[diagnostics-name-the-written-form]]) or inspect the token/span window while
using resolved designation data to decide whether a replacement is valid.
A regex over names such as `add`/`Lt` is not acceptable: qualification,
shadowing, first-class uses, and multiple carriers make it lie.

The n-ary-call half is structurally visible and can land independently. Its
negative controls must retain intentional partial application and reject any
rewrite that would change which later argument participates in inference.

## Acceptance

- A documented standard-library style guide states the rules and exemptions.
- The lint identifies `f(a)(b)` when `f(a, b)` is definitionally the same call,
  while leaving meaningful partial application alone.
- The lint identifies direct calls to an in-scope designated operation in
  operator positions, without flagging first-class values, instance keys, or
  necessary structural spellings.
- The initial cleanup includes Nat, Int, Bool, List, and Logic motives/proofs.
- Generated fixtures are opt-in or exempt unless their owning generator adopts
  the same style contract.

## What it assumes from elsewhere

- **[[idiomatic-spelling-pass]]** established n-ary application as the preferred
  generated surface; this issue generalizes that decision to hand-written std.
- **[[stdlib-operator-spelling-locality]]** made designated notation available
  early enough for the rule to be actionable.

## Log

- 2026-08-19: Filed from the post-I-prime review. Both representative rewrites
  were checked against the current elaborator: n-ary calls spill across the
  curried signatures, and `<` resolves correctly at both Nat and Int inside the
  dependent motive. The remaining gap is consistency and feedback.
