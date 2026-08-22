---
title: "Lint unused constructor fields and induction hypotheses"
status: closed
labels: [tooling,lint,frontend,patterns,proofs,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

An explicitly named constructor field that is never used should normally be
written `_`. An unused generated induction-hypothesis binder is stronger
evidence: the branch requested recursive elimination but did not consume its
recursive result, often revealing a proof that only needs case analysis.

Keep this rule narrower than a general unused-variable lint. Constant
functions, theorem parameters, and deliberately retained names in signatures
are ordinary mathematical/programming style and would make an unsuppressible
default warning noisy. This issue owns binders introduced by match patterns and
the recursive hypotheses attached to them.

Use scope-aware binding identities or an equivalent traversal, not name-text
search: nested lambdas may shadow a field name, and uses in local annotations,
`on` clauses, nested motives, or qualified structures still count.

## Acceptance

- Unused constructor payload binders receive a `_` suggestion when that syntax
  preserves the pattern's meaning.
- Unused induction hypotheses receive a distinct message explaining that
  recursive elimination may be unnecessary.
- Shadowing, nested binders, local types, motives, goal discharges, and
  argument slots cannot create false uses or false non-uses.
- Ordinary declaration parameters and intentional constant functions remain
  outside the rule.
- Generated pattern levels and compiler-invented binders never warn.

## What it assumes from elsewhere

- [[lint-roadmap]] owns rollout policy. This rule targets the conservative
  default only after the induction-hypothesis controls are clean.

## Log

- 2026-08-22: Filed from the lint review as a deliberately scoped alternative
  to a language-wide unused-variable warning.
- 2026-08-22: Implemented `unused-pattern-binder` with lexical binding
  identities across lambdas, locals, nested matches, annotations, and `on`
  clauses. Payloads carry exact `_` fixes; explicit Nat induction hypotheses
  get a distinct case-analysis message. Generated/if-lowered binders and dead
  arms are suppressed. The stdlib census applied 99 safe fixes (92 initially,
  then seven exposed by motive cleanup) and now reports zero findings.
