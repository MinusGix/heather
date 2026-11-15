---
title: Add function-scoped Result propagation with explicit success values
status: closed
labels: [frontend,stdlib,elaboration,syntax]
created: 2026-09-14
updated: 2026-09-28
---

Own the Result slice of [[prelude-option-and-friends]]: a standard Result
module, postfix `?`, and a runnable parser client. The agreed scope is the
nearest function or lambda, with ordinary nested blocks transparent and
success values explicitly wrapped in Ok. No implicit error conversion.

## Acceptance

- Ordinary library-defined Result, map, and_then, map_err, unwrap_or.
- Postfix propagation composes with calls, branches, bindings, and nested
  Results, without changing prefix proof goals.
- Preserve lexical scope and first-error order. A lambda is a separate boundary.
- Show a real parser and recursive collection, with open-input equivalence
  to handwritten matches, closed computations, and negative controls.
- Keep elaboration and ordinary kernel checking as the only proof boundary.
- Update Tree-sitter/Zed syntax support and run the full suite.

## Implementation

`docs/language/result-propagation-design.md` records the semantics and lowering.
`crates/syntax/src/try_lower.rs` lowers to the library's ordinary map/and_then.
Nested scopes package a local success value before passing it to an outer
continuation; continuation code is never moved under a written inner binder.
The application solver can infer the result of a generated propagation
callback once its input domain is fully solved. That narrow fallback does
not change ordinary source-lambda inference or introduce a kernel rule.

The runnable customer is `docs/showcase/result_parser.hthr`: two-number token
parsing, specific errors, trailing-input rejection, a handwritten-match
reference, and recursive collection. Focused acceptance also covers open
types, lexical shadowing, nested lambda boundaries, fields, vector indexing,
collection construction, and named arguments evaluated in written order.

## Remaining ownership

- [[prelude-option-and-friends]] retains Option chaining and any future
  generic propagation protocol.
- [[result-propagation-dependent-motives]] owns non-tail written dependent
  motives. The current parser declines these explicitly.
- No implicit success wrapping or automatic error conversion is promised.

## Validation

Focused acceptance: 6 passed; syntax unit/integration suite: 125 passed.
Tree-sitter corpus tests (8), positive fixtures, the new parser example, and
all five query compilations pass. Its whole-library scan retains the
pre-existing [[tree-sitter-match-code-scrutinee]] failure, reproduced with
HEAD's original parser in an isolated temporary checkout.

The kernel timing gate reports 12 Nat comparisons on an idle rerun;
[[kernel-benchmark-nat-baseline-drift]] owns that unchanged-kernel baseline
investigation. The baseline was not rewritten. Final plain `scripts/test`: **2,640 passed, 0 failed, 5 ignored**
(`/tmp/result-clean-final-suite.log`, 246 s wall). Focused negative controls
also reject unknown and duplicate constructor arguments through the map
optimization; `?` does not erase written named arguments. The final guard
filters private callback syntax before type substitution.

`scripts/issue check` and `git diff --check` pass. No kernel source, benchmark
baseline, or existing library theorem was changed.
