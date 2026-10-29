---
title: Stop resolving the CollectionLiteral dictionary afresh at every list literal
status: open
labels: [elaboration,performance,traits]
area: language
created: 2026-10-29
updated: 2026-10-29
---

Found by the 2026-10-29 cold-checking profile ([[native-tool-test-cold-certificate-rail]]'s
round; gdb stack samples of `lib/_tests/std/algebra`, the slowest gate folder
cold). After character literals stopped resolving once per character (same
round, `DeclAttempt::char_literals`), the largest elaborator share left in
that folder is instance resolution, and the largest single caller of it is
`check_collection_literal` (`crates/elab/src/lib.rs`): every `[…]` resolves
`CollectionLiteral<C>(n)` afresh, projects `element` and `fromLiteral` out of
the dictionary, normalizes the element, checks the vector, converts the
result type to the carrier, and normalizes the application. Nothing is shared
between two literals of one declaration, even at the same carrier.

`resolve_goal` has no memo at all (`crates/elab/src/resolve.rs`); each call
is a registry search plus a kernel check of the candidate.

## Directions

- The length is a value parameter of the goal, so two literals of different
  lengths are different goals. If the library's instances are all
  `∀ n`, the length-independent half (the resolved dictionary at a variable
  length, its `element`) can be computed once per (carrier, context,
  Ψ scope) in a declaration and instantiated per literal, the way
  `DeclAttempt::instance_matches` keys its answers.
- More generally, a per-declaration memo of `resolve_goal`'s successes keyed
  by the goal type (structurally), the context and the Ψ scope. Resolution
  can read local hypotheses, so the context key has to say which entries it
  saw, not only how many — the kernel's `CtxEntriesIdentity` is the shape,
  but it is crate-private.

## Done when

The per-literal cost of a collection literal at a carrier already used in the
declaration is attributed, and either no longer pays a resolution or the
reason it must is written here.
