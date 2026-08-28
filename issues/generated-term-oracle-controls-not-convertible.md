---
title: Generated-term oracle controls are not convertible on master
status: open
labels: [kernel,conversion,elaboration,testing,regression]
created: 2026-08-28
updated: 2026-08-28
---

Three exact-term controls currently fail individually on `master` with
`NotConvertible`:

```text
in_language_fold::hook_output_is_convertible_with_the_rust_oracle
in_language_tabulate::hook_output_is_convertible_with_the_rust_oracle
let_and_blocks::a_block_is_the_program_without_it
```

The first two compare an in-language generated vector operation with the Rust
schema oracle. The third is sharper still: it asserts the two elaborated terms
are structurally equal immediately before conversion rejects them. These are
not ordinary negative controls; their test names, comments, and assertions all
require conversion success.

They were discovered while validating an unrelated implicit-inference probe.
That probe was reverted completely and all three failures reproduced. As an
additional isolation check, disabling both additions in the recent gate-local
conversion reuse path — positive memo hits and the syntactic-reflexivity fast
path — did not change either the fold or block result; those temporary edits
were also reverted. The cause is therefore not established and must not be
assigned to either experiment.

## Acceptance

- Establish the first bad revision or otherwise identify the shared conversion
  boundary. Do not weaken or delete the oracle comparisons.
- Explain why `let_and_blocks` can reject two terms after its structural
  equality assertion succeeds; this should provide the smallest reproducer.
- Restore all three positive controls without changing their fuel merely to
  hide the mismatch.
- Run the complete elaborator suite, including the sibling map/nth generated
  artifact controls, and record whether any other positive oracle is affected.
- If the terms are genuinely convertible but the algorithm refuses them, add
  the reduced kernel-level reproducer beside the conversion tests.

## What it assumes from elsewhere

- **[[implicit-value-inference-through-constructor-fields]]** discovered these
  failures during validation but does not own them. Assumed here: no proposed
  constructor-unification change is present.
- **[[kernel-gate-conversion-reuse]]** owns the recent cache. Its two operative
  paths were disabled independently without changing the failures, so this
  issue assumes neither guilt nor innocence for the rest of that round.

## Log

- 2026-08-28: Filed after each failure reproduced in isolation with a clean
  elaborator/unifier diff. The current working x86 cleanup and generic lookup
  test do not touch any of the failing paths.
