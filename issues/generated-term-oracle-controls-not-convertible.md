---
title: Generated-term oracle controls are not convertible on master
status: closed
labels: [kernel,conversion,elaboration,testing,regression]
created: 2026-08-28
updated: 2026-09-06
---

Three exact-term controls began failing individually with `NotConvertible`:

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
were also reverted.

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
- 2026-08-28: **Cause established; repair remains open.** Automated bisection
  from the fold template's landing commit identified `dd923db` (`kernel: avoid
  redundant open bitvector conversion`) as the first bad revision. That optimization
  changed neutral application comparison from the annotation-directed rule to
  a single Π inferred from the left function spine. The fast rule is sound on
  its successful path, but incomplete: with the dependent substitutions
  produced by the in-language fold/tabulate templates, its left-biased Π can
  be stuck in a spelling that cannot check the right argument. The block test
  supplies the minimal behavioral witness: its two root terms are structurally
  identical, yet their applications reached the same refusal.

  Restoring the original annotation-directed rule makes all three controls
  pass, proving the regression is in that optimization rather than in the
  generators. It is not an acceptable final repair: using stored codomains
  throughout makes the complete x86 target exceed its existing 300-second
  rail. A simple `NotConvertible` fallback also restores the controls and
  preserves focused x86 performance, but failed probes consume enough fuel to
  make `ir_pass_fuel` fail. Rolling back only that speculative fuel makes the
  three controls and IR pass, but the complete x86 target then aborts after
  85 seconds while requesting a 500 MiB allocation. The shallow scoped-type
  identity predicate cannot select the safe route either: the bad tabulate
  case is identity-equal until dependent instantiation exposes the spelling
  difference.

  No experimental kernel change is retained. A repair needs a canonical or
  coherently respelled inferred Π result, or another way to preserve the
  original application judgment without recursively expanding its stored
  codomains. Backtracking/refunding inside the trusted checker is explicitly
  not accepted by this investigation. The block control's Ψ was separately
  corrected to be the context that owns its terms; this is test hygiene and
  does not alter the reproduced failure.
- 2026-08-28: Corrected the performance interpretation with exact-test phase
  measurements. The unchanged inferred rule checks the x86 module in 42.80 s
  (26.26 s measured kernel, 16.54 s frontend) and finishes the isolated module
  test in 49.83 s. Restoring the original stored-annotation rule checks the
  module in 62.40 s (32.61 s kernel, 29.79 s frontend) and finishes the test in
  74.93 s: a real 46% module regression, but not an individually unusable
  check. More importantly, the unchanged five-test x86 binary already reaches
  the runner's 303-second test timeout after four tests pass. Its aggregate
  rail repeats the entire dependency stack and x86 module five times under a
  serializing mutex, so crossing that rail does not by itself reject the
  correctness-restoring rule. Judge future candidates on exact consumers and
  fix or split the aggregate harness independently.
- 2026-08-28: **Fixed and closed.** Restored the ch. 06 annotation-directed
  application rule, with no fallback, fuel change, or new trusted mechanism.
  Fold, tabulate, and the block control pass, as do the sibling map (3) and nth
  (5) suites, the kernel suite (299), BitVec (7), and the default-fuel IR rail.
  The x86 harness now elaborates its dependency stack and module once, then
  runs each formerly separate consumer against an isolated cheap clone of that
  base. This preserves negative-test isolation and cuts the complete correct-
  rule x86 suite from an incomplete 303-second aggregate to 146.34 s. Its base
  module elaboration is 60.40 s (31.15 s measured kernel), consistent with the
  exact A/B measurement. The pragmatic follow-up is to reduce stored
  annotation representation/instantiation cost; a paired/common neutral type
  remains a possible theoretical redesign, not a prerequisite for correctness.
- 2026-08-28: A follow-on metrics round retained the restored rule and added a
  narrower identity win: equal annotation bodies captured over pointwise-
  identical arena values are the same closure denotation even when their
  environment nodes were rebuilt. This raises x86 base-module annotation fast
  hits from 13.8% to 25.0% without helping—or bypassing—any fold/tabulate
  comparison. The remaining cost is tracked by
  [[application-annotation-sharing-cost]].
- 2026-09-06: Diagnosis corrected (2026-09-06): the fold/tabulate/block refusals under the left-inferred rule were a test-harness bug, not an incompleteness. in_language_fold/tabulate/map/nth and let_and_blocks called conv_term with the elaborator's full Ψ while comparing the LAST binding's body, whose global indices are scoped over the prefix — index 0 resolved to the binding itself (probe: Π(Vec(Nat;3)). Nat) instead of add, so any rule that reads a head's declared type from Ψ refused; the annotation-directed rule never does and passed. The tests now compare in the owning prefix (owning_psi), and the typed application rule is in (docs in crates/kernel/DESIGN.md, Algorithms).
