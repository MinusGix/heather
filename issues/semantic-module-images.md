---
title: Load checked semantic module images without re-elaboration
status: open
labels: [tooling,elaboration,performance,caching,design]
created: 2026-08-29
updated: 2026-08-29
---

The declaration-verdict cache skips only the final kernel gate. Serious
standard-library closures now spend most of their warm time reconstructing
the semantic world before reaching that gate: the 573-declaration Omega
prefix takes roughly 173 seconds both cold (570 declarations checked) and
warm (573 cache hits). Splitting its acceptance matrix restores the process
rail but pays that prefix in five binaries and does not scale to a compiler,
larger architecture models, or proof-heavy downstream projects.

Implement `docs/semantic-module-images-design.md`: first make the complete
committed-state boundary an explicit in-memory image with isolated suffix
forks, then freeze per-module deltas, persist them under source/dependency and
semantic fingerprints, and load them without parsing or elaborating unchanged
source. The first persistent version rechecks imported kernel bindings; a
disk artifact is acceleration data, not a proof verdict.

## Acceptance

- An in-memory image contains every committed fact and no transient attempt,
  diagnostic, report, configuration, or gate state.
- Two suffixes forked from one image cannot observe each other's commits.
- Elaborating a downstream module against a restored image produces exactly
  the same kernel context and semantic lookup behavior as elaborating the
  complete source closure afresh.
- A persistent module image has explicit format, elaborator-semantics, kernel-
  semantics, source, and ordered dependency-interface identities.
- Loading an untrusted persistent image rechecks every imported kernel
  binding before exposing any frontend metadata.
- The warm Omega prefix and one unrelated standard-library closure are
  measured; unchanged dependency loading should be seconds rather than
  minutes and generated/mutated suffixes remain freshly kernel-checked.

## What it assumes from elsewhere

- **[[parallel-checking-and-caching]]** owns interface hashes, proof opacity,
  the trust ladder, and the eventual resident shared-telescope architecture.
- **[[integration-test-prefix-reelaboration]]** owns the current harness
  symptom and pragmatic Omega sharding.
- **[[warm-path-rewalks-unchanged-declarations]]** owns avoiding repeated
  declaration hashing after semantic reconstruction is gone.
- **[[application-annotation-sharing-cost]]** owns the cost of genuinely new
  x86 declarations; module images remove unchanged dependency work, not that
  root-module cost.

## Log

- 2026-08-29: Design started after the Omega suite established the phase
  inversion. Cache v1 was built for a kernel-dominated workload; Omega's cold
  and warm prefix times are equal within noise, so parsing/elaboration/world
  reconstruction now dominate. First implementation slice is deliberately
  in-memory and untrusted-boundary-neutral: expose and test the committed
  semantic image before choosing a byte encoding.
- 2026-08-29: Stage 1 implemented in the working tree. `SemanticImage` promotes
  the existing transaction checkpoint's eight committed stores to a public,
  opaque process-local boundary; `elaborator()` restores them around fresh
  transient state and never inherits diagnostics, Omega reports, metrics,
  item timings, lint policy, fuel bookkeeping, or a cache gate. Focused tests
  establish byte-identical downstream Ψ versus a fresh source closure,
  independent sibling suffix commits, whole-bundle rollback after failure,
  stored generic constructor use after restoration, and empty diagnostic/
  instrumentation history.

  The same slice added opt-in structured per-surface-item attribution and
  wired the Omega fixture to report it. Warm reconstruction measured 154.80
  seconds. Dependencies through `int` cost about 1.48 seconds; `omega.hthr`
  alone cost 136.86 seconds, all frontend and zero final kernel gate. Ten
  CutSat support theorems account for about 135.7 seconds: `cutsat_left_cut`
  55.09, `cutsat_right_cut` 31.67, the two remainder bounds 13.21/10.28,
  cancel-middle 6.49, remainder-gap 5.61, the two gap-nonnegative lemmas
  5.25/2.09, and lower/upper bound 4.31/1.68. The image target is therefore
  correctly placed: unchanged semantic import can remove nearly the entire
  prefix, while these declarations remain the profile for edits to Omega
  itself.
- 2026-08-29: Verification: focused semantic-image tests 3/3; full ordinary
  rail 2,170 passed / 0 failed across 150 binaries in 568 seconds wall. The
  frontend and kernel benchmark runs retained every declared scaling band but
  did not pass their absolute-time comparison on this noisy desktop run:
  untouched kernel phases moved 1.6--3.2x during the frontend gate, while the
  kernel gate was mostly 0.7--0.8x faster and flagged one 1.36x mirror point.
  No baseline was re-recorded and those contradictory absolute movements are
  not attributed to this change.
