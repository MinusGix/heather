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
- 2026-08-29: Stage 1 committed as `1ebe886` (`elab: define semantic module
  image boundary`). Stage 2a now makes image capture, restore, and transaction
  checkpoints share a single immutable `CommittedWorld` pointer. The world's
  eight registries are independently shared and detach on first mutation, so
  an ordinary theorem suffix does not clone untouched type, trait,
  representation, or meta-program tables. The dynamic stored-syntax
  resolution stack moved out of `Names` and into each `Elaborator`; otherwise
  sharing the name registry would have allowed one fork's temporary scope to
  contaminate another. Focused image and transaction tests pass, including an
  ownership pin which proves two forks initially share the world and that an
  ordinary declaration detaches the world while retaining the untouched
  registry allocations. This is deliberately named Stage 2a: first mutation
  still copies a whole affected registry (notably `Names`), so key-level
  base-plus-delta maps and growth measurements remain Stage 2b.
- 2026-08-29: The existing release `corpus/prelude` benchmark gives the first
  direct ownership number: cloning a prelude world fell from its recorded
  6.873 microsecond baseline to 89 nanoseconds (about 77x), while rebuilding
  the prelude measured 205 microseconds. This isolates the O(1) fork win. It
  does not measure or absolve first-write registry detachment; Stage 2b needs
  a growth fixture for snapshot, lookup, and the first suffix commit.
- 2026-08-29: Stage 2a full verification is green: 2,171 passed / 0 failed
  across 150 binaries in 612 seconds wall. That includes all five Omega
  acceptance shards, x86_64, representation generation/access, datarepr,
  certgen's generated-bundle rollback paths, semantic-image equivalence, and
  the new ownership pin.
- 2026-08-29: Stage 2b first registry implemented. `Names` now holds sealed,
  immutable module layers plus one current-module delta. A semantic snapshot
  shares and seals the current layer, so a restored suffix's first name commit
  mutates an empty delta instead of copying every imported name, surface AST,
  absolute-position index, and member base. Resolution iterates layers without
  a combined allocation and preserves original declaration order for
  ambiguity diagnostics; repeated chunks of the same module stay in one layer
  so depth tracks modules, not REPL submissions. A 64-module ownership test
  pins sharing, old-name visibility, and suffix isolation; all 39 module tests
  and the semantic-image/transaction tests pass.

  The release prelude benchmark now separates the boundary: world clone 87
  ns, fresh image fork 258 ns, and fork plus first ordinary declaration 7.49
  microseconds, versus 210 microseconds to rebuild the prelude. These new
  benchmark cases remain untracked until a final stable run records the
  baseline. Whole-table COW remains in types, traits, representations,
  provenance, and meta-programs; Ψ retains its binding-vector COW.
- 2026-08-29: Full Stage 2b/name-layer verification: 2,172 passed / 0 failed
  across 150 binaries in 602 seconds wall. Aggregate reported target time was
  1,798.65 seconds versus 1,826.52 immediately before the layering change.
  The comparable large targets were flat-to-faster: Omega core 232.39 ->
  233.67 s, div/mod 239.29 -> 237.98, div/mod scaling 234.36 -> 226.25,
  logic 181.50 -> 184.87, reconstruction 176.65 -> 164.91, and x86_64
  104.53 -> 102.87. This is not a controlled benchmark claim, but it rules
  out a material real-closure lookup penalty on the ordinary rail.
- 2026-08-29: Stage 2b Ψ slice implemented. `GlobalCtx`'s flat
  `Rc<Vec<GlobalBinding>>` became a logical binding sequence backed by sealed
  fixed-width persistent chunks and one at-most-63-binding COW tail. Semantic
  images share both Ψ views, so a restored append copies at most that tail.
  This fixes a
  stronger repeated-copy shape too: `delta_psi` shares Ψ after each ordinary
  declaration, so flat COW could copy the growing suffix again at the next
  append; the new bound is 64 shallow bindings. Absolute lookup is O(1) by
  fixed-width chunk index, iteration preserves outermost-first order, and the
  conversion memo keys the logical context's allocation identity rather than
  one flat vector allocation.

  A representation-independence failure was caught immediately by the exact
  semantic-image hash: derived `Debug` exposed chunk boundaries, giving equal
  Ψ values different cache identities. `GlobalBindings` now renders only its
  logical sequence; semantic-image equivalence and the determinism golden are
  green. A kernel ownership test pins sealed-chunk sharing, bounded empty-tail
  suffixes, lookup/order, isolation, and equality with a flat construction.
  The full kernel benchmark gate reports 106 comparisons within thresholds;
  several checking cases improved because `check_global_ctx` now grows one
  persistent prefix instead of rebuilding every prefix slice quadratically.
  The focused release frontend figures after the representation change were
  88 ns world clone, 385 ns image fork, 8.33 microseconds through the first
  declaration, and 222 microseconds to rebuild the prelude. The fork movement
  from 258 ns is below a microsecond but will be remeasured with the full
  frontend gate before any baseline decision.

  The first implementation allowed semantic snapshots to seal partial chunks
  and therefore needed a binary search over chunk ends. Its initial concurrent
  acceptance run moved several targets by 10--15% (x86_64 102.87 -> 116.24 s),
  so it was stopped and replaced rather than accepted on microbenchmarks alone.
  A later fixed-width full run showed the host/scheduling contribution was
  large—x86_64 was still 115.42 s concurrently but 96.51 s alone—so the first
  movement is not attributed wholly to binary search. Fixed-width chunks are
  retained on the stronger design argument: arithmetic O(1) lookup with the
  same bounded-copy guarantee.
- 2026-08-29: Final fixed-width Ψ verification: 2,179 passed / 0 failed across
  150 binaries in 645 seconds wall. The host was slower across unrelated large
  targets (aggregate reported target time 1,925.07 s), so this run is treated
  as correctness evidence, not a regression measurement. Performance evidence
  is the isolated x86_64 96.51 s run and the kernel gate's 106 comparisons
  within thresholds; no benchmark baseline was re-recorded.
- 2026-08-29: Post-Ψ priorities recorded in the design. The immediate Stage 2b
  slice is registry-specific growth/first-write attribution followed by
  provenance layering: provenance is written by ordinary declarations and its
  dependency paths make whole-table detachment less shallow than the nominal
  indexes. Types follow if measured; traits need lookup indexes as part of its
  design rather than mechanical layering. After the costly registries are
  bounded, Stage 3 dependency replay has greater leverage than polishing tiny
  tables. This track is explicitly separate from theorem-scale x86/Omega
  performance, which requires conversion/evaluation attribution and kernel
  work; sub-microsecond image operations cannot explain those targets.
