---
title: Load checked semantic module images without re-elaboration
status: open
labels: [tooling,elaboration,performance,caching,design]
created: 2026-08-29
updated: 2026-08-30
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
- 2026-08-29: The first registry-specific growth family confirmed the
  provenance target. Before conversion, one fixed ordinary suffix declaration
  grew 11.15 -> 19.45 -> 42.90 -> 116.19 microseconds over 16/64/256/1,024
  imported declarations (slope 0.56). `Provenance` now seals its current
  dependency map into an immutable shared image layer and starts the suffix
  empty; entries are `Rc`-shared and lookup/report ordering remains logical
  across layers. The same family is now 9.90 -> 10.49 -> 10.51 -> 10.06
  microseconds, slope 0.00, an approximately 11.5x reduction at 1,024. A new
  ownership/transitive-path test pins prefix sharing and suffix isolation;
  public provenance, image equivalence, determinism, transaction, and
  benchmark-smoke tests are green. The new family is not yet a recorded
  baseline. The broad fast rail is also green: 2,051 passed / 0 failed across
  150 binaries (plus serial documentation tests), including every Omega shard
  and x86_64; 772 seconds wall under the two-worker acceptance runner.
- 2026-08-29: The nominal-type first-write probe also found a real, smaller
  imported-prefix cost: 14.27 -> 18.41 -> 29.42 -> 64.14 microseconds over
  4/16/64/256 imported one-constructor types (slope 0.36). `Types` now seals
  its correlated name/tag/constructor/record-field indexes as one immutable
  layer, while `GenDefs` seals its paired forward/reverse and guard indexes in
  a sibling layer; the suffix starts both empty without breaking atomic
  registration. After conversion the family reads 14.98 -> 20.00 -> 23.26 ->
  29.60 microseconds (slope 0.16, inside the flatness band), about 2.2x faster
  at 256 types. The remaining mild growth stays visible rather than being
  described as zero: nominal tags and generated work still observe the larger
  world. Ownership/isolation plus 110 focused nominal, generated-definition,
  image, determinism, rollback, provenance, and benchmark tests are green.
  The subsequent broad fast rail is green as well: 2,052 passed / 0 failed
  across 150 binaries plus serial documentation tests, including all five
  Omega shards and x86_64; 548 seconds wall with three acceptance workers.
- 2026-08-30: Stage 3 is now the active target. Remaining trait,
  representation, and meta-program storage rewrites are explicitly deferred
  unless replay or resolution measurements name them. `ModuleDelta` will be a
  logical ordered commit journal, not a diff or serialization of live registry
  maps. Replay quarantines metadata, checks the Ψ extension sequentially, and
  publishes only an atomic fully validated candidate. The first kernel seam is
  implemented as `check_global_ctx_extension`: it checks an ordered suffix
  against a presupposed well-formed prefix without rechecking dependencies;
  the existing whole-context checker now shares exactly the same binding
  routine.
- 2026-08-30: Stage 3's in-memory semantic delta and safe replay boundary are
  implemented. Extraction journals logical operations at the existing
  infallible commit points rather than diffing registry storage: ordinary and
  generated globals, names/nominal types, traits and derived dictionaries,
  repr/impl obligations and access paths, provenance, and meta-program slots.
  Whole-module extraction is atomic, and nested generated-bundle rollback
  truncates the journal together with the committed-world pointer.

  Replay requires both the loader-supplied ordered dependency identity and an
  equal logical Ψ prefix; this deliberately accepts an independently rebuilt
  equivalent world and uses no allocation identity. It rechecks the suffix in
  order with `check_global_ctx_extension`, keeps metadata quarantined in a
  private candidate world, then publishes one committed pointer. Differential
  tests prove equal Ψ and downstream elaboration versus source, dependency
  mismatch and failed extraction preserve the target, a deliberately
  corrupted stored body is kernel-refused without leaking its name, and a
  combined registry fixture exercises inductives/generated definitions,
  classes, instances, designations, meta definitions, reprs, and designed
  access paths.

  Release measurements: the tracked frontend fixture's real `logic.hthr`
  module is 10.25 ms from source versus 1.62 ms through safe replay (6.3x).
  The manual ignored Omega closure probe builds and journals nine modules in
  78.119 s, then rechecks/replays all 577 bindings in 0.376 s (207.5x): logic
  2 ms, bool 4, nat 4, option/pair below 1, list 48, algebra 75, int 150, and
  omega 92. The full safe path is already below half a second, so this run
  names no trait/representation/meta COW rewrite as the next target. Stage 4's
  bounded persistent encoding and loader identities now have vastly more
  leverage than tuning those unmeasured tables.
- 2026-08-30: Final Stage 3 verification is green: 2,188 passed / 0 failed /
  1 intentionally ignored across 151 binaries plus serial documentation tests
  in 675 seconds wall. The ignored target is the manual Omega source/replay
  benchmark above; it passed separately in release mode. The ordinary rail
  includes all five Omega acceptance shards, x86_64, class/operator resolution,
  repr generation/access, datarepr and obligation records, meta templates,
  generated-term mutation controls, semantic-image differential tests, and the
  new kernel-extension judgment.
- 2026-08-30: Stage 3 hardening centralized durable frontend mutations behind
  semantic commit operations shared by source elaboration and replay. Journal
  payloads are now built lazily, so inactive extraction adds no unconditional
  cloning. A source-tree tripwire rejects known direct registry commits outside
  that seam; it is intentionally defense in depth rather than a claim that a
  textual audit can replace schema review.

  New observable differential fixtures force canonical derived resolution,
  meta-slot execution, repr/impl access, and obligation lookup from a consumer
  module, then require exact source/replay Ψ. The repr fixture caught an actual
  completeness hole: generated-definition bindings replayed, but their
  type-code guard, recursive-shape slots, and family-level indexes did not.
  The result still kernel-checked because replay unfolded to a convertible
  structural type, but it lost the compact annotation spelling and generated
  a different, much larger term. These correlated indexes now have explicit
  events and use the same commit seam. Focused verification is green: 9/9
  semantic-image integration tests and 3/3 replay-boundary unit tests.

  Stage 4's documented risks are now explicit: hostile bytes need total,
  allocation-budgeted decoding and cross-reference validation; metadata stays
  quarantined through full suffix checking; dependency identity is computed by
  the loader rather than trusted from the artifact; v1 absolute positions
  require the exact ordered prefix; and cache publication is atomic. The next
  implementation slice is the bounded versioned codec, not further
  sub-microsecond registry tuning.

  Broad fast verification exercised all 151 binaries. It produced 2,059
  passes, zero assertion failures, and one ignored manual benchmark; x86_64,
  Omega logic/reconstruction, every repr/datarepr/access suite, the elaborator
  unit suite, and the semantic-image fixture all passed. The aggregate run is
  nevertheless recorded as incomplete: under three-way contention, Omega
  core and the two division/modulus binaries reached the harness's fixed
  300-CPU-second limit and were killed. Omega core then passed serially in
  282.42 seconds. `omega_div_mod` still reached the rail serially at 305
  seconds without an assertion result; its scaling sibling was not redundantly
  rerun after showing the same broad-run boundary. The previous green full
  run measured these targets below the rail, so this is resource evidence on
  a slower host, not a green claim and not a semantic failure.
- 2026-08-30: Stage 4a's semantic wire codec is implemented. `ModuleDelta`
  now has a deterministic versioned encoding and a bounded, inert decoder
  covering the complete kernel syntax, semantically retained surface AST and
  all sixteen registry-event families. Dependency Ψ is not serialized: the
  image carries its expected length and ordered interface identities, while
  the caller supplies the already accepted logical prefix.

  Decode rejects unknown tags, malformed scalar encodings, invalid UTF-8,
  truncation/trailing bytes, over-budget bytes/strings/sequences/nodes/depth,
  dangling suffix positions, mismatched correlated tables and duplicate
  registry operations. Replay now preflights decoded events against dependency
  registries before calling infallible commit operations, retaining the
  no-panic quarantine boundary for hostile artifacts. Deterministic rebuild,
  byte-identical decode/re-encode, every-prefix truncation, hostile-budget,
  dangling-reference and registry-rich source/decode/replay tests are green.
  No filesystem policy has leaked into the elaborator codec.
- 2026-08-30: the Stage 4b loader/cache baseline is implemented. A build-time
  fingerprint now covers the syntax, elaborator and kernel sources; the
  content-addressed key also covers module name, exact source digest and the
  complete ordered accepted-module identity prefix. The CLI loads bounded
  artifacts, decodes them inertly against its live Ψ, rechecks the complete
  suffix through the kernel, and only then publishes the candidate semantic
  world. Misses, corruption and replay rejection rebuild through a new
  journaled form of the ordinary multi-error checker, preserving the CLI's
  diagnostic recovery rather than replacing it with first-error atomic
  elaboration. Successful warning-free modules publish through unique
  temporary siblings and atomic rename; corrupt-artifact and round-trip tests
  cover the storage boundary.

  Two deliberate performance limitations remain. V1's resulting module
  identity is conservatively the hash of the complete semantic artifact,
  rather than a projection of only facts observable by dependents, so an
  opaque proof edit invalidates downstream images. And warnings are not yet
  encoded: warning-producing modules are therefore never published, keeping
  cache hits observationally honest at the cost of reuse. Both are explicit
  follow-up slices, not trust holes.
