---
title: Represent repeated inductive construction as saturated shared programs
status: open
labels: [kernel, inductives, conversion, performance, representation]
created: 2026-08-28
updated: 2026-09-09
---

Large canonical inductive values need not be materialized as one native node
per logical constructor. A one-hole constructor context can instead be a
shared straight-line program: `Run(context, NonZeroU64)` stores a bounded
repetition and `Compose(outer, inner)` retains construction history and DAG
sharing. Counts never become an unbounded host integer; adjacent runs merge
only when checked `u64` addition succeeds, and remain composed on overflow.

The representation is observational. Pattern matching exposes one ordinary
constructor and a compressed predecessor. A fold whose algebra is itself a
matching one-hole constructor context maps the whole program; an arbitrary
fold continues one logical step at a time under ordinary fuel. Shared program
identity is a positive conversion shortcut only; conversion does not perform
an unfueled structural program walk.

Nat is the first semantic customer because it has a kernel constructor. The
program layer itself is generic over the constructor-context identity.
Declared inductives lower to `Wf`, so applying the representation there needs
a separate design for recognizing a unary recursive `Supf` context through
its label, arity, child vector, motive, and dependent `elim_Wf` step. Do not
special-case generated constructor names.

## Acceptance

- Represent `Succ^(2^64)(Zero)` with saturated `u64` runs and with a depth-64
  shared composition program, without materializing the logical spine.
- Preserve the ordinary one-step `Zero`/`Succ` view in evaluation, conversion,
  `Vec`/`Fin`, shifting, and the syntax/value differential oracle.
- Map an exact `Succ(ih)` Nat algebra over either representation in work
  proportional to compressed size, while an arbitrary fold reaches
  `OutOfFuel` rather than returning a guessed result.
- Extend the same mechanism to unary recursive declared inductives through a
  constructor-shape rule, not a Nat or global-name rule.
- Attribute which useful consumers are context homomorphisms. In particular,
  recursively defined `Le` originally lay outside the unary-map fragment and
  must not be repaired by recognizing the name `Le`; its generic synchronous
  two-run algebra is now handled under [[nat-order-large-run-comparison]].

## What it assumes from elsewhere

- **[[bitvec-closed-reduction-cost]]** owns the concrete unary arithmetic
  failure. Assumed here only: exponentiation can produce the large constructor
  spine, while the `carry_add` proposition's recursive `Le` is the consumer
  that actually forces it. Merely inspecting `pow(2,64)`'s outer constructor
  is not a sufficient acceptance probe.
- **[[datarepr-separation]]** owns compiled runtime representations. Assumed
  here only: this semantic representation is kernel-time and does not select
  a program's runtime layout.

## Log

- 2026-09-09: The generalized run algebra landed
  ([[nat-run-algebra-primitives]]): any step that evaluates to successors
  and projections of the induction hypothesis — including `mul`'s
  `add(ih, a)` through the nested fold and `half`'s course-of-values
  window — is iterated over the program's DAG by exponentiation, with
  program-valued increments that compose past `u64` instead of declining.
  The synchronous fragment is likewise recognized by probing the algebra at
  `Succ x`, so `sub`, `min`, `max` join `Le`/`leb` without a spelling.

- 2026-09-07: Two more consumers attributed as context homomorphisms, from
  [[bitvec-ofnat-large-literals]]. The successor algebra `λ k ih. su^p ih`
  is now recognized at any `p ≥ 1`, not only `p = 1`: a saturated run's
  count is multiplied by `p` (so `twice` maps a run in constant work),
  declining to the ordinary step on a composed program or an overflowing
  count. And the mapped fold no longer leaves its tail pending: it is forced
  through a `NatRunTail` frame, and a run it returns is merged by
  `ContextProgram::append` (one saturated run when the counts add, composed
  otherwise). Before, `add(p, p)` on a literal was two fragments and
  `pow(2, k)` — `mul` is repeated `add` — a chain of `2^k` single-successor
  fragments that overflowed the native stack at `k = 20`; now `pow(2, 63)`
  is one run. Both fast folds also unfold a glued scrutinee (and the
  synchronous fold a glued right-hand counter) rather than stalling for
  conversion's outside δ-steps, which replay the pending spine each time —
  the cost that made a doubling chain under a literal consumer quartic in
  its length. The evaluator tests cover merge, scaling, and the decline; the
  glued cases are pinned at the library level in `lib_std_bitvec`.

- 2026-09-02: The first ordinary compact-literal producer exposed two
  compatibility omissions in certgen after landing. Its value reader still
  accepted only `Zero`/`Succ`, so the in-language signature checker failed on
  `su^1 ze`; independently, the reflection marker pass rejected a literal
  function body such as `fn seven() -> Nat { 7 }` before the code recursor
  could present its ordinary successor view. Both are repaired without unary
  expansion. `ContextProgram::repetition_count_up_to` computes an exact
  bounded size over the shared DAG, certgen consumes that count and resumes at
  the run tail, and `mark` preserves `NatLit` for the already-compatible code
  recursor.

  The wider audit found two more consumers of the same missing constructor
  view. `absurd`'s Nat no-confusion builder matched raw `Zero`/`Succ` syntax
  (breaking both its focused tests and the standard List law kit), and the
  route-2b cast-invariant test's deliberately exhaustive syntax walker had no
  compact-literal leaf. The former now uses the shared `nat_head` view; the
  latter explicitly treats a closed literal as a leaf.

  Why these escaped the producer round: its reported verification ran the
  kernel library, cache rails, elaborator **library** tests, the FunctionIR
  certificate generator and the new maximum-literal integration test. It did
  not run the separate certgen integration binaries, and no full
  `scripts/test` followed the cherry-pick. The maximum-literal rail proved
  production/reflexivity but exercised neither value readback nor reflected
  code, no-confusion, or the test-side structural audit. The first omission now
  has a zero-library-prefix unit regression in `certgen.rs`, so the same
  elaborator-library command catches compact and exponentially shared runs;
  certgen's existing `seven` acceptance continues to pin the reflection
  boundary. The final gate for this repair is the full suite, not the original
  focused set.

- 2026-09-01: Independently allocated but bisimilar value-program DAGs now
  compare and cancel in work proportional to unique node pairs. The walk is
  iterative, and retains every node named by its pointer-pair memo so allocator
  reuse cannot alias a key. It shares one explicit inspection budget with
  cursor descent. Conversion
  charges those inspections to its fuel; a synchronous fold reserves its
  ordinary reduction step, charges the program work, and returns `OutOfFuel`
  if the bound is insufficient. Thus neither a hostile near-match nor a
  genuinely different program can acquire an unfueled verdict.

  Rails cover shared identity, independently allocated depth-64 doubling
  DAGs, unequal residuals after an exponential common prefix, composed
  saturated runs, and a bounded hostile near-match. The independent-equality,
  conversion, and hostile controls each complete effectively instantly under
  a 128 MiB address-space limit and ten-second timeout. This is intentionally a
  sufficient DAG bisimulation plus prefix cursor, not a complete solver for
  arbitrary straight-line programs that denote the same context string with
  unrelated association and run boundaries; [[context-program-denotational-equivalence]]
  owns that larger compressed-string problem. Declared-inductive production
  remains the other open acceptance item here.

- 2026-08-31: [[nat-order-large-run-comparison]] added generic matching-prefix
  cancellation for context programs and recognized the exact two-input fold
  algebra whose successor/successor branch resumes the recursive result at
  both predecessors. This brings `Le` into a second, structurally justified
  fast fragment without naming it, while arbitrary folds retain ordinary fuel
  behavior. Nat conversion uses the same cancellation before exposing unary
  constructors. Declared-inductive production remained broader work for this
  issue; independently constructed bisimilar DAGs were completed above.

- 2026-08-31: Closed Nat literals now provide the first ordinary producer for
  the dormant value substrate. `Term::NatLit(u64)` is a compact internal form
  with the same one-step `Zero`/`Succ` observations as its constructor spine;
  evaluation sends it directly to one saturated `ContextProgram::Run`. This
  fixes representational allocation through `u64::MAX`, but does not pretend
  arbitrary folds are homomorphisms: the synchronized recursive `Le` consumer
  still overflows its native stack on huge nearby operands and remains owned
  by [[nat-order-large-run-comparison]]. Generic declared-inductive production
  and composed-program consumers remain open here.

- 2026-08-28: The representation substrate landed in the value domain.
  `ContextProgram<C>` has
  saturated runs, shared composition, and iterative one-step destruction.
  `Val::NatRun`
  presents the old successor view to conversion, `Vec`, `Fin`, shifting, and
  the evaluator differential oracle. An exact `Succ(ih)` eliminator maps the
  shared program without visiting logical nodes. Rails cover both two-run and
  depth-64 representations of `2^64`, a two-fuel homomorphic fold, a 32-fuel
  hostile fold, and independently wrapped values carrying one shared program.

  Two automatic-production experiments were deliberately not retained.
  Compressing every evaluated `Succ` spine made the x86 test roughly 1--2 s
  slower, while recognizing a run at `ElimNat` made it roughly 5 s slower.
  A `positive(pow(2,64)) = True` probe was also not a useful acceptance test:
  it only demanded the outer constructor. The forcing customer
  `carry_add(64, all_ones(64), one(64))` still reaches `OutOfFuel`, because its
  `Le` definition synchronously eliminates two counters one logical successor
  at a time. The current slice therefore supplies and tests the semantic
  representation, but intentionally has no general source-term producer yet.
  Finding a cheap production boundary, then extending it through `Wf`, remains
  the next work rather than hiding a regression in the evaluator's hot path.
  The retained, dormant substrate itself is neutral: two base-only x86 runs
  measured 48.82/25.40 and 48.97/25.61 s total/kernel, while an isolated build
  of unchanged `HEAD` in the same machine session measured 49.47/25.45 s.

  Verification: the focused kernel suite is green at 306 tests and
  `scripts/bench --check` accepts all 106 comparisons. A plain full run from a
  fresh target built and ran the current 38-test kernel binary; 2,167 tests
  passed. Its only failures were the two pre-existing Omega division rails,
  followed by the general Omega binary's kill. They reproduce without this
  working tree and are reopened under [[omega-div-mod-expansion]]; x86,
  BitVec, IR, certgen, and every kernel target passed in the same run.
