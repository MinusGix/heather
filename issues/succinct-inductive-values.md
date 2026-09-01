---
title: Represent repeated inductive construction as saturated shared programs
status: open
labels: [kernel, inductives, conversion, performance, representation]
created: 2026-08-28
updated: 2026-08-28
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
