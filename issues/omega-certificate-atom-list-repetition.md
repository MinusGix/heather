---
title: omega certificates spell their atom list at every use; bind it once
status: closed
labels: [omega,performance,proofs]
created: 2026-09-26
updated: 2026-09-28
---

`omega`'s certificate for a small goal (five Nat facts, six atoms) is 203 KB
of source. It spells its atom list, `[OfNat(sv), OfNat(r), …, OfNat(b)]`, 177
times: inside every `omega::basis(i, atoms)`, `zeros(atoms)`, `dot(row,
atoms)` and lemma argument. Measured 2026-09-26 at width 1:

- per kernel check, `Nil` costs ~43 steps, each `Cons` ~85, an Int literal
  ~44, so this list costs ~820 steps per copy;
- 177 copies are ~145k of the item's 152k kernel steps;
- the certificate has 4,199 `list::Cons` and 868 lists in all, and the
  elaborator parses and elaborates all 203 KB.

An identity lemma applied to *variable* lists costs 0 kernel steps; applied to
literal ones, ~3k.

## Proposed shape

Bind the atoms once, as a variable. The certificate becomes
`(λ (A: List<Int>) (e₀: nth0(0, A) = OfNat(x₀)) … => cert)(atoms, refl, …)`,
so the literal list is checked once and each `eᵢ` by one computation. Inside,
rows are spelled as literal coefficient lists (not `basis(i, A)` or
`zeros(A)`, which would be stuck on a variable `A`), `dot(row, A)` stays
symbolic, and an atom enters only through `normalize_atom(i, A)` transported
along `eᵢ`. Combinations still compute on literal rows. Expected: kernel cost
per certificate proportional to its steps, not to steps × atoms; source a
fraction of the size.

## Acceptance

- The measurements above drop by an order of magnitude on the same goal, and
  `scripts/perf ab` over the omega-heavy corpus shows the whole-workload total
  moving.
- Every omega suite member passes unchanged (splits, cutsat, division atoms,
  wide constants).

## What it assumes from elsewhere

- **[[bv-omega-check-cost]]** found this. `bv_omega`'s per-call overhead is
  mostly `omega` certificates.

## Log

- 2026-09-26: Premise revised before implementation. Binding the atom list once does not pay
  by itself. With `A` a variable, `basis(i, A)` and `zeros(A)` are stuck, so the
  rows must be literal coefficient lists, and a literal row of m Int
  coefficients costs the kernel about what the atom list does. That would trade
  177 copies of the atom list for 126 rows.

  What a list costs, traced with `HEATHER_CONV_MISS_TRACE` (value-metrics
  build): each `Cons` misses three conversions. `El(List#tycode(A))` against
  `Wf`: the tail's type code, unfolded and decoded. `Vec` against `Σ`: the
  children type, with the arity's `case` evaluated on the label. `Vec` against
  `Unit`. The kernel has a memo for exactly these cross-head queries
  (`Tc::conv_ty`, keyed by the `Rc` identity of an anchor sub-term), but it hits
  0 times on a `Cons` chain (`cons3`: 22 misses, 0 hits). Every constructor
  value gets freshly allocated annotations from `build_ctor`, so the anchors
  never match. A monomorphic `inductive NatList` (named `Wf` slots) is somewhat
  cheaper per node, and still 22 misses and 0 hits.

  So the lever is the emission of constructor values: share each
  instantiation's annotation allocations within a declaration, so repeated
  nodes hit the memo or `Rc` pointer equality. That would help omega's
  certificates and every list-heavy term. It belongs to the emission-cost line
  (`docs/wf-shape-code-design.md`, `docs/annotation-component-respell-design.md`)
  rather than to omega.
- 2026-09-26: Annotation-interning round (uncommitted). A constructor value's children
  annotation and its `sup_f` shape and arity slots are built once per
  declaration (`DeclAttempt`) and shared. In the kernel memo's bucket hint
  (`type_anchor`), an `El` headed by a global anchors on the global's index,
  since its local weakening is rewritten by every substitution, so no two
  occurrences ever share an allocation; a `Vec` or `Σ` anchors on its element.
  Hits are still confirmed by full equality.

  Result: `cons3` 298 → 173 steps (0 → 5 memo hits). Across the `bv_omega`
  fixture and omega's own lemmas, conversion misses fall 8–15%, queries are
  unchanged, seconds fall 10–20% on one noisy pair (not an ab).

  The premise this chain started from does not hold. An `omega` item's kernel
  steps barely move (152.6k → 151.6k). The value-metrics miss table puts its
  conversion misses at ~0.16 s of ~0.56 s, the largest share 13 `El`/`El`
  misses (64 ms): certificate-level comparisons that evaluate `dot` and Int
  arithmetic, not constructor typing. The ~145k-steps-from-lists figure was an
  estimate (per-literal cost × copies), never measured against `omega` itself.
  Omega's certificate cost needs its own attribution before another round.
- 2026-09-26: Attribution round (width 1, one `omega` item: five facts, six atoms).

  - Phases: reflection, search and reconstruction together take under 2 ms;
    elaborating the certificate 158 ms; the kernel gate 374 ms. All of the cost
    is checking the certificate.
  - Kernel: a declaration holding just 177 `have`-bound copies of the item's
    atom list costs 150.6k steps and 518 ms of gate, against the item's own
    151.6k steps. The copies are essentially the whole kernel cost.
  - Per copy: a six-element `List<Int>` costs 851 steps. `Nil` costs 94, each
    element ~126, of which `int::OfNat(x)` alone is ~90 (4 conversion misses)
    and the `Cons` ~36. A six-element `List<Nat>` costs 302.
  - The Int constructor's check goes through the checked-spelling path
    (`InlAt`, conversion via `conv_ity`), which has no memo. Interning its
    spine annotations and re-anchoring `Sum`/`GlobalTy` in `conv_ty`'s memo
    changed nothing, and were reverted.
  - Negative control: `have`-binding every derived bound at a literal row
    (`coeffs_source`) doubled the kernel steps (151.6k → 308.3k): more literal
    lists, each checked.

  Levers, by where the cost is: the per-Int-constructor check (~70% of an
  element), e.g. a memo on the checked-spelling conversion path; the number of
  copies (177 per certificate), omega-side; list-free certificates, which
  remove both. Not yet attributed: the 158 ms of elaboration.
- 2026-09-26: Lever 2, the atom list named once. Probe first: the one `omega` item above, with its 177 literal lists
  replaced by a call to a top-level `fn omega_atoms(sv, r, …)`, fell from
  151.6k to 23.5k kernel steps and 482 → 121 ms. So the copies were the cost,
  and a reference to one definition removes it.

  Built as a *transparent slot* of the declaration's goal arena
  (docs/bv-omega-design.md §6.1):
  - The certificate names its atoms `__omega_atoms`.
  - The `omega` arm elaborates the literal once, stores it in a slot that is a
    definition both while the declaration elaborates and once lifted, and
    checks the certificate with the name bound as an alias to the slot's
    reference.

  Capacity: `count_tactic_slots` reserves two slots per `omega` and five per
  `bv_omega`. An overflow doubles the reservation and restarts. The first
  build gated the restarted attempt anyway, and paid the inline certificate's
  full check (175.9k steps, more than before). An attempt with a restart
  pending is now never gated.

  Result, same item at width 1: 151.6k → 24.3k kernel steps, 521 → 98 ms
  total, with one restart. On the `bv_omega` fixture, kernel steps fall
  50–84% on every `omega`-bearing item: `bv_place_step` 1.56M → 268k,
  `taken_left` 223k → 36k, omega's own `cutsat_*` lemmas 60–77%. The
  fixture's hand side and `bv_` side sum to 1.0 s and 3.5 s at width 1. What
  remains on the `bv_` side is `bv_omega`'s own proofs: their lifted lemmas'
  gates (100–536 ms each) and, on `raise`/`line_state_start`, ~450 ms of
  elaborating the generated forms. Both belong to [[bv-omega-check-cost]].

  `scripts/perf ab --base 86de9b67` (width 1, 3 cold samples, every verdict
  separate): `lib/std/tactic/omega.hthr` total −41%, gate −41%, RSS −12%, its
  `cutsat_*` lemmas −50–68%. The `bv_omega` fixture: total −58%, gate −63%,
  RSS −44%, conversion misses −83%, eval steps −68%, `bv_place_step`'s gate
  4.8 s → 1.3 s. Full suite: 2998 passed. The acceptance's "an order of
  magnitude" is met on the fixture's hand-side items (−67–73%), and not quite
  on the probe item (6×): its remaining steps are the certificate's own rows.
- 2026-09-28: Completion audit: the implementation already landed in
  `c26e5d46`, but this issue remained open. The atom list is parsed and
  elaborated once, named by a transparent goal-arena slot, and lifted as a
  checked definition; a capacity restart is discarded before the gate.

  Added `omega_reconstruction::atom_list_repetition_cost_is_bounded` over
  the original six-atom, five-fact goal. It asserts that reflection still
  uses all six atoms, counts the entire declaration including the atom
  definition's gate, and bounds evaluator steps below 50,000 and total
  generated certificate source below 25,000 bytes. Current result: 17,021
  steps and 11,997 bytes, with the library prefix excluded. The focused
  regression and every Omega suite pass, including bitvectors, logical
  splits, CutSat, division/modulo and wide constants.

  Repeated the original-fix A/B with the existing `86de9b67` and `c26e5d46`
  release binaries, the same historical library sources, width 1 and three
  interleaved cold samples. The probe's evaluator count is 151,583 → 24,288
  in all three pairs; the whole Omega-library count is 695,119 → 427,717
  (−38.5%). Local report: `target/perf-ab/omega-atom-list-sharing.json`.
  Current bitvector sources cannot be checked by the historical before
  binary, so that fixture's earlier A/B remains the evidence recorded above.

  Correction to the previous entry: a 67–73% reduction is not an order of
  magnitude. The original fix achieves 6.2× on the probe, and the current
  tree about 8.9× in steps and 17× in source against the original report.
  The repeated atom list is removed; the stronger overall certificate-cost
  target belongs to [[omega-per-goal-elaboration-cost]] and
  [[arithmetic-certificate-dag-sharing]]. Close this repetition scope.

  Full `scripts/test` records 3,054 passed and zero failed but remains
  INCOMPLETE because the unchanged read-loop process hits its 300 CPU-second
  rail, owned by [[read-loop-process-test-cpu-rail]]. All three of that
  group's tests pass in separate bounded runs: library 54.67 s, fetched
  counting 17.39 s, and mutation controls 260.64 s. The combined-process
  rail remains a separate issue; no caps or coverage were changed.
