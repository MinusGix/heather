---
title: Prove bounded-width executable BitVec addition and subtraction
status: open
labels: [stdlib,bitvectors,proofs,performance]
created: 2026-09-07
updated: 2026-09-07
---

## Problem and scope

Large literals now construct efficiently, but bitvec::add and bitvec::sub still
iterate increment/decrement to the unsigned value of the second operand. In
particular, adding a sign-extended negative displacement can request an enormous
iteration. Supply structural arithmetic whose algorithmic work depends on bit
width, with generic proofs equating its results to the existing definitions.
This is library arithmetic work, separate from the checker's resource diagnostics.

## Acceptance

- Add structural modular add/sub operations with work bounded by width rather
  than operand magnitude, reusing existing carry/borrow machinery where useful.
  Names are provisional; keep existing add/sub definitions and their current
  definitional behavior intact for this round.
- Prove equality to existing add/sub for arbitrary width and open operands.
  If using carry/borrow inputs internally, state and prove their meaning.
  Use ordinary checked Heather proofs, with no new axioms or trusted evaluator
  shortcuts. A handful of closed examples is not a correctness proof.
- Expose congruence/transport lemmas that let a future generator replace an
  expensive concrete computation while keeping canonical arithmetic semantics.
- Exercise widths 0, 1, 8, 32, and 64; zero, all ones, modular wrap, underflow,
  the high-bit boundary, mixed bits, and full-width negative-offset patterns.
  Test open/neutral operands and include a kernel refusal control for a wrong
  result. Small-width reference comparisons may compute the old definitions;
  large tests must not force the very unsigned iteration this issue removes.
- Verify representative width-64 computations within ordinary fuel/memory/CPU
  rails. Use the repository's documented performance protocol for measurements,
  and record enough bounded evidence to distinguish width from magnitude cost.
- Run focused tests and the full scripts/test gate. Keep a resource diagnostic
  failure separate from mathematical incorrectness or an algorithmic bound.

## Independent handoff boundary

Work in the BitVec library, its focused tests, and this issue. A separate helper
module is acceptable if it reduces churn. Do not edit x86 models, call generators,
ELF files, native examples, or kernel/frontend implementation. The coordinator
will integrate the proved operations into x86 after the API is reviewed. The
uncommitted calls implementation is not a prerequisite: existing arithmetic and
carry/borrow code plus the cases above are sufficient to start from a worktree.

## What it assumes from elsewhere

- [[fixed-width-bitvectors]] owns the existing carrier and arithmetic definitions.
- [[bitvec-executable-carry-correspondence]] owns the existing carry correspondence.
- [[bitvec-executable-borrow-correspondence]] owns the borrow correspondence.
- [[bitvec-ofnat-large-literals]] supplies bounded-width literal construction.
- [[bitvec-closed-reduction-cost]] owns refusing excessive computation safely;
  this issue owns a better arithmetic algorithm, not that checker repair.

## Log

- 2026-09-07: Landed in `lib/std/bitvec.hthr` (section *Width-bounded addition and subtraction*).
  **API.** `add_bits(n, a, b, carry)` and `sub_bits(n, a, b, borrow)` are the
  ripples with an incoming carry/borrow, built from the existing
  `carry_majority` and `borrow_next` and forcing the next carry before the
  recursive call as `carry_bits` does; `ripple_add`, `ripple_sub`,
  `ripple_neg` are their no-carry-in instances. **Meaning of the carry-in:**
  `add_bits_spec` — `add_bits(n,a,b,c) = iterate_increment(n, a, toNat(n,b) +
  bit_value(c))` — and `sub_bits_spec` likewise with `iterate_decrement`.
  **Equations at open width and operands:** `ripple_add_eq_add`,
  `ripple_sub_eq_sub`, `ripple_neg_eq_neg`. **Transport:**
  `add_eq_of_ripple_add` / `ripple_add_eq_of_add`, `sub_eq_of_ripple_sub` /
  `ripple_sub_eq_of_sub`, `neg_eq_of_ripple_neg`, plus `cong_ripple_add`,
  `cong_ripple_sub`, and the inherited laws `ripple_add_comm`,
  `ripple_add_sub_cancel`. A generator proves `ripple_add(64, a, b) = r` by
  `refl` and restates it as `add(64, a, b) = r` through the transport lemma;
  the width-64 test does exactly that for `add`, `sub` and `neg`.
  **Proof shape.** One column at a time: the count `toNat(Succ k, cons(hb, tb))
  + bit_value(c)` is put in the existing `borrow_right_value` normal form
  (`twice t`, `Succ(twice t)`, `twice(Succ t)`), a generalized doubled-tail
  law (`iterate_increment_twice_cons`, `iterate_decrement_twice_cons`: two
  low-bit steps move the tail once at any low bit) handles the doubled part,
  and the eight fully cased leaves are definitional. No axioms, no evaluator
  shortcuts; the existing `add`/`sub` are untouched.
  **Evidence (release `heather check`, one furnace box, module baseline ≈3.0 s
  / 110 MB; times are issue-log data, not baselines):** width-64 ripple against
  an `ofNat` literal is ≈3.2 s / 210 MB at operands 2^10, 2^12, 2^14 and 2^63
  alike, and the structural equality grows 109 → 192 MB from width 8 to 64;
  the old `add(64, x, 2^10)` is ≈12.6 s / 6.8 GB (over the 4 GiB test cap) and
  `add(8, x, 248)` already 8.5 s / 3.4 GB. Value-metric counters for the same
  contrast are printed by the metrics-gated block of the new test
  (`HEATHER_VALUE_METRICS=1 scripts/test --fast --features value-metrics -p
  heather-elab --test lib_std_bitvec ripple_add_and_sub_cost -- --nocapture`):
  term closures 366,753 for `ripple_add(64, x, 2^10)` and 366,539 for
  `ripple_add(64, x, 2^63)` (flat in magnitude), 111,267 at width 32 (the
  width is the cost), against 360,385 for the old `add(64, x, 8)` — eight
  increments already cost the whole width-64 ripple, i.e. ≈45k closures per
  unit of the operand.
  **Limitation, owned by [[bitvec-closed-reduction-cost]]:** a *consumer*
  over a width-64 ripple result — `toNat`, `complement`, `sign_bit`, a
  second `ripple_add` over the first, `carry_add_bit` of it — exhausts fuel or
  gigabytes, while the same consumers over `ofNat`/`band` results are cheap
  and the ripple compared against a literal is cheap. It is not the spelling:
  a fully forced eight-branch ripple and an accumulator/list spelling (closed
  list, then `from_bit_list`, the shape `ofNat` uses) cost the same. Numbers
  are logged there. Until that is fixed, integrate by equating ripple results
  with literals or `ofNat` and transporting; do not chain structural
  consumers over them at machine width.
  **Validation:** focused `scripts/test --fast -p heather-elab --test
  lib_std_bitvec ripple` (2 passed) and the plain full `scripts/test` on
  furnace: 2488 passed, 0 failed, 5 ignored. Left open for the coordinator's
  API review and x86 integration; nothing else in scope remains.
- 2026-09-07: The consumer-over-producer limitation above is lifted by the kernel round logged in [[bitvec-closed-reduction-cost]] (transparent δ-whnf for a side with no defined head to meet): `sign_bit`, `toNat`, `toInt`, `complement`, `carry_add_bit`, `borrow_sub_bit`, `signed_overflow_add`, the comparison bits, and a ripple over a ripple all check over width-64 ripple results in seconds under the ordinary rail, pinned by `consumers_over_computed_machine_width_producers_cost_the_width`. x86 integration may chain structural consumers over ripple results at machine width; transporting to `add`/`sub` remains the way to state canonical facts.
