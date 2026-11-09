---
title: Drop no-overflow premises where a word equation needs none
status: closed
thread: Treat machine words as a modular ring
labels: [bitvec,native,cleanup]
area: mathematics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

issues/machine-words-modular-ring.md left the ~240 `Nat::pow(2, …)` side
conditions in native, arch and os for later: each could be dropped where its
lemma only needed the modular statement. This is that pass.

## Audit

84 theorems in `lib/std/{bitvec,machine,arch,os,tactic}` and `lib/native`
take a `2^k` premise in their signature. They sort into:

- **A value read back as a Nat** (44): the conclusion is about `toNat`, a
  bound or a Nat count (`toNat_word_of_nat`, `count_down`,
  `BitVec::offset_toNat`, `cap_small`, …). The bound is the content.
- **Canonical addresses** (`2^47`): x86-64's address space, a property of
  the machine (`perm_canonical`, `Site::moves_load`, the `room` premises of
  argument and stack layouts). Not overflow.
- **Sign and zero tests** (`2^63`, `Succ(k) < 2^64`): `count_nonzero`,
  `cat_count_clear`, `ofNat_sign_clear`, `loop_counter_nonzero`. False
  without the bound.
- **Program specifications**: `cat_implements`' `capacity < 2^63` and the
  correctness theorems' premises, which state what the program assumes.
- **A word equation that holds at every count**: the ones this pass drops.

So the survey's "~240" counts every occurrence, most of them in proofs, and
the premises that were only a route to a word equation are a handful.

## Resolution

Closed 2026-11-09. Dropped:

- `BitVec::zero_iterate_increment(n, m)`: counting up from zero is `ofNat`
  at every count (by `increment_ofNat`, moved with `ofNat_cong`,
  `ofNat_digit` and `ofNat_zero` from `bitvec_nat` to `bitvec`, ahead of it).
- `BitVec::add_nat_iterate(n, a, offset)`: at every offset.
- `word_of_nat_eq_ofNat(n, value)` (new, `bitvec_nat`) replaces native's
  `word_of_nat_ofNat(c, fits)` at width 64; `Target::count_fits` had no
  other use and is deleted.
- `Target::at_rip(q)`, `word_rip(i)`, `buffer_rip(b)`: no `inside`/`found`
  premise; their callers no longer derive one.
- `loop_counter_step(rest)` and `argv_slot_sum(a, r, k, value)` (no `below`,
  no `room`), the latter through `BitVec::ofNat_add_of` (new, `bitvec_nat`):
  `add_words` read at the word, with no bound.

Probes: `count_past_period` … `sum_of_ofNats` in
`lib/_tests/std/bitvec/bitvec_ring_tests.hthr`. `docs/proof-patterns.md`
names which premises a word fact needs.
