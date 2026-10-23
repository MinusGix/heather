---
title: A certified word-to-Nat lifting tactic (bv_omega-style) for no-overflow word arithmetic
status: closed
labels: [proofs,bitvec,metaprogramming,ergonomics]
created: 2026-09-25
updated: 2026-09-26
---

Most of `lib/decimal_line.hthr`'s hand work is not about decimals. It moves
64-bit word facts to Nat and back:
- `toNat_ofNat` with a `below_word` side condition (15 uses);
- `add_words` with its no-overflow bound (6);
- `toNat_sub` with its no-borrow bound;
- `toNat_take_drop` to read bytes back (7).
Then `omega` closes the Nat goal. Every step is mechanical: to state a word
equation over `toNat`, discharge each "does not overflow" by bounds already in
context, and call the Nat solver. Lean's `bv_omega` is this tactic.

A certified tactic that does this would make the next program's formatter,
parser or checksum a page, not a module. And its output is an ordinary proof
term the kernel checks, so it adds nothing to the trusted base.

## Scope

- Reify a goal over `BitVec(w)` `add`/`sub`/`ofNat`/`toNat`, byte extraction
  and comparisons into Nat, with `x.toNat() < 2^w` for each atom.
- Emit the rewrite through the existing `bitvec_nat` lemmas, discharging each
  side condition with `omega` over context bounds. On failure, report which
  side condition failed, not only that the goal did.
- Wrap-around is out of scope for the first slice: refuse, do not model `mod`.

## Acceptance

- `decimal_line`'s `line_state_*`/`place_step` facts are re-proved by the
  tactic, and the hand proof stays as the control. The two are compared on
  size and check time.
- A wrong bound in the context gives a refusal that names the side condition.

## What it assumes from elsewhere

- **[[certifying-arithmetic-proof-automation]]** owns the certifying
  arithmetic tactic family. This is a bitvector-to-Nat slice of it.
- **[[grind-port]]** owns the general certifying solver. A bit-blasting
  route (complete and heavier) is a separate question. This route suits wide
  words whose facts are arithmetic.
- **[[tactic-composition-ergonomics]]** owns how the tactic composes with
  others.
- **[[omega-constants-beyond-u64]]** owns omega's constants at 2^64 and
  above. Assumed here: that omega can state and use `x.toNat() < 2^64`.
  Today it can't, so this issue waits on that one.
- **[[omega-respells-atoms-without-implicits]]** owns spelling atoms such as
  `toNat(ofNat(…))`. Assumed here: that omega accepts word facts in its
  context, which the tactic adds on every call.

## Log

- 2026-09-25: Sequencing, from probes of the workarounds in `lib/decimal_line.hthr`. Two of
  its comments are stale. "vectors of different lengths" and the kernel
  refusing `v + v = 2 * v` were both the `coeffs_source` trailing-zero defect,
  fixed the same day (see [[omega-respells-atoms-without-implicits]]'s log).
  Neither reproduces now, in a Nat context or with a `BitVec` fact in scope.
  The 2^60 cap is real and has a new owner, [[omega-constants-beyond-u64]]:
  omega can't print a constant of 2^64 or more, and it reads `pow(2, 64)` as an
  atom. Fix that and the respelling issue first, then measure how much of the
  word section is still hand work before building the tactic.
- 2026-09-25: Re-measured `decimal_line` after [[omega-constants-beyond-u64]] landed.
  Retired: `below_word`'s hand bridge to `pow(2, 64)`, now one `omega`, and the
  two stale comments. `double_scaled` and `doubling_bounds` stay. `omega` can
  now prove their goals inline, but in `times256_value`'s context that costs
  6.0 s against 31 ms, because omega reflects every fact in scope
  ([[omega-relevant-facts-only]]). What remains is the tactic's real target:
  - 25 bridge-lemma uses: `toNat_ofNat` 6, `add_words` 6, `toNat_take_drop` 7,
    `toNat_sub` 2, `unsigned_lt_nat` 2, `toNat_word_of_nat` 2;
  - 15 `below_word` side conditions;
  - 23 transports under `toNat`: 21 `j(sym(…))` and 2 `cong`.

  A further 8 Nat-only helpers (`kept_*`, `taken_*`, `weight_small`) exist
  because of [[omega-respells-atoms-without-implicits]]. Fixing respelling alone
  won't retire them profitably, since inlined they'd pay the whole context.

  Design consequence: the tactic must hand `omega` only the facts each side
  condition needs. So it waits on [[omega-relevant-facts-only]], or does that
  slicing itself.
- 2026-09-25: Unblocked: [[omega-relevant-facts-only]] landed. An inline `omega` in
  `times256_value` now costs about 1.6 times the lemma form, not about 5.5
  times (width 1), so the tactic can send each side condition to `omega` in place. The
  remaining target is the 25 bridge uses, 15 side conditions and 23 transports
  counted above.
- 2026-09-26: Design verdicts (with the user; do not relitigate). `bv_omega` is a
  checking-position leaf beside `omega`. It emits one flat `let` per word
  subterm (`t.toNat()` in terms of its children's, by the bridge lemmas), each
  side condition its own `omega` so a refusal names it, then `omega`. Unfolds
  non-recursive user definitions by one δ-step when the head is not a known word
  operation, spelling facts at the call. First slice does arithmetic leaves only:
  splitting a `match` stuck on `unsigned_lt_bit` is a follow-up. Step 0 is
  [[omega-respells-atoms-without-implicits]]'s speller fix.
- 2026-09-26: First slice landed: `bv_omega` (docs/bv-omega-design.md;
  `crates/elab/src/bv_omega.rs`, lemmas in `lib/std/tactic/bitvec_omega.hthr`, tests in
  `crates/elab/tests/bv_omega.rs`). Step 0 closed
  [[omega-respells-atoms-without-implicits]]. The emission shape changed three
  times under probes (design §2 gives the reason for each): facts over leaves,
  not children (chained facts made each `omega` pay for the chain); `have`, not
  `let` (2^depth kernel paths: 82 s → 2.4 s at eight doublings); a balanced
  bundle plus the goal over Nat variables (a Π per side condition, or omega's
  atom fallback reducing `toNat(double(…))`, ran out of kernel depth near 39
  doublings).

  Acceptance, against `decimal_line` (probes; width 8, total ms from
  `--timings`; "hand" is the item plus the helpers it alone uses):

  | fact | hand | `bv_omega` |
  |---|---|---|
  | `times256_value` (+ `doubling_bounds`, `double_*`) | ~750 | 2,600 |
  | `raise_value` (+ `raise_bounds`, the above) | ~1,100 | 9,700 |
  | `line_state_start`'s value, one call | (inside `line_word_value`) | 10,500 |
  | `line_start_value` | 62 | 670 |
  | `line_length_value` | 27 | 1,080 |
  | `place_step` (+ 9 `kept_*`/`taken_*` helpers) | ~5,200 | 14,100 |

  Size: the raise chain (about 45 lines over six lemmas) becomes one line.
  `place_step` keeps its `match` on `q` and its branch selection, and loses the
  nine Nat helpers, `below_word` and every transport. A too-weak bound is refused
  naming the side condition ("`double(y)` may overflow 64 bits").

  Verdict: correct everywhere, and 3–40× the hand proofs' check time, so the
  library keeps its hand proofs and the re-proofs stay probes. Residue, each
  with an owner: the cost, and whether `decimal_line` adopts the tactic once it
  drops → [[bv-omega-check-cost]]; byte extraction, `unsigned_lt_bit` and word
  equality goals → [[bv-omega-bytes-and-comparisons]]; splitting `place`'s
  match → [[bv-omega-split-stuck-comparison]]. Found on the way:
  [[omega-shadowed-binder-certificate]].
