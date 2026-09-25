---
title: A certified word-to-Nat lifting tactic (bv_omega-style) for no-overflow word arithmetic
status: blocked
blocked-by: [omega-constants-beyond-u64]
labels: [proofs,bitvec,metaprogramming,ergonomics]
created: 2026-09-25
updated: 2026-09-25
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
