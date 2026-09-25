---
title: omega can't spell a constant of 2^64 or more in its certificate
status: open
labels: [omega,proofs,bitvec]
created: 2026-09-25
updated: 2026-09-25
---

Omega reasons over `i128` coefficients, but it rebuilds its certificate as
source, and a source numeral is a `u64` token. Any constant of 2^64 or more
in the certificate fails to parse, even an intermediate one the user never
wrote:

```text
theorem a(x: Nat, h: x < 1152921504606846976): x + 1 <= 18446744073709551615 { omega }
error: `omega` got stuck: numeral out of range: 18446744073709551616
```

Also refused (probes, 2026-09-25, at 5079abcc):
- `x, y < 2^64 - 1 ⊢ x + y < 2 * (2^64 - 1)`: the Fourier–Motzkin
  combination is `36893488147419103230`.
- `v = 1099511627776 * r + h, h < 2^40, v < 2^64 - 1 ⊢ r < 2^24`: a
  normalized bound reaches 2^64.
- `x < 2^60 ⊢ x < Nat::add(18446744073709551615, 1)`: writing 2^64 as a
  sum doesn't help, because omega folds it to one constant and prints that.

One more gap, of the same kind: `Nat::pow(2, 64)` is an opaque atom, so
`x < 2^60 ⊢ x < Nat::pow(2, 64)` gets stuck. A 64-bit word's bound can
therefore be stated neither as a literal nor as a power.

This is why `lib/decimal_line.hthr` keeps every word value below 2^60 and
bridges to `pow(2, 64)` by hand (`below_word`). Word arithmetic lives right
at this bound. A carry or borrow is `± 2^64`, and the no-overflow bounds of
[[bitvec-nat-lifting-tactic]] are `x.toNat() < 2^64`.

## Scope

The fix is omega's. The kernel already carries Nats past `u64` as adjacent
runs (`crates/kernel/src/value/program.rs`), so only the spelling is
bounded:
- Render a constant that doesn't fit a token as an expression that does
  (for example a `Nat::add`/`Nat::mul` of `u64` literals), at every site that
  prints one. That's `int_ctor` (`crates/elab/src/omega_cert.rs:2141 @
  5079abcc`) and the direct `{value}` formats around it.
- Check that `literal_lt_proof` and the other closed comparisons still check
  cheaply at those sizes.
- Decide whether a closed `Nat::pow(2, k)` reflects as its constant. Plain
  evaluation is one answer. A registered power lemma is another, and it
  avoids surprising reductions (the constraint
  [[certifying-arithmetic-proof-automation]] records).

Wide source literals (lexer, AST, `NatLit`) are a separate decision, deferred
in [[radix-numeric-literals]]. This issue doesn't need them.

## Acceptance

- The repro above and the three refused probes check.
- `x < 2^60 ⊢ x < Nat::pow(2, 64)` checks, or a note records why power
  reflection was declined and what callers state instead.
- A negative control near the bound, such as `x < 2^64 ⊢ x + 1 < 2^64`, is
  still refused.
- A carry-shaped fact at full width checks:
  `a, b < 2^64, a + b = s + 2^64 ⊢ 2^64 <= a + b`.

## What it assumes from elsewhere

- **[[radix-numeric-literals]]** owns the `u64` token bound. Assumed here:
  only that it stays, so omega must spell around it.
- **[[bitvec-nat-lifting-tactic]]** is the motivating consumer, not a
  dependency.
