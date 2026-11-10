---
title: The numeral crate's limb arithmetic compiled from Heather and linked into heather
status: open
labels: [native,self-hosting,kernel,design]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-10
---

A third linked target, after the lexer and SHA-256 (Minus, 2026-11-10:
"Another useful target would numeral eventually. This may be slower as we
don't have a proper optimizer yet but we will eventually").

`crates/numeral` is the arbitrary-precision natural every stage shares: the
lexer reads a literal into it, the kernel's `Term::NatLit` carries it, and
the kernel relies on `is_zero`, `pred` and `limbs`. It is small, it is in
the trusted base, and its operations are loops over little-endian `u64`
limbs: `pred` (a borrow walking up), `succ`, `mul_add` (a limb times a
`u64` plus a carry, what `parse` folds over digits), `div_rem` by a `u64`
(what `Display` folds), `bits`, `bit`, and the comparison. Each has a
one-line specification over `Nat`, which is what makes it a good target:
the theorem a linked export carries is "this is the number".

## What it needs that the first two targets do not

- **A wide multiply and a divide.** `mul_add` is a 64×64→128 product plus
  two carries; `div_rem` divides a 128-bit value by a 64-bit one. Both are
  [[x86-wide-multiply-and-carry]]'s (`MUL`, `DIV`, `ADC`/`SBB` or the
  flag-free forms), with `bitvec`'s wide-product laws
  ([[bitvec-rotates-and-wide-ops]]).
- **A buffer the callee writes and whose length changes.** `pred` and
  `mul_add` return a number with one limb fewer or more. Under
  [[native-library-exports-design]]'s contract the caller owns the memory,
  so the export is "limbs in place, new length returned", with the Rust
  side keeping `Arc<[u64]>` and the normal-form invariant (`Big` exactly
  past `u64::MAX`, top limb nonzero) stated as the export's postcondition.
- **The specification.** A limb list's value as a `Nat` (little-endian,
  base 2^64) and each operation's equation against `Nat`'s. The library
  has the single-word half (`bitvec_nat`); the list half is new and is
  [[machine-words-modular-ring]]'s neighbour.

## What it does not need

Nothing here is secret-dependent, so no constant-time theorem, and nothing
allocates on the Heather side.

## Order

After `sha2-compress-native`'s buffer-held state (the first export that
writes memory) and after the wide multiply. The Rust stays the fallback
and the oracle: the tests are the crate's own (`display_round_trips_in_every_radix`,
`order_is_numeric_and_pred_borrows_across_limbs`) run over both, plus a
differential over varied limb vectors, as `crates/linked/tests` does for
the hashes.

## Speed

Linked code is slower than rustc's today (every live register saved around
a call, a frame per leaf, no instruction selection past the obvious). That is
accepted for this target: numerals past one limb are rare, and the small
case never leaves Rust. Record the ratio with the export, so the optimizer
work has a number to move.

## Done when

`pred`, `mul_add`, `div_rem` and the comparison are `runtime fn`s proved
against the `Nat` specification, linked through `crates/linked` under the
regeneration gate, and `crates/numeral` calls them behind a switch with
its tests and the whole suite unchanged.
