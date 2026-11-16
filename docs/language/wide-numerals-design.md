# Numerals of any size

Status: implemented 2026-09-26. Tracking: `issues/wide-numerals.md`.

A numeral was a `u64` from the lexer to the kernel: `18446744073709551616`
(2^64, the first number a 64-bit word cannot hold) did not lex. Mathematics
needs such numbers constantly — a word's bound is one — and the workarounds
were `Nat::pow(2, 64)`, which the kernel computes one multiplication per
exponent step, or `omega`'s byte chain `add(mul(x, 256), b)`. Numerals are now
arbitrary-precision everywhere.

## 1. One type, first-party

`heather-numeral` (`crates/numeral`) holds `Numeral`, an arbitrary-precision
natural: a `u64` inline, and little-endian `u64` limbs behind an `Arc` above
it. The crate has no dependencies. It is shared by the lexer, the AST, the
elaborator and the kernel, which is why it is a crate of its own rather than
a kernel module: the syntax crate stays independent of the kernel.

Invariant: the limb form is used exactly when the value exceeds `u64::MAX`,
and its top limb is nonzero. Equality, hashing and order are therefore
structural. The crate offers only what its users need — parsing in a radix,
decimal display, `as_u64`, `pred`, `is_zero`, limbs — and no arithmetic
beyond that: computation is the kernel's business, on its own values.

It is in the trusted base, since `Term::NatLit` carries it. What the kernel
relies on is small: `pred` of a nonzero value, `is_zero`, and the limbs.

## 2. Kernel

`Term::NatLit(Numeral)`. Nothing about its meaning changes: it is
observationally `Succ^n(Zero)`, its one-step view is `Succ(NatLit(n - 1))`
(`reduce.rs`, the syntax conversion domain), and evaluation hands it to the
run representation (`Val::NatRun`). A value up to `u64::MAX` is one saturated
run, as before. A larger one is built from its limbs by doubling:
`2^64` is two shared runs of `2^63`, a limb multiple is binary composition
over that, and the low limb is appended — `O(bits)` shared nodes, which is
what `ContextProgram` already produces when arithmetic overflows a run.

Comparison (2026-10-22, `issues/kernel-wide-run-comparison.md`): every
composed node carries its length, so `leb`, `sub` and conversion cancel two
numbers by their lengths and cut the longer one along one path — `O(bits)`
however the two were built. Before, numbers built by different routes were
walked one `≤ 2^63` fragment at a time and ran out of fuel near `2^96`.

## 3. Surface and elaborator

The lexer reads any digit string in all four radixes into a `Numeral`
(`TokKind::Num`, `ExprKind::Num`). Positions that need a machine integer — a
universe level, an argument slot, a width, an index — take `as_u64()` and
refuse a larger numeral where they refused nothing before, with a message
that says why. A value-position numeral elaborates to `NatLit` at any size,
and carrier-directed numerals (`Numeral<C>`) receive it as their `Nat`
argument unchanged.

`omega` spells a constant past `u64` as the numeral it is. Its own integers
are `i128`, so a constant past that is still declined, as before.

## 4. What is not changed

Module images and the cache hash a small literal exactly as before; a large
one has its own tag. Readers that want a machine value (`certgen`'s value
reader, `function_ir_source`'s constants, tag readers) take `as_u64()` and
decline above it.
