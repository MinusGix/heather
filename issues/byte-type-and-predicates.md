---
title: A byte type name and C-locale byte classes in the library
status: closed
labels: [stdlib,native,surface-syntax,design]
area: heather-in-heather
created: 2026-10-07
updated: 2026-11-03
---

A byte-reading program spells its byte type `BitVec(8)` everywhere and writes
its own byte classes. `examples/x86-native/wc.hthr:32-35`:

```heather
fn newline(b: BitVec(8)) → Bool { decide_bit<b = '\n'>() }
fn space(b: BitVec(8)) → Bool { decide_bit<b = ' ' ∨ ('\t' <= b ∧ b <= '\r')>() }
```

`wc_l`, `tr`, `tr_s`, `tr_d` and the command library restate the same
classes. Wanted: a name for the byte type and the C-locale classes as library
methods, so the program reads `b.is_newline()` and `b.is_space()`.

Questions to settle:

- **`Char` or a byte.** `Char` (`lib/std/text/char.hthr`) is a Unicode scalar, so
  reading input as `Char` presumes a decoder (UTF-8 or UTF-32) in front of the
  step. GNU `wc` under `LC_ALL=C` counts bytes, and so does the claim. The
  likely answer is a byte type for byte programs and `Char` for decoded text,
  with the classes on both (`Char::is_space` already exists, with Rust's
  ASCII-whitespace set, which differs from C's `isspace` by vertical tab).
- **Alias or type.** The surface has no top-level type alias today: a
  type-valued `let` is a local alias (`crates/elab/src/inductive.rs:1210`).
  Options: a top-level `type Byte = BitVec(8)`; methods declared on
  `BitVec(8)` at that width only; or a `Byte` record wrapping `BitVec(8)`
  (a new type, which every native lowering would then have to see through).
  An alias is attractive on its own because `BitVec(8)` is the most common
  type in the native library. Probed 2026-10-07: `type Byte = BitVec(8);` is a
  parse error ("expected `fn`, `theorem`, `axiom`, or `inductive`"), and
  `fn BitVec::is_nl(self b: BitVec(8)) → Bool` works as a method on a
  `BitVec(8)` receiver. It is also offered on a `BitVec(16)` receiver, where
  the gate refuses it with a note naming the method and both widths
  ([[width-specific-method-on-other-width]], closed 2026-10-08).
- **Lowering.** The structured frontend must still see the comparisons a
  class method unfolds to, as it does for today's `decide_bit` predicates
  (helpers that are comparisons are split at the comparison,
  [[filter-default-spells-program-names]]).

## What it assumes from elsewhere

- **[[byte-vocabulary-for-native-programs]]** (closed) settled how a byte
  test is written and lowered. Assumed here: only that `b = '\n'` and the
  connectives keep lowering as they do.
- **[[bool-from-decidable-prop]]** owns whether `decide_bit<…>()` can be
  dropped from a Bool-valued body.

## Log

- 2026-10-21: The code cited above (crates/elab/tests/fixtures/open_read_close.hthr, examples/x86-native/wc.hthr) was burned in B1 ([[native-burn-process-stack]]; last at 189659d, tag native-v0); the language ask stands on its own.
- 2026-11-02: 2026-11-02 (PR #394 review): Minus asks for named abbreviations such as u8 and u64 for the common BitVec widths. Probed: `def u8: Type = BitVec(8);` is a value and cannot be used as a type ("`u8` cannot be used here"), and a top-level `type` alias is still a parse error. So the alias question here is the general one: a top-level type alias, with u8/u16/u32/u64 (and `Byte`) as its first customers.
- 2026-11-03: 2026-11-03: Done, widened per Minus to any width and signed (docs/library/fixed-width-integers-design.md). No `type` keyword (types-as-expressions.md chose type-valued definitions): a `def` at a universe now names its type and is expanded on the spot, so `def u8: Type = BitVec(8)` works, and a width family `def u: Nat → Type = BitVec;` makes `u8`, `u27`, `u64` mean `u(n)` = `BitVec(n)` (in bitvec.hthr). Signed words are a type of their own, `record SInt(n) { bits: BitVec(n) }` with `def i = SInt` (`i8`, `i64`), because `<`, division, right shift, widening and numerals differ; shared operations are the word's on `bits`. New: `+ - *` and prefix `-` designations at BitVec, long division (`udiv/urem/sdiv/srem`, width-bounded, SMT-LIB by zero, bitvec_div.hthr), and the C-locale byte classes as `u8` methods (`b.is_space()`, `b.is_newline()`, … in byte.hthr). Follow-ups: [[integer-operator-symbols]], [[bitvec-division-laws]], [[sint-native-lowering]], [[type-name-display-respelling]].
