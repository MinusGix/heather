---
title: Decimal output and input for native programs, on add and subtract
status: closed
labels: [native,stdlib]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-28
---

Round 9 of `docs/native-real-programs-plan.md` (§3.7, §6). Printing a count
needs digits, and `head -n N` needs to parse one. The ISA model has no
multiply, divide or shift, and FunctionIR's shifts are refused at lowering
([[verified-lowering-instruction-coverage]]). Neither is needed. Output
subtracts powers of ten in a bounded loop, as the burned `%*d` did
([[native-proven-formatting-api]]). Input multiplies by ten as `8x + 2x`,
by doubling with `Add`.

## Scope

- Builder library functions: format a 64-bit word as decimal into a buffer
  at an offset (POSIX `%d`, and `%*d` for `wc`'s columns), and parse a
  decimal prefix of a buffer with overflow detection.
- Each with a pure spec (`decimal_digits`), stated against the `Source` it
  lowers to, where the round can afford it.

## Done when

`wc -c` prints its count, and `head -n N` takes N from argv.

## What it assumes from elsewhere

- **[[native-source-builder]]** owns the builder.
- **[[native-source-bytes]]** owns the byte stores.

## Done (2026-10-28)

- **Procedures** (`lib/native/native_decimal.hthr`, builder statements, so
  inlined where called): `put_decimal_padded(buf, at, value, width)` is
  `printf("%*lu")`, `put_decimal` `%lu`, `put_signed_decimal` `%ld`, and
  `parse_decimal(buf, from, upto, value, end, overflow)` reads the digits
  from `from` before `upto`, `end` where they stopped and `overflow` set
  past the largest word. Output finds the largest power of ten not past the
  word going up from one (×10 is `Var::times_ten`: `2v` kept, doubled twice,
  `2v` added, four nodes), takes each digit as how often the power comes
  off, and comes down to the next power by going up again from one, so
  nothing divides. Input tests `value > ⌊(2^64−1)/10⌋`, or equal and the
  digit past 5, before each ten-fold.
- **Spec.** The probes (`lib/_tests/native/native_decimal_tests.hthr`) run
  each procedure's lowered source through `Source::tree` and compare the
  bytes with `pad_left(width, ' ', decimal(value))` (`std/text/decimal`), or
  read the parse's results from the exit status. Each pass of a loop costs
  the source's denotation tens of thousands of kernel steps, and `decimal`
  itself divides in unary, so the probes are small values at the edges the
  code turns on (0, 7, 10, 99, 100, padding wider and narrower, −7, a stop
  at a non-digit). A theorem for every word is
  [[native-decimal-io-proved]].
- **Tools** (`lib/native/native_tools.hthr`): `wc_counts` is GNU's `wc`
  over stdin with `-l`, `-w`, `-c` in any grouping (one count bare, more in
  seven columns, C-locale words: `isspace` ends one, a printable byte starts
  one, others neither); `head_n` is `head -n N`/`-nN`/no argument, with
  GNU's two diagnostics for a bad count. `decimal_echo` (the probes'
  module) parses argv[1] and prints it unsigned and signed.
- **Tests** (`crates/cli/tests/native_tools.rs`, off the fast lane):
  `compiled_wc_prints_counts_as_gnu_wc` (nine flag sets × seven inputs,
  stdout and status), `compiled_head_takes_its_count_as_gnu_head` (counts
  from 0 to the largest word, the bad counts' stderr, `/dev/full`), and
  `compiled_decimals_round_trip_the_widest_words` (every power of ten and
  the number below, the signed edges, random words, refusals).
- **The wall met: write-elf's allocator.** `wc` ran write-elf out of the
  8 GiB rail in `{p}_homes_spelled`: `Allocator::greedy` evaluated on the
  fork, whose read keeps everything it forces. It now runs in Rust over the
  read-back source (`crates/cli/src/native/allocator.rs`), the same homes
  ([[native-allocator-cost]]). After it, `wc`'s single-`refl` lowering
  took about nine tenths of the per-declaration fuel, which the
  certificate-budget round's per-part statements
  ([[native-tool-certificate-budget]]) then removed; the tools are nullary
  `_tool`s for that.
- Not here: files (`head -n N FILE`, `wc FILE…`, and the column width GNU
  takes from a regular file's size), `-c` for head, GNU's `+N`/`-N`/suffix
  forms of a count (refused with GNU's invalid-count message), and the
  missing-argument message.
