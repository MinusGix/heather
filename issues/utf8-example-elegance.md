---
title: The UTF-8 example reads as logic, not plumbing
status: open
labels: [examples,tactics,library,language]
area: tactics
created: 2026-11-18
updated: 2026-11-18
---

After PR #787 (`examples/utf8/utf8_check.hthr`, 856 → 448 lines), Minus's
review (2026-11-18) of what still reads badly, and the plan agreed for it,
worked down in this order and merged as each lands.

## What reads badly, and why

Three causes account for most of it:

1. **The span is a bare `List<u8>` and a length word.** `byte_within` (0
   past the end), `at` (a default of 0 that only dodges a proof), `Window`
   and its read rules, the `drop((i + 1).toNat())` arithmetic and most
   `Cons` spellings exist for this. `Bytes(n)`
   (`lib/native/runtime/bytes.hthr`) reads `s[i]` under a found proof.
2. **The program mimics the decoder in word arithmetic**: it assembles a
   code point and compares it with bounds, through `utf8_two/three/four`
   and the `_at` helpers (which exist only so the certificate scan of the
   loop fits one step), returning `0`/`1` words tested by `.eq_bit(0)`.
3. **Statements are Bool equations** (`holds() = …`) because `rewrite` and
   `bv_decide` read those, where a reader wants `↔`.

And the proof: `valid_window_decides` is thirteen induction arms of
positional plumbing (`h3`, `h4`, `rewrite(win.left(i + 1), bv_omega)`);
names like `two`, `cut_two`, `stops`; theorems that should not need to
exist (`valid_is_decoded` is `refl`; `decode_cons` exists because `decode`
matches three conses deep; `class_*` because the program and the decoder
classify a lead byte separately).

## The list

1. Library and language pieces:
   - [x] `Option::is_some` in `option.hthr` (the example's `Option::holds`;
     one definition also ends the compile-x86 clash of two modules each
     defining it).
   - [x] Widening casts between words (`u8 → u64`), in the cast graph
     (docs/language/casting-design.md), read by `bv_decide`/`bv_omega`;
     the example's `word` goes.
   - [x] List patterns and literals with a rest (`[b, c, ..r]`).
   - [x] A rule in docs/proof-patterns.md: an induction's cases each name
     the fact of the specification they are; a chain of rewrites every case
     repeats is a lemma or a tactic; never thread hypotheses by position.
2. Tools: `bv_decide` reads `∧ ∨ ↔ ¬` over what it reads; `↔` lemmas
   rewrite, so statements stop being Bool equations. `split_all` through a
   decision ([[split-all-decided-proof-scrutinee]]) so `emit_is_some` goes.
3. The example over `Bytes(n)`: `byte_within`, `at`, `Window` go
   (needs loops taking facts in `runtime fn`, the span-loops thread).
4. The program as Unicode's well-formed byte table (Table 3-7: the second
   byte's range depends on the lead, `E0 → A0..BF`, `ED → 80..9F`,
   `F0 → 90..BF`, `F4 → 80..8F`, else `80..BF`; later bytes `80..BF`), with
   a `Lead` classification shared by the program and the decoder; the proof
   one lemma per sequence length and a `match` on the lead's class; the
   result in Rust's shape, `Result<(), Utf8Error { valid_up_to }>`, which
   also states the bad byte's offset the README lists as unproved.

## Log

- 2026-11-18: filed with the plan.
- 2026-11-18: item 1 built. `Option::is_some`/`is_none`/`is_some_and`/`get`
  in option.hthr (from function_ir_lower and regex_table; utf8's
  `is_some_string` is `.is_some()`). Word widening edges
  (`BitVec::widen_8_64` and kin, `Casts::indexed_edge` for one carrier at two
  indices), compiled by `runtime fn` (`PWiden`) and read by `bv_omega`; the
  example's loop compares its byte at `u8` and widens with `↑`, so `word`
  is gone. `[a, b, ..rest]` patterns and values; the example's nested length
  matches are one match each. The proof-patterns rule. Found on the way:
  `omega` does not unfold `len` three conses deep (`cut_four` annotates the
  binder `short: r3.len() + 3 < 3`), and a block in a deep-pattern arm turns
  the match into one the termination guard refuses ("a deep pattern is not
  available in this `match`") though the function does not recurse.
- 2026-11-18: `by bv_decide()` splitting `utf8_four`'s four nested ifs over a
  21-bit code point peaked at 6.4 GiB in `compile-x86` (the native gate's
  rail is 6 GiB; latent since #787, where the native test was not re-run).
  Stating the verdict as one Boolean formula first (`four_bits`, by
  `split_all; all_goals { refl }`) brings it to the file's 2.2 GiB
  baseline; `three_decides` alone peaks at 5.3 GiB. The split is the cost,
  not the bit-blast: a bv_decide that reads a program's ifs as
  `ite` without splitting them would retire `four_bits` (item 2), and the
  range-table program (item 4) has no nested arithmetic tests to split.
- 2026-11-18: item 2, first half: `split_all` splits a decision
  (`b.is_true_dec()`) as itself and rewrites `b` by the case equation
  (`Bool::decided`), so `emit_is_some` is `split_all; all_goals { refl }`
  ([[split-all-decided-proof-scrutinee]], closed). The `↔` half moves into
  item 4: its statements are the ones that change (a lead's class, byte
  ranges, `Result<(), Utf8Error>`), and reading `∧ ∨ ↔ ¬` in `bv_decide`
  is built for the shapes those statements take rather than for today's
  `is_some()` equations, which item 4 replaces.
- 2026-11-18: item 4, first half: the program is the table
  (`sequence_length`, its tests as Table 3-7 prints them), `sequence_at`
  reads the four bytes at an offset, and the loop steps by what the table
  answers. `utf8_two`/`_three`/`_four`, their `_at` readers, `four_bits`
  and the `*_decides` theorems are gone; the native program is 1488
  certified bytes. Built for it in `bv_decide` (PR #803): a word chosen by
  an `if` is read as an `ite` without splitting the goal, and a word call
  with a list argument (`s.byte_within(n, i)`) is an atom. The proof is one
  `takes`/`refuses` lemma per length over four byte variables, each by
  `bv_decide` in a few seconds, and the induction's arms find the table's
  answer with `by assumption()` rather than by a hypothesis's position.
  What the round found: naming those tests in the program (`if two: k = 2`)
  makes the kernel run out of fuel on `utf8_valid_from::compile`, though
  the unnamed program compiles; a `runtime fn`'s parameters must be
  64-bit words, so the table takes words and truncates them to bytes
  (`issues/function-ir-multi-word-calls.md`); the same table compared at
  64 bits makes the kernel's `bv_decide` certificate check run out of fuel
  (more than eight times the budget), at 8 bits it is seconds; and stating
  the per-length lemmas about `sequence_at(s, n, x)` with the reads as
  atoms gave a false counterexample (the reads were partly unfolded),
  which byte variables avoid. Left for the second half: a `Lead`
  classification shared with the decoder (today the decoder's
  `class_of` and the table each test the lead byte), `↔` statements, and
  the result as `Result<(), Utf8Error { valid_up_to }>`.
