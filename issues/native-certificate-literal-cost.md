---
title: Cut what a write-elf certificate's literals cost per byte and per instruction
status: closed
labels: [native,elaboration,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-31
updated: 2026-10-31
---

The next-areas survey (2026-10-31) ranked "the certificate cost that grows
with tool size" first, quoting `perf/bench/targets.md` T3: write-elf's own
reads of `cat_files_tool` at about 56 s (`bytes_#_#` 37 s, `read_#_entry`
19 s). That figure is from 2026-10-29 and had gone stale.

Measured on master f9c6e9d (cloud box, dev-profile `heather`, width one,
`write-elf --timings` over a fresh copy of a warmed store, the library
replayed): `cat_files_tool` 86 s in all, the reads `bytes_#_#` 5.7 s,
`read_#_entry` 1.2 s, `read_#_part` 2.0 s. Every family is linear in the
code: per-read steps are flat from `cat_x8` to `cat_x16`, and doubling the
code (`cat_x8` 42 s → `cat_x16` 65 s) adds 19 s of items spread over the
families. What grows with a tool is therefore the constants per byte and
per instruction, and the two largest were the elaboration of the literals:

| family | items | s | of which |
|---|---|---|---|
| `at_#` (the program literal) | 335 | 11.8 | resolve 2.4, instance_match 2.4, kernel 3.2 |
| `piece_#` (the byte pieces' literals) | 195 | 10.5 | elab whnf 3.7, body 4.3, kernel 2.0 |

## What changed

- **A list literal's spine read back in linear time.** `collection_literal_spine`
  reads each child back from the value, and each child holds the rest of
  the literal's vector. The readback applied the closure's substitution even
  when it was the identity, and a closed subtree that mentions a global is
  never skipped by its bounds (its `u^δ` tail is rewritten unconditionally,
  `crates/kernel/src/bounds.rs`), so each child walked the rest: `k²` node
  visits for `k` elements (a 224-byte literal 586K, now 87K).
  `Readback::identity` (`crates/elab/src/readback.rs`) returns the body when
  the substitution sends it to itself. Test:
  `list_literals::a_literal_spine_is_read_back_in_time_linear_in_its_length`
  (64 → 256 elements was 11×, now about 6× in a debug build, whose sampled
  re-check by the reducer still copies; under 4× without it).
- **Byte pieces as numerals mapped to bytes** (`labels::byte_pieces`):
  `List::map([n, …], λ b => BitVec::ofNat(8, b))` instead of a literal of
  `from_bits(8, [eight Bools])`. The elaborator paid eight constructor
  lookups and a vector per byte; the kernel reads `ofNat` at a numeral as
  one word ([[ofnat-nat-state-arithmetic]]), so `piece_#_is` is unchanged
  (6.158M → 6.161M steps) and `upto_#_len` grows a little (138K → 249K steps,
  under 0.1 s).
- **Instruction blocks by their constructors** (`verified::read_items_with`):
  `Block(Cons(i, Nil))` instead of `Block([i])`. A list literal resolves its
  `CollectionLiteral` instance and unifies its element type per use; the
  constructors skip both. `at_#` steps fall too (680K → 546K).

## Result

Same box and lane, before → after:

| run | before | after |
|---|---|---|
| `cat_files_tool` | 86 s | 65 s |
| `cat_x8` | 42 s | 35 s |
| `cat_x16` | 65 s | 50 s |
| added by 8 more cat passes | 23 s | 16 s |

`piece_#` 10.5 → 1.6 s and `at_#` 11.8 → 6.8 s on `cat_files_tool`.

## Left, largest first (cat_files_tool, after)

- `bytes_#_#`, 5.1 s: the fork re-emits each part to read its bytes
  (7.5M steps); reading the bytes in the part's own read needs the label
  offsets, which are known only once every part is read.
- `piece_#_is`, 4.0 s of kernel: the assembler run per piece
  ([[native-certificate-pieces-remaining-cost]]).
- `e_#`, 3.2 s of kernel: each whole part's emission by `refl`.
- `at_#`, 6.8 s: kernel 2.6 s (constructor typing) and `instance_match`
  1.7 s per constructor.
- The fixed floor of a write-elf process, about 20 s ([[native-process-fixed-cost]]).
