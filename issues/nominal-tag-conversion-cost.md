---
title: The nominal tag was most of what comparing declared-inductive data cost
status: closed
labels: [performance,kernel,inductives,conversion]
created: 2026-09-26
updated: 2026-09-26
---

Comparing two values of a declared inductive cost several times what the
values contain. Every constructor carries its declaration's nominal tag
(`docs/inductive-tier0-lowering.md` §3.3), and the tag was the declaration
index's binary digits as a right-nested Σ of `Unit`s. The tier-0 design
called it "free in conversion", on the grounds that η never compares it. In
fact Σ-η projects its way down the nest, so every comparison of two values
walked all `O(log k)` levels, and with the library loaded `k` is in the
hundreds.

## Attribution

Probe: two separately built 48-element lists compared by `refl`, with
temporary per-former counters in `Conv::tm_nf` (not kept).

| 48 elements | `tm` calls | Σ-η arms | of which tag digits | `Unit` leaves |
|---|---|---|---|---|
| `List<Nat>` | 1,162 | 488 | 392 | 490 |
| `List<Bool>` | 1,844 | 824 | 728 | 874 |
| `List<Int>` | 2,161 | 968 | 824 | 970 |

About 85% of the Σ-η work and nearly all the `Unit` checks were the tag.
A `Bool` comparison was almost nothing else; the `Nat` payload of an `Int`
cost about one call. Evaluation was small beside it: a copying `match` adds
about 13 steps per element, rebuilding each `Int` about 20.

This was found while costing a kernel mechanism for `Int`-shaped values
([[bv-omega-check-cost]]): the per-element cost of omega's coefficient rows
was per encoded operation, and most of that operation turned out to be the
tag.

## Fix

The tag is now `sEq⁰(Nat; k; k)`, inhabited by `srefl` — irrelevant by
`sEq`'s own conversion arm (one call) rather than by an η derivation, and
still distinct per declaration because type conversion compares an `sEq`'s
endpoints. §3.3 of the tier-0 lowering states what it means and the three
obligations it carries (one spelling of `k`, no casts along a tag, the
evaluator's finite-type readers know the tag). A dedicated kernel label former is the
alternative if borrowing a proposition ever costs more than it saves.

## What else had to learn the tag

The first full suite on the new tag found three places that recognised the
old shape structurally:

- **certgen's marker pass and in-language walker** (`certgen.rs::mark`,
  `lib/certgen_code.hthr`'s `transcribe`/`check_sig`) accept `Triv`/`Pair`
  and `Unit`/`Σ` as "pure"; they now also accept `srefl`/`sEq`.
- **The emission walker** flagged an `SRefl.ty` slot: `tag_value` copied
  `El ⌜Nat⌝` off a tag type that arrived as code. The inhabitant is now
  rebuilt from the index, always `srefl⁰(Nat; k)`.
- **The bit transducer's finite-state enumeration**
  (`eval/transduce.rs::enumerate`/`enum_value`/`read_enum`) knew only
  `Unit`/`Sum`/`Σ`. With `Bool` no longer enumerable, a register fold that
  carries a `Bool` stopped classifying and ran bit by bit: the x86
  `caller_native_exit_status` went from 147k evaluation steps to past its
  fuel. An `sEq` is now one state exactly when both endpoints are the same
  closed literal (`bits.rs::seq_is_unit`); at unequal endpoints the type is
  empty and enumerating it would invent a state. `unit_inhabitant` uses the
  same test.

With those, the `stack_save` x86 build's total kernel evaluation steps went
from 11.5M to 7.9M (−32%), and no item moved up by more than a few steps.

## Acceptance

- The probe's comparisons lose the tag walk (per-former counts above).
- `scripts/perf ab` over the bv fixture and `lib/std/omega` reports the
  counters moving and no item regressing.
- Full suite green.

## Log

- 2026-09-26: LANDED. `scripts/perf ab --base HEAD` (3 interleaved cold samples each, every seconds row `separate`): `lib/std/omega` eval_steps 427,711 → 261,125 (−38.9%), kernel gate −15.4%, wall −14.7%; the bv fixture `bv_decimal_line` eval_steps 1,304,173 → 901,668 (−30.9%), gate −11.9%, wall −10.7% (`bv_place_step` −11.8%); `docs/showcase/calc_parser` eval_steps −42.6%, gate −17.3%. conv_misses and eval_delta_steps flat (±3%): the same comparisons happen, each cheaper. No ranked item regressed. Full suite green (2,999 passed plus the moved Nat golden hash). Less than the 1.5–2× this issue's origin estimated for omega's gate: the rows' evaluation (`Int::mul`/`add` matches and projections) does not walk the tag, and it is now the larger part.
