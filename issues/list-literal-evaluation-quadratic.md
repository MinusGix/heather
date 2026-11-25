---
title: A [...] list literal costs evaluation steps quadratic in its length
status: open
labels: [kernel,elaboration,performance]
area: language
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Found by [[reflected-languages-typed-by-construction]] (2026-11-25). A closed list written as a `[…]` literal costs the kernel's evaluator a number of steps quadratic in its length the first time something reads it; the same list spelled `Cons(…, Cons(…, Nil))` is linear.

The measurement: `Steps::apart(m_xs(), m_ys()) = Some(Nil)` by `refl`, with `m_xs` and `m_ys` two `List<Step>` of length `n` declared as `fn`s (`lib/lang/ownership/steps.hthr`), `heather check --timings`, release, width one. The `steps` column of the theorem's row:

| n | `[…]` | `Cons` spine |
|---|---|---|
| 32 | 11,302 | 2,048 |
| 64 | 40,774 | 3,840 |

The `[…]` column grows about fourfold per doubling and the `Cons` column twofold; `m_get` (a read through `Val::place` of the same list) shows the same split. The literal goes through `CollectionLiteral<List<A>>`'s `fromLiteral`, a `fold` over the vector (`lib/std/data/list.hthr`), whose fold is the container schema on the vector's length (`crates/elab/src/vec.rs`); which part is quadratic is not attributed. The absolute cost is small at the lengths the library writes, but every reflected program the checker evaluates is a literal of this kind once a reflector emits one.

## Done when

A literal of length `n` costs evaluation steps linear in `n`, measured as above at doubling lengths, or the quadratic part is attributed and a decision recorded.

## What it assumes from elsewhere

- **[[collection-literal-resolution-per-literal]]** owns the literal's elaboration cost (resolution per literal); this issue is about evaluating the elaborated term.

## Log

- 2026-11-25: 2026-11-25: Attributed and fixed. Not the fold, the vector's indexing or the evaluator: a literal of three distinct values was already linear and cheaper than its spine; the quadratic part was capped at 64 elements (the verdict's δ-steps were identical at 64 and 128). It was the **packed `VecLit` tail** (`ExprElab::packed_vec_tail`: the last ≤64 elements of a literal at a sum element type with at most two distinct values, which `Step` probes and `List<Bool>` literals hit). `collection_literal_spine` builds the literal's `Cons` spine at elaboration and contracts each element's projection off the literal's vector, but its `projected` read through a `Pair` and a `VecItems` only, so each element past the packing point kept a `fst(snd(…snd(VecLit)))` chain from the literal's root as deep as its position, walked once per element. Fix: `projected` reads a `VecLit` through `term::vec_lit_unfold`, as it read `VecItems` — the general spine walk, every container's literal, nothing keyed on `List`. After it a literal's read is linear in its length and a little cheaper than the same list as a `Cons` spine (the probe above at 16 to 128, both verdicts). `scripts/perf ab` (width one, three samples, counters): length 64's `apart` verdict down by about 15×, length 32's by about 8×, a 64-element `List<Bool>` read by about 5×; the showcase `calc_parser`'s diagnostic items down 1–2% of their steps (their short literals pack); nothing else moved. Neighbours: string literals, byte strings at `List<u8>` and `[Bool; n]` vector literals were already linear (characters and bytes do not pack; a vector literal is read natively as a bit run); literals past 256 elements (`VecItems`, a 64-element spine head and the fold after it) linear before and after; there are no set or map literal instances (`CollectionLiteral` has one instance, `List`), and a tuple of literals is its literals. Every other elaborator reader of a literal vector (`shown.rs`, `module_image.rs`, `emission_walk.rs`) already handled both packed forms; the packed-literal design (`docs/kernel/bitvector-literal-entry-design.md` §3.1) now says every reader must. Pinned: `list_literals::a_packed_literal_is_read_in_evaluation_steps_linear_in_its_length` — a packed literal's verdict costs no more `eval_steps` than its spine at 16/32/64 and its increment per doubling at most doubles; it fails without the fix (where the totals grew only 2.5× and 2.9× per doubling at those lengths, so a ratio-of-totals bound would not have caught it).
