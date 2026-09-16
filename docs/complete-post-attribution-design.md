# `parser_primitives::complete_post`: what the twenty seconds are — design

Attribution pass on `issues/parser-certified-composition-cost.md`'s 2026-09-15
closing line ("`complete_post` unmoved at ~21 s and is now the largest item:
attribute it next"), 2026-09-16. `docs/showcase/calc_parser.hthr` on the
`43a968f` tree, release with `--features value-metrics`, one furnace E5 box,
`--kernel-workers 1`, no `--cache` anywhere.

Every number below was hand-run in this pass on that box. Ten furnace round
trips and nineteen reproducer files; `probes/cp_*.sh` and `probes/t_cp*.hthr`
are what a reader re-runs, and `probes/README.md`'s round section says in what
order. No source change lands here.

**The headline is that four hypotheses died and the fifth is not a
conversion rule.** The item is not the instance matcher's residue, not the
`Pi`/`Pi` row, not the open type parameters, not the equation's element type
and not the type-argument slot — all five were measured and all five are
negative. What survives is a law with no exceptions in nineteen probes: a
`→ Type` function whose body is a **declared type former with
binder-dependent components** costs one fixed block of conversion misses per
such component, and the same component written as the whole of the body costs
nothing. `CompleteSpec` has two of them. That is 16 s of the item's 20 s.

---

## 1. The datum, from the trace and not from the hypothesis

The premise first (`probes/cp_premise.sh`), untraced, because a traced run
inflates this item's `total_ns` 2.6×. `complete_post`'s whole row, the columns
that are not zero:

```text
item  parser_primitives  complete_post
  total_ns        20 334 739 909      kernel_gate_ns  15 654 760 644
  decl_body_ns     2 369 062 689      decl_emit_ns       824 045 594
  elab_whnf_ns       890 027 125      other_ns           516 019 765
  matching_ns         60 597 422      decls_gated                  2
  check_terms                  1      conv_memo_hits               8
  conv_shortcut_hits   5 726 206      conv_misses            110 851
  eval_steps           7 675 169      eval_delta_steps       377 963
```

The run it sits in is 74.2 s wall, 73.3 s over the item rows, 58.4 s of kernel
gate, 319 877 misses and 13.67 M evaluator steps. So this one seven-line
library theorem is **27 % of the showcase's time, 35 % of its conversion
misses and 56 % of its evaluator steps**, and it is the largest item by a
factor of three over `close_body` (6.39 s), `factor_body` (2.68 s),
`expr_body` (2.65 s), `number_grammar` (2.60 s) and `checked_expr` (2.01 s).
Its own module, `parser_primitives`, is 21.5 s of which it is 20.3 s; its
neighbours in that module are ordinary (`recognize_post` 370 ms,
`complete_sound` 254 ms, `recognize_bound` 231 ms, `recognized_head` 189 ms,
`eof_at` 5.8 ms, `complete` 0.8 ms). `check_terms = 1`: the 15.65 s is **one**
proof obligation handed to the kernel once.

### 1.1 Half the gate is not conversion misses

`probes/cp_trace.sh` runs `HEATHER_CONV_MISS_TRACE=complete_post` and sums the
sampler's own clock over the 110 851 records. The sampler brackets exactly
`conv_type_cached_with_metrics` and nothing else — the excerpt and the
backtrace it prints are outside the measured window — so the sum is what the
misses cost:

```text
records = 110 851      summed = 7 324.7 ms
```

Against a 15.65 s gate. **The misses are 47 % of it.** The rest is the
traversal that issues them: 5 726 206 conversion queries that the syntactic
reflexivity shortcut answered, one per node of a term the kernel walks once.
The same is true of the run as a whole — the value-metrics head-pair table's
top twenty rows total 24.4 s against a 58.4 s gate.

This matters for what may be concluded. A miss count is not the item's cost
here and a head-pair row is not a diagnosis; §3 measures both sides of the
split at once by measuring counts.

### 1.2 What the misses are

`trace_agg.py`'s head-pair table for the item, and the whole records bucketed
by their `expected len=… inferred len=… first difference at …` signature
(`trace_agg` truncates at 260 characters and hides the excerpt, so the
bucketing is `s4_excerpt.sh`'s read):

```text
count      ms   head pair     bucket signature
29 560  1 749.5  El⌜⌝/El(?)   expected len=732   inferred len=50    at 6
14 762  1 733.3  El(?)/El⌜⌝   expected len=187   inferred len=1341  at 6
 8 299  1 453.9  Sigma/Sigma  expected len=3512  inferred len=1250  at 8
14 762  1 356.2  Sigma/El⌜⌝   expected len=2064  inferred len=3284  at 0
14 816    601.3  Sum/El⌜⌝     expected len=281   inferred len=409   at 0
14 780     45.6  Nat/El⌜⌝     expected len=3     inferred len=14    at 0
 7 267     18.5  El⌜⌝/Unit    expected len=17    inferred len=6     at 0
```

Read off it:

1. **87 % of the misses are the quote pair.** 95 947 of 110 851 records carry
   `El⌜⌝` on exactly one side, and 5.50 s of the 7.32 s. The `Nat/El⌜⌝` row is
   `Nat` against `El[0](«Nat»)`, 14 780 times — the *group A* excerpt of
   `docs/closed-argument-and-parameter-domain-spelling-design.md` §5.2, whose
   amendment predicted it would be left behind by the name slice and whose
   owner is `issues/quote-see-through-bounded-arm`. The dominant row's
   expected side is a 732-character `El «Wf «(«Σ[0,0](«Σ[0,0](«Unit 0»)…`
   against a 50-character inferred side: the inline lowering, quoted, meeting
   the spelled form.
2. **Every bucket repeats between 7 267 and 29 560 times at ONE site.** The
   `site:` lines cross with the head pairs almost one to one:
   `Nat/El⌜⌝` is 14 780 records at `Var < App < App < App < App < TmSigma ×11`,
   `Sum/El⌜⌝` is 14 762 at `Var < Case < Case < TmWf < TmWf < TmId < TmId <
   TmSigma ×9`, `El⌜⌝/El(?)` is two site variants of 14 744 each. The kernel
   is checking the well-formedness of a code — `TmSigma`, `TmId`, `TmWf`
   formation rules — and at each leaf of it re-asking one conversion.
3. **The memo cannot help and is not the finding.** `conv_memo_hits = 8`. The
   cross-head memo is keyed on Ψ and Γ identity, and these 14 780 queries sit
   at 14 780 different Γs as the formation walk descends. There is no trace
   here of the same syntax at the same Γ repeating, so no kernel memo is
   chartered (§6).
4. **`Pi`/`Pi` is gone from this item.** Two records, 25 ms. The previous
   round's row was `close_body`'s and stayed there.

### 1.3 What the brief's prediction got wrong

`issues/parser-certified-composition-cost.md` recorded the item's rows as
`El(?)`/`Wf`, `El⌜⌝`/`El(?)` and `Vec`/`Sigma`, and the telescoped design
predicted "nested `s.end.offset` projection chains through `Success` then
`Cursor`". Only `El⌜⌝`/`El(?)` survives. `El(?)`/`Wf` (38 466) and
`Vec`/`Sigma` (30 725) are large rows of the **run** and neither is in this
item's top twelve; the projection-chain reading is refuted by §3's `cp3` and
`cp4`, where the whole chain is present and the item costs 37 ms and 17 ms.
Those rows were read off the whole-run table rather than off this item's
trace, which is the error `probes/README.md`'s per-module rule already warns
about in the other direction.

---

## 2. The reproducer is the theorem

`probes/t_cp1.hthr` is `complete_post`'s statement and proof copied verbatim
under the name `cp_full`, in a twelve-line file that imports `parser`. It does
not approximate the item; it **is** the item:

```text
                         total ms   gate ms    misses    shortcut     steps
parser_primitives::complete_post   20 294.3  15 724.9   110 851   5 726 206  7 675 169
t_cp1::cp_full                     19 096.1  15 380.8   110 851   5 726 206  7 675 169
```

Identical to the unit in all three counters, in the same process — every probe
run in this round re-elaborates the library too, so the library item is the
control on the same box in all ten jobs (15.5–16.1 s of gate, 110 851 misses,
every time). The 1.2 s of `total_ns` between them is the probe file's shorter
declaration prefix, and it is the only difference.

This settles the 2026-09-12 lesson the brief cites — "a unit miss reproduced
9× cheaper and the item did not follow" — in the other direction: there is no
unit, the reproducer is the whole item, and every subtraction below is taken
against a term that reproduces it exactly.

---

## 3. The table

Nineteen files, one variable each, all in `probes/`, all run with
`heather check -L lib/std -L lib/std/parser --kernel-workers 1 --timings`,
one process per file, no cache. Sorted by miss count.

| probe | item | what it changes from the base | total ms | gate ms | misses | shortcut hits | eval steps |
|---|---|---|---|---|---|---|---|
| — | `complete_post` | the library item, showcase | 20 334.7 | 15 654.8 | 110 851 | 5 726 206 | 7 675 169 |
| `t_cp18` | `cp_twice` | `And<relation(…),relation(…)>` | 26 645.5 | 21 689.7 | 151 369 | 7 792 204 | 10 429 811 |
| `t_cp6` | `cp_fixed` | `relation` a named declaration | 19 126.0 | 15 366.8 | 110 851 | 5 727 161 | 7 675 173 |
| `t_cp1` | `cp_full` | — (the base) | 19 096.1 | 15 380.8 | 110 851 | 5 726 206 | 7 675 169 |
| `t_cp15` | `cp_nateq` | the equation moved to `Nat` | 19 069.7 | 15 353.3 | 110 934 | 5 730 981 | 7 681 317 |
| `t_cp7` | `cp_local` | `CompleteSpec` re-declared locally | 19 002.3 | 15 274.7 | 110 851 | 5 726 206 | 7 675 169 |
| `t_cp13` | `cp_both` | `And` → a file-local record | 18 995.5 | 15 330.0 | 110 865 | 5 726 268 | 7 675 211 |
| `t_cp19` | `cp_rec` | conjuncts → **field types** of a record | 18 670.0 | 15 486.2 | 110 865 | 5 726 268 | 7 675 211 |
| `t_cp5` | `cp_mono` | `T`, `A` **closed** | 17 870.3 | 14 158.0 | 111 157 | 5 748 507 | 7 705 010 |
| `t_cp9` | `cp_andt` | `And<relation(…),True>` | 12 265.4 | 9 801.7 | 70 320 | 3 659 609 | 4 920 110 |
| `t_cp12` | `cp_teq` | `And<True,rest(…)=Nil<T>>` | 10 093.6 | 7 874.3 | 56 818 | 2 971 143 | 4 001 983 |
| `t_cp16` | `cp_tnateq` | `And<True,list_len(…)=0>` | 10 072.9 | 7 881.5 | 56 901 | 2 975 918 | 4 008 131 |
| `t_cp17` | `cp_le` | `And<nat::Le(…,…),True>` | 8 194.5 | 6 252.7 | 43 330 | 2 283 855 | 3 085 575 |
| `t_cp14` | `cp_nest` | `And<And<True,True>,True>` | 3 464.9 | 2 667.0 | 16 293 | 904 566 | 1 246 955 |
| `t_cp11` | `cp_tt` | `And<True,True>` | 3 346.9 | 2 562.3 | 16 287 | 904 546 | 1 246 909 |
| `t_cp10` | `cp_wrap` | body = `relation(…)`, wrapped | 3 194.5 | 2 456.3 | 16 282 | 904 535 | 1 246 937 |
| `t_cp8` | `cp_eq` | body = `rest(…)=Nil<T>` alone | 3 145.2 | 2 400.6 | 16 282 | 904 535 | 1 246 946 |
| `t_cp2` | `cp_plain` | the plain `relation` | 3 137.4 | 2 394.3 | 16 282 | 902 591 | 1 246 929 |
| `t_cp3` | `cp_pure` | `pure_at` continuation, no inner match | 36.8 | 18.0 | 7 | 8 955 | 3 211 |
| `t_cp4` | `cp_floor` | no combinator in the conclusion | 16.5 | 7.8 | 6 | 3 840 | 2 967 |

### 3.1 The gate is one line

`kernel_gate_ns ÷ conv_shortcut_hits` over the whole table: 2.03, 2.01, 2.65,
2.71, 2.65, 2.83, 2.95, 2.74, 2.65, 2.65, 2.68, 2.68, 2.67, 2.69, 2.46, 2.68,
2.78 **µs**. Nineteen probes, a 2 000× range of counts, one constant.

So `kernel_gate_ns` carries no information that `conv_shortcut_hits` does not,
the misses and the traversal are in a fixed ratio to each other (misses are
1.80–1.95 % of queries and evaluator steps are 1.34–1.38 per query in every
variant from `cp_plain` up), and **the item's cost is the size of the term the
kernel is handed, nothing else.** A conversion rule, a memo, a shortcut or a
spelling that made a query cheaper would move the constant; nothing here does,
and the design must not propose one. Read the table by counts.

### 3.2 Five hypotheses, five refutations

- **It is not the projection chains, the combinators or the two matches.**
  `cp3` keeps the whole `bind_at` over the open `r`, keeps `Success`/`Cursor`
  and every `s.end` read, and costs **37 ms**; `cp4`, with no combinator at
  all, costs 17 ms. Everything above `cp_plain`'s 3.1 s line is the conclusion's
  relation argument and nothing else.
- **It is not the open type parameters.** `cp5` closes `T` to a local
  two-constructor inductive and `A` to `Nat`, and moves the item by −7 %
  (111 157 misses against 110 851). The memory rule "complex types get a
  mundane verdict" applies literally: the cost does not come from
  polymorphism.
- **It is not the function-typed `relation` parameter.** `cp6` replaces it
  with a named generic declaration of the file's own — the naming slice
  `docs/closed-argument-and-parameter-domain-spelling-design.md` §4 rejected,
  applied to the library instead of the compiler — and the item is 19 126 ms
  against 19 096. Zero. `Pi`/`Pi` was never this item's row (§1.2 item 4) and
  naming its domains is not this item's slice.
- **It is not `logic::And`, and it is not the equation's type.** `cp13`
  replaces `And` with a two-field record declared in the probe file: identical.
  `cp15`/`cp16` move the second conjunct from an equation over `List<T>` — the
  `Wf`-lowered declaration that is also the run's largest `instance_match`
  decline (`issues/list-instance-match-wf-sigma-decline`, 27 886 rows) — to one
  over `Nat`: identical, twice.
- **It is not the type-argument slot.** `cp19` moves both conjuncts out of
  `And`'s type arguments and makes them the **field types** of a telescoped
  dependent record whose parameters are all value parameters — `Certified`'s
  own shape, the one the 2026-09-15 device named — and the item is 18 670 ms
  at 110 865 misses. This probe was written as the design's proposed library
  respelling and it refuted itself before it was recommended.

### 3.3 What is left, stated as a law

Every cheap row has a `→ Type` body that is **one former**: the plain
parameter (`cp2`), the relation applied (`cp10`), the equation (`cp8`), or a
former whose components are closed (`cp11`, and `cp14` nested a level deeper —
also free). Every expensive row has a body that is a **declared type former
with at least one component that mentions the function's own binders**.

The blocks are fixed and they add:

```text
  base, no dependent component            cp2/cp8/cp10/cp11/cp14    16 282
  + nat::Le(begin.offset, end.offset)     cp17                     +27 048
  + rest(source,end) = Nil<T>             cp12                     +40 536
  + relation(source,begin,end,value)      cp9                      +54 038

  predicted for both of the base's two:    16 282+54 038+40 536 =  110 856
  measured (cp1, cp7, cp13, cp15, cp19)                            110 851
```

Five parts in 110 851 — the two blocks are independent and exactly additive.
The block's size tracks the component, not its type: 27 k for a global applied
to two cursor offsets, 40 k for an equation (at `List<T>` or at `Nat`, the same
number), 54 k for an application of the open relation parameter. A component
that mentions nothing (`True`) costs zero, at any nesting depth.

`cp18` is the one row that is not exactly additive: the **same** component
twice charges +135 087 rather than +108 076, 2.5× one occurrence rather than
2×. Two distinct components add; two copies of one over-add. Recorded as
measured; §8 item 5 asks the implementer to re-read it rather than a
paragraph here guessing why.

---

## 4. The mechanism, named against the existing vocabulary

The trace says the comparisons are quote-against-spelling (§1.2), the decline
listing says no naming device is even being asked, and the table says the
count is charged per binder-dependent component of a declared former. Together
they name one thing, and it is the oldest of
`issues/elaborator-canonical-type-spelling`'s three spellings.

**The decline listing first, because it is a clean negative.**
`probes/cp_declines.sh` runs `HEATHER_GENDEF_DECLINES=1` on `t_cp1` and on
`t_cp2` — the base and the 6× cheaper variant — and the two listings are the
same to two lines out of 252 847, row for row in the same order
(`respell_ty_at False no-closed-code` 219 428, `instance_match List
hole-match-Wf/Sigma` 27 886, `instance_match List hole-match-Wf/Sum` 4 030, …).
And **neither listing charges a single row to the probe's own theorem**, nor
to `parser_primitives::complete_post`. So the per-instantiation type code, the
record-projection devices and the hole matcher are not declining here: they
are not consulted. The family that owned the last two rounds — §5.1's
residues, `hole-match-Wf/Sigma`, the receiver gate — owns none of this one.
That is worth stating plainly, because the natural next move after two
successful matcher slices is a third, and the listing says there is nothing
here for it to fix.

**What is left is the quote layer.** A type that is the *component* of a
declared former is carried in the emitted term as a **code**: a record's field
type and a former's type argument are both `code_of` of the component's
lowering, written by `crates/elab/src/code.rs`'s `code_of` at
`crates/elab/src/expr.rs`'s `quote_type_at` and at the type-argument path.
`code_of` is a pure structural rewrite — it respells nothing, and in
particular it does not go through `Elaborator::emit_ty`. The same type written
as the *whole* of a `→ Type` body escapes this, because there the body is
already an `El`, and `code_of` of an `El` is the identity (`code.rs`'s own
comment: "the code of a decoded code is the code"). That is the exact shape of
the split §3.3 measures, it is why `True` is free and a binder-dependent
component is not, and it is why the head pairs are `El⌜⌝` against everything.

This is `issues/elaborator-canonical-type-spelling`'s **third spelling**,
named on 2026-09-06 —

> the boxed literal is what the code layer writes … quoting the respelled
> type instead is this issue's next cheap slice

— and re-diagnosed there on 2026-09-10 as "the kernel's own substitution
result". It is `issues/emission-walker-residual-sites`' quote residue, whose
table already lists `Pair.fst_ty`/`Pair.snd_ty` as "`El ⌜Σ…⌝` ⇒ the inline Σ
(quote residue)" and whose note says the five-node listing's 578 findings
"every one carries an `El ⌜⟦Instruction⟧⌝` quote inside the slot — the quote
layer, [[elaborator-canonical-type-spelling]]'s residue, not this issue's".
Nine months of rounds have walked past it because on every previous workload
it was a row and not an item. On `complete_post` it is 16 s of 20 s.

### 4.1 Why it was invisible until now

Every earlier attribution ranked misses. The quote rows rank low by *seconds
per miss* — `Nat/El⌜⌝` is 14 780 misses for 45.6 ms — and they were repeatedly
read as noise beside a `Sigma/El(?)` or a `Pi/Pi` row worth whole seconds.
What §3.1 shows is that on this item seconds per miss is a constant, so the
ranking that matters is by **count**, and by count the quote pairs are 87 % of
the item. The two previous rounds' successes came from rows that were both
numerous and dear; this one is numerous and cheap, and the item is large
because there are so many of them.

---

## 5. The slice

**(a), an elaborator spelling.** Not a kernel rule and not a library
respelling; the argument for each is below.

The slice is the one its own issue named in 2026-09-06 and has never been
taken: **quote the respelled type.** `code_of(emit_ty(T))` in place of
`code_of(T)` where a component's code is written — `quote_type_at`
(`crates/elab/src/expr.rs:445`) and the type-argument path that reaches it
through `check_at_universe`, plus the field-type quoting that
`cp19` shows takes the same route.

The precedent is landed and measured, and it is a change of spelling at one
call. On 2026-09-13
`register_ty_code_fn` was changed from `code_of(template)` to
`code_of(emit_ty(template))` for exactly this reason
(`docs/record-projection-reference-design.md` §9.8; the entry on
`issues/elaborator-canonical-type-spelling` records item total 45.12 → 35.18 s,
kernel gate 35.30 → 25.47 s, steps 35.4 M → 16.1 M, **misses identical at
237 888**, one bucket 8.62 → 0.62 s and no bucket grown). That entry also
records the method this round confirms: "the sampler classifies a miss by its
root head pair; its cost lives in the component spelling after the unfold".
Here the same sentence is true of the *count*.

**What is not yet known, and must be measured before a line is written.**
`emit_ty` is `decode_deep` then `respell_ty_deep_in`: it names what has a
closed code. These components are open in the enclosing function's binders —
`relation(source,begin,end,value)`, `rest(source,end) = Nil<T>` — so what it
can change is their *components* (`List<T>`, `Cursor<T>(source)`, the element
type of the equation), not the argument as a whole. Whether that removes the
block, shrinks it, or leaves it is the spike's first hour and §8 item 1. This
design deliberately does not predict it: §3.2 killed four predictions in a row,
including one the design itself wrote down (`cp19`), and the discipline that
caught them is measuring before writing.

### 5.1 If the spike says `emit_ty` does not reach it

Then the finding narrows to a statement about the kernel that this pass has
**not** earned the right to charter: that a component code is re-decoded once
per node of the enclosing lowering, and — offered as a reading and not as a
measurement — that the elaborator has no spelling available that avoids it,
because the component mentions locals and the per-instantiation codes abstract
parameters rather than a local context. The owner would then be a
**bounded** `El ⌜⌝` arm — `issues/quote-see-through-bounded-arm`, whose trigger
("the `El⌜⌝` head pairs a top row after the name slice") this round's §1.2
fires — and the shape would be the bounded one that issue already specifies,
never an unbounded decode, which was built and overflowed the stack
(`docs/closed-argument-and-parameter-domain-spelling-design.md` §5.2). It is
named here so that the spike knows what its negative result means; it is not
chartered, because §1.2 item 3 shows no repeated syntax at a repeated Γ.

---

## 6. Rejected shapes, with reasons

- **A kernel memo, cache or conversion rule.** Refused on §3.1: the gate is
  2.46–2.95 µs per query across a 2 000× range, so there is no query that is
  unusually dear and nothing to memoize. `conv_memo_hits = 8` and the 14 780
  repeats of one bucket sit at 14 780 distinct Γs as the formation walk
  descends; the brief's own rule — do not charter a kernel memo without a
  trace showing the same syntax at the same Γ repeating — refuses it, and the
  trace refuses it.
- **A pointer-equality fast path in `conv_ty`'s reflexivity shortcut.**
  `Type`'s `PartialEq` is derived and fully structural where `CtxEntries`'
  is hand-written with an `Rc::ptr_eq` short-circuit and a comment saying why.
  It is tempting: 5.7 M structural comparisons is where half the gate goes.
  It is rejected as **this round's** answer because it is a constant-factor
  change to a number the defect should not be producing — 5.7 M queries for a
  seven-line theorem is the finding, and making each of them 30 % cheaper
  would bank a third of the item and retire the evidence that produced it.
  It belongs on its own issue with its own before/after and the
  `desktop-bench-gate-for-constants` protocol, not in a round whose subject is
  why the term has 5.7 M nodes.
- **Naming the function-typed value-parameter domain** (the `Pi`/`Pi` slice
  `docs/closed-argument-and-parameter-domain-spelling-design.md` §4 rejected
  and `issues/parser-certified-composition-cost.md` chartered as "next").
  Refuted here as well, and by the strongest kind of evidence: `cp6` does it
  *in the library*, at no compiler cost, and the item does not move. `Pi`/`Pi`
  is two records and 25 ms of this item.
- **Anything in the instance-matcher family.** The decline listing is
  identical between the base and the 6× cheaper variant and charges nothing to
  either theorem (§4). `instance_match List hole-match-Wf/Sigma` is real, is
  the run's largest decline row and keeps its own issue; it is not this.
- **A library respelling of `CompleteSpec`.** Two were tried.
  Moving the conjuncts into a telescoped dependent record's field types
  (`cp19`) changes nothing, and dropping a conjunct is not a respelling but a
  weaker theorem. The only respelling that is actually cheap is to stop
  conjoining — to state `complete_post` twice, once per conjunct — and that
  is refused on the standing rule that a dependent shape must be cheap at the
  root: `And<P, Q>` inside a `→ Type` body, with `P` and `Q` mentioning the
  parameters, is the most ordinary proposition this library can write, and
  `parser_contracts` would have to be shaped around a compiler defect to avoid
  it. Recording it as available and declined is the point; if a customer needs
  the 16 s before the slice lands, that is the lever, and it costs the library
  its conjunction.
- **Making `quote_type_at` respell by decoding on the kernel side instead.**
  Same objection as the unbounded quote arm, same stack overflow, same issue.

---

## 7. Cost, and the boundaries not moved

**Cost of the proposed mechanism.** `emit_ty` at a quote site is called once
per component written, at elaboration time, and what it materializes is a
spelling the emission chokepoint already computes everywhere else. The
2026-09-13 precedent at `register_ty_code_fn` took that workload's kernel gate
down 28 % (35.30 → 25.47 s) at an unchanged miss count. The risk is the
opposite one and is named in §8 item 3: a respelled quote is a *reference*
inside a code, and references are cheap to compare and dear to compute
through — the x86 certificates have
refused one twice (`issues/per-instantiation-projection-boundaries` boundary 2,
`caller_native_memory_same_27/28`).

**Persistence.** Nothing about registration, Ψ, `psi().bindings.len()` or the
image codec is proposed to change; what changes is which spelling a code that
is already written carries.

**The receiver gate, the dependency test, the hole matcher and the three
devices** are untouched. The listing says they never fire here.

---

## 8. Verification items for the implementer's first hour

Stop and report if any of these fires; each would refute part of this design.

1. **Does `emit_ty` change these components at all?** Before any edit: on
   `probes/t_cp1.hthr`, confirm that `emit_ty` of `relation(source,begin,end,
   value)` and of `rest(source,end) = Nil<T>` at the binder depth
   `CompleteSpec`'s body sits at returns something other than the input. If it
   returns the input, §5's slice cannot help and §5.1's fork is the answer —
   report that and do not write the one-liner to find out.
2. **The counts, not the seconds.** Every measurement in this round is a
   count; `kernel_gate_ns` is 2.46–2.95 µs per `conv_shortcut_hits` in all
   nineteen probes and will tell you nothing a count did not. The bar for the
   slice is `t_cp1`'s 5 726 206 conversion queries, and the sub-bar is
   `t_cp9`'s 3 659 609 and `t_cp12`'s 2 971 143 falling toward `t_cp2`'s
   902 591 — the block, not the total.
3. **The x86 rails do not move**, at two sizes, per item.
   `crates/elab/tests/function_ir_x86_scaling.rs` and
   `caller_native_memory_same_27/28` inside the default fuel. A quote that now
   carries a reference is the shape those gates have refused twice. A
   regression here is a design refutation and the report is the per-item
   scaling, never a raised budget (`issues/x86-scaling-rail-out-of-fuel`).
4. **The emission walker's residue list may only shrink.**
   `crates/elab/tests/ir_v1.rs`'s `WALK_RESIDUE` and the whole-library
   acceptance load. The quote rows this slice targets are literally the ones
   `issues/emission-walker-residual-sites` lists as not its own; if the list
   grows, the chokepoint and the quote layer have been put out of step.
5. **Re-read `cp18` before believing §3.3's additivity.** Two distinct
   components add exactly (110 856 predicted, 110 851 measured); the same
   component twice over-adds 2.5×. Whatever the slice does to the block, do it
   to `t_cp18` as well and say whether the two rows converge. If the additive
   law breaks under the change, the model in §3.3 was a coincidence of this
   one shape and the table has to be re-read before the round's claim stands.
6. **`complete_post`'s neighbours are the transfer test.** `close_body`
   (6.39 s), `number_grammar` (2.60 s), `checked_expr` (2.01 s), `expr_body`
   and `factor_body` (2.65 s each). If the slice moves `complete_post` and
   none of them, it is narrower than §4's mechanism claims and the design's
   generality — not its measurement — was wrong.
7. **The new tests vary the four axes** (`docs/testing-generated-terms.md`).
   The probes here already supply the shapes: a **literal** and a **neutral**
   scrutinee (`cp1`'s `match r` over a parameter, against a constructed reply),
   an **open** element type (`cp1`'s `T`) *and its closed control* (`cp5`,
   which must stay within a few percent of the open one — that equality is
   itself a finding of this round), a **checking** position (every probe here
   is a stated theorem whose proof is refused if the spelling is wrong), and
   negative controls: a spec with a false second conjunct refused, and the
   quote pair pinned exactly as
   `docs/closed-argument-and-parameter-domain-spelling-design.md` §7 item 7
   pins it, so the day the bounded arm lands the pinned test is the one that
   changes.
8. **Landing order.** The spike of item 1 first and on its own; then one
   commit for the spelling, with the showcase table taken serially and at the
   default width, `complete_post` and `close_body` named. Nothing else rides
   along — in particular not the reflexivity-shortcut fast path of §6, which
   would make the round unable to say which change moved the gate.

---

## 9. Status

Design only. No source change lands in this pass, `crates/` and `lib/` are
untouched, and `probes/cp_*.sh` plus `probes/t_cp*.hthr` are what a reader
needs to reproduce every number above. The open items this round hands on:
`issues/elaborator-canonical-type-spelling` gains its long-named third-spelling
slice with a customer worth 16 s; `issues/quote-see-through-bounded-arm`'s
trigger has fired but its charter waits on §8 item 1;
`issues/emission-walker-residual-sites` gains the attribution its table asked
for; and `issues/parser-certified-composition-cost` may not close — its own
condition is that `close_body` and `complete_post` become ordinary items, and
`complete_post` is now attributed but unmoved.
