# The sixteen million conversion queries: what issues them — design

Attribution pass on `issues/quoted-component-traversal-remainder.md`, the
remainder `docs/elaborator/complete-post-attribution-design.md` §10 filed on 2026-09-16:
the quote slice removed 87 % of `complete_post`'s conversion *misses* and 31×
its evaluator steps but only 36 % of its conversion *queries*, and the
showcase still spends 48.9 s of serial kernel gate on 16 762 944 of them.
`docs/showcase/calc_parser.hthr` and `probes/t_cp*@ef3961a` on the `a6ba37a` tree,
release with `--features value-metrics`, one furnace E5 box,
`--kernel-workers 1`, no `--cache` anywhere.

Every number below was hand-run in this pass on that box: four furnace round
trips, one instrument, five new reproducers. `probes/qt_*.sh@ef3961a`,
`probes/t_qt*.hthr@ef3961a` and `probes/qt_agg.py@ef3961a` are what a reader re-runs, and
`probes/README.md@ef3961a`'s round section says in what order.

**The headline is that the question was posed at the wrong end of the
pipeline.** The brief asked which kernel walk issues a million queries for one
equation's code, and expected a code-formation answer. The instrument says
code formation is **1.7 %** of them. 96.5 % sit in the `App` rule, at
application spines eighteen to thirty deep, and each is a two-microsecond
tautology: `Ty 0 ≈ Ty 0` at a type-argument slot, or a stored `Π` against the
`Π` the kernel just inferred for the same function. The kernel is not
re-walking anything. It is walking, once, a term that is **exponential in the
conclusion's combinator nesting** — measured over five points at base ≈ 3.5 —
and the elaborator that wrote it paid the same exponent three times over
before the kernel ever saw it.

---

## 1. The instrument

Today only a *miss* prints its site (`crates/kernel/src/typing.rs`'s sampler,
`self.diag_site()` at `typing.rs:627`). The queries that the syntactic
reflexivity shortcut answers at `conv_ty` — 3 681 039 of them for
`complete_post` against 14 210 misses — were invisible, and on a workload
whose gate is a flat cost per query that is the whole datum.

`HEATHER_CONV_QUERY_TRACE=<item>[:N]` (this pass's one source change,
`crates/kernel/src/typing.rs`, `#[cfg(feature = "value-metrics")]`, one
`Option` test per query when unset) prints every Nth shortcut hit of that
item as

```text
conv query trace <item> <head>/<head> size=<n> at=<addr> site: <f0> < <f1> < …
```

`size` is the bounded `Debug` length of the type compared — `fmt.rs`'s budget
makes it a *saturating* node measure, which is exactly what is wanted. `at` is
the address of that type, which is the only thing in the process that can say
whether the elaborator wrote one object and shared it or wrote one per
occurrence. The site is `diag_site`'s own stack, rendered by a
`diag_site_stack` that `diag_site` now opens with: one stack, one renderer, no
backtrace per query (a backtrace per *miss* is affordable; per query it is
three orders of magnitude more work than the query).

**The sanity check the brief demanded, on every probe in this round:**

| item | samples × 128 | `conv_shortcut_hits` | error |
|---|---|---|---|
| `cp_full` | 3 681 152 | 3 681 039 | +0.003 % |
| `cp_plain` | 680 576 | 680 369 | +0.03 % |
| `cp_andt` | 2 395 904 | 2 395 753 | +0.006 % |
| `qt_deep` | 7 928 320 | 7 928 179 | +0.002 % |
| `close_body` | 2 585 984 | 2 585 801 | +0.007 % |

The stride is the sampler's only bias and it is accounted. Read every table
below as queries, not as samples.

---

## 2. The datum: the site histogram of queries

`probes/qt_trace.sh@ef3961a` and `probes/qt_probe.sh@ef3961a`, on `perf/fixtures/matched_type_normal_form/t_cp1.hthr`
(`cp_full`, which `docs/elaborator/complete-post-attribution-design.md` §2 establishes
*is* the library item to the unit — 3 681 039 queries, 14 210 misses, 246 498
steps on both).

### 2.1 By rule frame — the answer to the brief's question

The frame is the innermost entry on the checker's stack that names a rule
family: a code's formation walk (`Tm…`), the `App` rule's own checks, an
eliminator, a binder.

```text
     3 552 384   96.5%  App annotation
        64 000    1.7%  code formation (TmUnit)
        51 968    1.4%  code formation (TmSigma)
         4 352    0.1%  other (Triv)
         3 584    0.1%  code formation (TmNat)
         2 048    0.1%  eliminator (Case)
         2 048    0.1%  other (Pair)
           640    0.0%  binder (Lam)
           128    0.0%  eliminator (ElimWf)
```

**Code formation is 3.2 % of the item.** The previous round's site column —
`Var < TmId < TmId < TmSigma ×10 < Fst < Fst < Snd`, ten Σ deep — is a true
description of where the *misses* were and a false lead for where the queries
are. `Case`, the eliminator the brief expected to find re-checking motives, is
2 048 queries out of 3.68 M.

### 2.2 By head pair, and why each query is a tautology

```text
     1 993 728   54.2%  Ty/Ty
     1 314 048   35.7%  Pi/Pi
       355 712    9.7%  El(?)/El(?)
         8 960    0.2%  Nat/Nat
         4 608    0.1%  Unit/Unit
         3 328    0.1%  Sigma/Sigma
           384    0.0%  Sum/Sum
           256    0.0%  Wf/Wf
           128    0.0%  El⌜⌝/El⌜⌝
```

Cross this with the innermost stack frame — `Var` 1 321 472, `App` 1 310 080,
`GlobalTm` 915 456 — and with the `App` rule as written
(`typing.rs:2012`, ch. 04's `t_app`):

```rust
self.ty_check(env, dom, dom_level)?;                  // the domain annotation
self.ty_check(&e, cod, cod_level)?;                   // the codomain annotation
let pi = Type::Pi { dom, cod, .. };
self.tm_check(env, fun, &pi, …)?;                     // ⇒ the Pi/Pi query
self.tm_check(env, arg, dom, dom_level)?;             // ⇒ the Ty/Ty, El(?) query
```

- **`Pi`/`Pi`, 35.7 %** is `tm_check(fun, &pi)`: the checker rebuilds the `Π`
  from the App node's two stored annotations and converts it against the `Π` it
  has just inferred for `fun` itself. It is the only place in these positions
  where a `Π` is an *expected* type.
- **`Ty`/`Ty`, 54.2 %** is `tm_check(arg, dom)` where `dom` is `Ty l` — the
  argument is a **type argument**, a code, and the query asks whether `Ty 0`
  converts with `Ty 0`. Its median bounded size is **4 characters**: 54.5 % of
  all queries compare a type under eight characters wide.
- **`El(?)`/`El(?)`, 9.7 %** is the same `arg` check at a value argument whose
  domain is a decoded reference.

So the gate's 2 µs is not buying a comparison that could be cheaper. It is the
per-node cost of the checker meeting a node. The count is everything.

### 2.3 By site shape — what the term is

The uncollapsed site table is useless here (100 % of stacks sit at the trace's
frame cap, 6 128 distinct keys at depth 40). Collapsing runs
(`probes/qt_agg.py@ef3961a`'s `collapse`) gives the shape:

```text
        44 800   1.2%  Var       < App×22 < Pair×12 < Snd×2 < Fst×2 < App
        39 296   1.1%  Var       < App×24 < Pair×12 < Snd×2 < Fst
        37 504   1.0%  GlobalTm  < App×22 < Pair×12 < Snd×2 < Fst×2 < App
        31 872   0.9%  Var       < App×20 < Pair×12 < Snd×2 < Fst×2 < App×3
        31 488   0.9%  App×23 < Pair×12 < Snd×2 < Fst×2 < App
        26 368   0.7%  App×21 < Pair×12 < Snd×2 < Fst×2 < App×3
        25 088   0.7%  GlobalTm  < App×24 < Pair×12 < Snd×2 < Fst
        24 448   0.7%  Var       < App×26 < Pair×12 < Snd
        23 680   0.6%  GlobalTm  < App×20 < Pair×12 < Snd×2 < Fst×2 < App×3
        23 296   0.6%  App×19 < Pair×12 < Snd×2 < Fst×2 < App×5
        …        6 110 more keys, 3 227 136 queries
```

Read it outward: an **application spine eighteen to thirty deep**, whose
arguments are type codes and cursor reads, sitting inside a **twelve-deep
`Pair` tower** — a `Wf`-lowered record *value*, written out — sitting inside a
projection chain, sitting inside another spine. `close_body`, which the quote
slice did not move at all, is the same family with the alternation repeated
rather than nested:

```text
         6 272   0.2%  GlobalTm < App×14 < Snd×2 < Fst×2 < App×2 < Fst×2 < App×12 < Snd×2 < Fst×2 < App
         5 120   0.2%  GlobalTm < App×10 < Snd×2 < Fst×2 < App×2 < Fst×2 < App×12 < Fst×2 < App×2 < Fst×2 < App×3
         5 120   0.2%  GlobalTm < App×16 < Fst×2 < App×2 < Fst×2 < App×12 < Snd×2 < Fst×2 < App
```

and its frame table is 98.9 % `App` with 1.0 % code formation — so the family
this round names is **not** the quote layer's and does not need a code at all.
That is the transfer answer `docs/elaborator/complete-post-attribution-design.md` §8
item 6 asked for, in the direction the §10.2 amendment predicted.

### 2.4 The addresses: the term is shared, and it is still that big

4 382 distinct addresses over 28 759 samples of `cp_full`; the single busiest
is one heap `Ty 0` object, four characters wide, standing as the `dom` of
**637 952** of the item's queries (17.3 %), and the second 243 456. So the
emitted term is heavily `Rc`-shared at its leaves — and §3 shows the whole
thing still grows exponentially, so sharing is not the missing idea (§6).

---

## 3. The multiplier

### 3.1 Component fixed, enclosing proof varied

The brief's step 3. `probes/t_qt1/2/3/5.hthr@ef3961a` hold the component at
`t_cp9`'s `CPAndT = And<relation(source,begin,end,value),True>` — the +1.72 M
block of §10.1 — and vary only the reply expression the conclusion's `Post` is
applied to. `probes/qt_probe.sh@ef3961a` and `probes/qt_scale.sh@ef3961a`, untraced, one
process per file, no cache.

| probe | item | the reply in the conclusion | queries | misses | steps | total ms | gate ms | `decl_emit` ms | `elab_whnf` ms | maxrss |
|---|---|---|---|---|---|---|---|---|---|---|
| `t_qt2` | `qt_floor` | `r` — no combinator | 6 495 | 21 | 738 | 27.2 | 12.0 | 0.9 | 6.5 | 1.41 GB |
| `t_qt1` | `qt_pure` | `bind_at(… pure_at)` | 390 503 | 1 469 | 27 174 | 1 379.6 | 725.1 | 63.7 | 259.2 | 1.41 GB |
| `t_cp9` | `cp_andt` | `bind_at(… map_at(eof_at))` | 2 395 753 | 8 860 | 162 499 | 7 005.4 | 4 390.1 | 433.3 | 711.0 | 1.41 GB |
| `t_qt3` | `qt_deep` | + one identity `map_at` | 7 928 179 | 33 780 | 525 244 | 25 268.1 | 15 301.2 | 1 579.2 | 2 517.3 | 2.78 GB |
| `t_qt5` | `qt_deeper` | + two identity `map_at` | 29 447 197 | 128 043 | 1 917 588 | 100 848.2 | 62 442.1 | 5 946.6 | 11 101.9 | 9.54 GB |

The added `map_at`s are `map_at(source,middle, INNER, λ (i: Nat) => i)`:
**identities**. They change no type, compute nothing, and add about thirty
characters of source each. The last three rows are 3.31× and 3.71× apart in
queries, 3.49× and 4.08× in kernel gate, 3.65× and 3.77× in emission, 3.54×
and 4.41× in the elaborator's own whnf clock, and 2.0× and 3.4× in resident
memory.

**The obligation is exponential in the conclusion's combinator nesting, base
≈ 3.5.** One line of source that computes nothing quadruples a hundred-second
item.

The same curve with **no** declared former in the body (the plain relation,
`probes/qt_curve.sh@ef3961a`): `cp_floor` 3 840, `cp_pure` 8 955, `cp_plain` 680 369.
Same shape, and the component multiplies it rather than replacing it.

### 3.2 Every phase pays the same constant

`kernel_gate_ns ÷ conv_shortcut_hits` across the five rows: 1 845, 1 857,
1 832, 1 930, 2 120 **ns**. `decl_emit_ns ÷` the same: 140, 163, 181, 199,
202 **ns**. Over a 4 500× range of counts, at three different phases of the
compiler.

That is the sentence this round adds to
`docs/elaborator/complete-post-attribution-design.md` §3.1. The flat gate is not a fact
about the kernel; it is a fact about the **term**. The kernel costs 1.9 µs per
node, the emission chokepoint 0.2 µs per node, the elaborator's normalization
0.3–1.0 µs per node, and all three are handed the same exponential object. A
change that makes the kernel cheaper per node caps at the gate's 62 % share of
`total_ns`; a change that makes the object smaller is worth the whole item.

### 3.3 Enclosing proof fixed, component varied

The other factor, from `docs/elaborator/complete-post-attribution-design.md` §10.1 on the
same binary — all five at the two-combinator reply:

```text
  base, the plain relation                cp_plain     680 369
  + nat::Le(begin.offset,end.offset)      cp_le      1 542 337   (+  861 968)
  + rest(source,end) = Nil<T>             cp_teq     1 967 610   (+1 287 241)
  + relation(source,begin,end,value)      cp_andt    2 395 753   (+1 715 384)
  both of CompleteSpec's two              cp_full    3 681 039
```

At a fixed proof the component multiplies the base by 3.52× (`cp_andt` over
`cp_plain`) and the blocks add exactly, as §3.3 and §10.1 record. At a fixed
component the proof's nesting multiplies by 3.5× **per layer, without bound**.

### 3.4 The verdict on (a)/(b)/(c)/(d)

The brief's four readings: (a) the occurrence count of the component in the
obligation, (b) the kernel re-checking a code's formation per decode, (c) the
size of the code itself, (d) something else.

**(b) is refused by §2.1** — code formation is 3.2 % and `Case` is 0.06 %.
**(c) is refused by §3.1** — the component is byte-identical across a 4 500×
range. What is left is (a), and its occurrence count is **(d)-shaped**: the
occurrences are not annotation slots the elaborator chose, they are the
`≈3.5ⁿ` copies of the reply's normal form that the elaborator's own
normalization produced before emission. The two factors, stated so that their
product is the block:

- **factor 1, the multiplier: ≈3.5 per nested combinator layer in the
  conclusion** — 6 495 → 390 503 → 2 395 753 → 7 928 179 → 29 447 197, five
  points, component byte-identical throughout;
- **factor 2, the per-occurrence cost: the component's own spelling**, ×3.52
  for `And<relation(…),True>` over the plain relation at a fixed proof, and
  the exactly additive `+0.86 / +1.29 / +1.72 M` blocks of §3.3.

`t_cp18`'s unexplained 1.25× over-add (the same component twice) is the same
phenomenon seen once: a repeated component is a repeated scrutinee, and
repetition is where this multiplier lives.

---

## 4. The mechanism, named

`Post(source,begin,relation,r)` is a `→ Type` function whose body **matches on
`r`** (`lib/std/parser/parser_contracts.hthr:31`). To check anything against
`Post(source,begin,CompleteSpec(relation), REPLY)` the elaborator must drive
`REPLY` to a constructor. `REPLY` is `bind_at(…, map_at(…, eof_at(…)))`; each
of those combinators is itself a `match` on its own argument
(`parser_combinators.hthr:25`, `:48`), and `Reply = Result<Success,Failure>`
is a two-constructor sum whose `Ok` payload is a three-field record. So one
layer of unfolding replaces the scrutinee by a **two-branch case whose `Ok`
branch rebuilds a record tuple**, and the next layer does it again inside both
branches. ≈ 3.5 copies per layer, which is the measured base.

The elaborator then **emits the result**. That is what §2.3's site shape is:
`Pair×12` is the rebuilt record value, `App×22` is the constructor spine that
fills one of its fields, `Snd×2 < Fst×2` is the field read that the next layer
took on it. The kernel's own evaluator is barely running — 1 917 588
`eval_steps` against 29 447 197 queries at `t_qt5`, 258 407 δ-steps — because
there is nothing left to evaluate. `elab_whnf_ns` is 11.1 s at that row: the
normalization happened in the frontend, once, eagerly, and its result was
written down.

The asymmetry is the defect. The **kernel's** conversion is lazy in δ
(`issues/kernel-lazy-delta-and-run-arithmetic`, `crates/kernel/DESIGN.md`'s
Algorithms section): handed `El (Post^δ …)` it would unfold only the head it
needs, and it memoizes nothing because it needs nothing. The **elaborator's**
path to an emitted annotation is eager: it whnfs to decide the match, and then
what it emits is the normal form rather than the application it started from.

### 4.1 The negative that settles the shape of the fix

`perf/fixtures/matched_type_normal_form/t_qt4.hthr` writes `t_qt3`'s reply **once, as a declaration**, and
applies it — the library form of "name it and let the reference stand", the
lever that worked twice this month (`docs/elaborator/record-projection-reference-design.md`
§9.8, `docs/elaborator/complete-post-attribution-design.md` §10).

```text
  t_qt3  qt_deep    7 928 179 queries   33 780 misses   25 268 ms   2.78 GB
  t_qt4  qt_named   7 917 550 queries   33 771 misses   25 559 ms   2.78 GB
```

**0.13 %.** Naming does nothing, because the elaborator unfolds the name and
normalizes exactly as before. So the fix is not a spelling the library can
reach and not a reference the emission chokepoint can substitute after the
fact; it is a question about *when* the elaborator normalizes and *what* it
writes down afterwards. This probe was written as the design's proposed
library lever and, like `cp19` before it, refuted itself before it was
recommended.

---

## 5. The proposed change, and its owner

**The elaborator, at the boundary between normalizing to decide and emitting
to record.** When a type's term argument has to be driven to a constructor so
that a `→ Type` body's `match` can reduce, the elaborator must keep the
*application it started from* as the spelling it emits, and let the kernel
unfold it on demand — instead of emitting the normal form it computed. The
machinery is the one that already exists: `Elaborator::emit_ty`'s
`respell_ty_deep_in` is the chokepoint that rewrites a spelling on the way
out, and the 2026-09-13 and 2026-09-16 rounds both landed by giving it one
more thing to rewrite. What it needs here is not a new device but a
*provenance*: the pre-normalization term beside the normalized one, so that
the slot can carry the former. The kernel accepts it — its conversion is lazy
in δ and `Post^δ` applied to a neutral reply is exactly the shape it already
handles — and every phase downstream of the decision then sees a term linear
in the source instead of `3.5ⁿ`. What the bar is, and how the implementer
learns in an hour whether this is reachable, is §8.

**Why not the kernel, argued against the alternatives.**

- The kernel's per-node cost is already flat and already small (§3.2), so
  there is no rule to make cheaper. The one rule change the trace *does*
  invite — a typed `App` rule that reads `dom`/`cod` off `fun`'s inferred type
  rather than checking two stored annotations and converting the rebuilt `Π`,
  the typing-side twin of
  `issues/conversion-typed-eliminator-congruence` — would remove the 35.7 %
  `Pi`/`Pi` row and both `ty_check`s at every App node. It is a real
  constant-factor win and it is **not this round's answer**, for the reason
  `docs/elaborator/complete-post-attribution-design.md` §6 refused the reflexivity fast
  path: banking 36 % against an exponential retires the evidence that produced
  it, and the next identity `map_at` takes it back three times over. It
  belongs on `conversion-typed-eliminator-congruence` with its own before and
  after.
- A **kernel memo** is refused on the brief's own rule and on the trace:
  `conv_memo_hits` is 3 193 against 3 681 039 queries, the Γ descends at every
  frame of a thirty-deep spine, and there is no repeated syntax at a repeated
  Γ anywhere in the histogram.

---

## 6. Rejected shapes, with reasons

- **Naming the reply.** Measured, §4.1, 0.13 %. The strongest kind of
  refutation: the proposed lever applied in the library at no compiler cost,
  and nothing moves.
- **Naming the component again** — a second round of the quote/reference
  slice, aimed at factor 2. Bounded above by 5.4× (`cp_full` over `cp_plain`)
  and it leaves the exponent untouched: `t_qt5` has one component and 29.4 M
  queries. Worth doing eventually, worth nothing as the answer to this issue.
- **Hash-consing or otherwise sharing the emitted term.** The term is
  *already* shared — 4 382 distinct type objects over 28 759 samples, one of
  them standing for 17 % of the queries (§2.4) — and it still grows 3.5× per
  layer in `decl_emit_ns` and in **resident memory** (1.41 → 2.78 → 9.54 GB).
  A DAG whose own size is exponential is not fixed by representing it as a
  DAG. Rejected on the memory column.
- **A kernel memo, cache or conversion rule.** §5, and
  `docs/elaborator/complete-post-attribution-design.md` §6, which this round's counts
  re-confirm rather than revisit.
- **A pointer-identity fast path in the reflexivity shortcut.** §2.4 says it
  would fire often — 17 % of `cp_full`'s queries are one object. Same
  objection as the last round's: a constant factor on a count the compiler
  should not be producing, with the `desktop-bench-gate-for-constants`
  protocol and its own issue, not a round whose subject is why the count is
  `3.5ⁿ`.
- **A library respelling — fewer combinator layers in the parser's
  contracts.** This is the lever that works, and it is refused. `map_at` of
  `eof_at` inside `bind_at` is the most ordinary thing this library writes,
  the identity layers of `t_qt3`/`t_qt5` are deliberately *not* a shape any
  library would write, and the standing rule is that a dependent shape must be
  cheap at the root and the library must not be designed around a compiler
  defect (`complex-types-mundane-verdict`,
  `library-drives-language-features`). Recorded as available and declined: if
  a customer needs the seconds before the fix lands, flattening a combinator
  chain is worth 3.5× per layer removed.

---

## 7. Cost, and the boundaries not moved

**This pass.** The only source change is the instrument (§1):
`#[cfg(feature = "value-metrics")]`, gated on an environment variable read
once through a `OnceLock`, one `Option` test per query when unset, no second
site stack. `scripts/test --fast` on the change: `== suite: 2556 passed, 0
failed, 5 ignored ==`. Nothing in `crates/elab`, `lib/`, the fixtures, the
`WALK_RESIDUE` list or the x86 rails is touched, and the instrument cannot
touch them: it prints and returns.

**The proposed change.** Emitting the pre-normalization application where the
elaborator today emits a normal form moves what the kernel is handed, so it is
the shape the x86 certificate gates have refused twice
(`issues/per-instantiation-projection-boundaries` boundary 2,
`caller_native_memory_same_27/28`): a slot that is cheap to compare and dear
to compute *through*. The kernel's δ is lazy and glued, so an obligation whose
head must be unfolded to decide a match will unfold it — once, at the head,
with fuel. §8 item 5 is where that is checked, and a regression there is a
design refutation.

**Not proposed to change:** registration, Ψ, `psi().bindings.len()`, the image
codec, the receiver gate, the dependency test, the three projection devices,
and the quote layer, whose slice landed yesterday and whose residue
(`El⌜⌝/El⌜⌝`, 128 queries here) is now beneath measurement on this item.

---

## 8. Verification items for the implementer's first hour

Stop and report if any of these fires; each would refute part of this design.

1. **Confirm the exponent before touching anything.** `probes/qt_curve.sh@ef3961a` and
   `probes/qt_scale.sh@ef3961a`: `t_cp9` 2 395 753, `t_qt3` 7 928 179, `t_qt5`
   29 447 197, with `elab_whnf_ns` and `decl_emit_ns` tracking within the
   ratios of §3.1. Three points, not one — a single pair is a slope, not an
   exponent (`rail-pass-is-a-floor`). If the exponent is not there on the
   current tree, this design is refuted and nothing below applies.
2. **Name the normalization site.** Which `elab_whnf` call drives `REPLY` to a
   constructor when `Post(…, REPLY)` is checked, and whether the pre-whnf term
   is still in hand at the point the annotation is emitted. If it is not — if
   the normal form is the only thing that ever existed at that point — then §5
   is a larger change than one call at one site, and the round's report is
   that fact, not a partial edit.
3. **The counts, not the seconds**, and the exponent, not the count. The bar
   is that the ratio between `t_cp9`, `t_qt3` and `t_qt5` falls toward 1 — the
   *shape* of the curve. `t_cp1`'s 3 681 039 and `close_body`'s 2 585 801 are
   the absolute sub-bars; the whole showcase is 16 762 944.
4. **No item may regress**, across all 944 joined rows of the showcase: not
   misses, not conversion queries, not evaluator steps. `probes/cp_gate.sh@ef3961a` is
   the per-item join and is the reading of the head-pair rule that survived
   `docs/elaborator/complete-post-attribution-design.md` §10.3.
5. **The x86 rails do not move**, at two sizes, per item:
   `crates/elab/tests/function_ir_x86_scaling.rs` and
   `caller_native_memory_same_27/28` inside the default fuel. Report the
   per-item scaling, never a raised budget
   (`issues/x86-scaling-rail-out-of-fuel`).
6. **`t_qt4` must stay within a percent of `t_qt3`** (§4.1). If the change
   makes them differ, the change is doing something other than what §5 says
   and the difference has to be understood before the numbers are believed.
7. **`WALK_RESIDUE` may only shrink** (`crates/elab/tests/ir_v1.rs`), and the
   full `scripts/test` — not `--fast` — is the gate, because this changes what
   the frontend emits.
8. **The four axes** (`docs/testing-generated-terms.md`) on the new pin: a
   literal and a neutral scrutinee, an **open** element type with its closed
   control, a checking position, and a negative control. The shape is
   `t_qt2`-against-`t_qt3`: one identity `map_at` between them, and the pin is
   that the emitted obligation's node count does not multiply. A unit-sized
   version of this pins nothing — the 2026-09-16 round dropped one for exactly
   that reason (§10.5 there) — so the probes are the cost gate and this doc is
   where they live.
9. **Landing order.** Item 2's spike alone and first. Nothing rides along, in
   particular not the typed `App` rule of §5 or the pointer-identity fast path
   of §6, either of which would make the round unable to say what moved the
   gate.

---

## 9. Status

Design only, and **§10 is the implementation pass's answer**: the spike of §8
item 2 stopped the round, so nothing under `crates/` changed here either. Read
§5 through §10.3.

The instrument is the one source change; `crates/elab`, `lib/`
and the fixtures are untouched, no commit is made, and `probes/qt_*.sh@ef3961a`,
`probes/t_qt*.hthr@ef3961a` and `probes/qt_agg.py@ef3961a` are what a reader needs to
reproduce every number above.

What this round hands on:

- `issues/quoted-component-traversal-remainder` is **answered and should be
  re-scoped**: the remaining block is not a quoted component's traversal at
  all. Its own question — "which walk asks ~1 M queries for one equation's
  code" — has the answer "none; the App rule asks 3.5 M tautologies for a term
  the elaborator normalized before emitting it", and the successor issue is
  about the elaborator's eager whnf, not the code layer.
- `issues/conversion-typed-eliminator-congruence` gains its **typing-side**
  twin with a measured customer: 35.7 % of this item's queries are the `Π`
  the App rule rebuilds from annotations that `fun`'s own inferred type
  already determines.
- The memory rule "computed-hypothesis shortcuts pay twice" gains its general
  case: not "elab whnf and the kernel both evaluate", but "elab whnf evaluates
  and the kernel then pays per node of the result, forever". Owner:
  `issues/elab-emits-normal-form-of-matched-type-argument`.
- `issues/parser-certified-composition-cost` still may not close.
  `complete_post` is 10.9 s and `close_body` 6.6 s, and §2.3 shows they are one
  family after all — `close_body` has no code in its histogram and the same
  `App`/`Pair`/`Fst` shape, so the transfer that §10.2 called "partly" is
  complete here even though the slice did not reach it.

---

## 10. Implementation, 2026-09-16: the spike, and the stop it fired

The implementation pass ran §8 items 1–2 before touching anything, as item 9
requires. Item 1 passed and item 2 **fired its stop condition**: the
normalization site is one call, the pre-normalization term is in hand at it,
and it is not a spelling any of the slots that are emitted there can carry.
Nothing under `crates/` changed. The instrument the spike needed is kept as
`probes/nf_spike.patch@ef3961a`; `probes/nf_*.sh@ef3961a` and `probes/nf_agg.py@ef3961a` are what a
reader re-runs, in the order `probes/README.md@ef3961a`'s round section gives.

### 10.1 The exponent, re-confirmed on the current tree (item 1)

`probes/nf_spike.sh@ef3961a`, `d53ec73`, release with `value-metrics`, one furnace
box, `--kernel-workers 1`, no `--cache`, one process per file.

| probe | item | queries | misses | steps | total ms | gate ms | `decl_emit` ms | `elab_whnf` ms | maxrss |
|---|---|---|---|---|---|---|---|---|---|
| `t_qt2` | `qt_floor` | 6 495 | 21 | 738 | 26.4 | 11.7 | 0.9 | 6.2 | 1.41 GB |
| `t_cp9` | `cp_andt` | 2 395 753 | 8 860 | 162 499 | 6 995 | 4 379 | 388 | 683 | 1.41 GB |
| `t_qt3` | `qt_deep` | 7 928 179 | 33 780 | 525 244 | 25 200 | 15 218 | 1 570 | 2 564 | 2.78 GB |
| `t_qt5` | `qt_deeper` | 29 447 197 | 128 043 | 1 917 588 | 100 997 | 62 251 | 5 850 | 10 915 | 9.54 GB |

Three points, and every count is §3.1's to the unit: ×3.31 and ×3.71 in
queries, ×3.48 and ×4.09 in gate, ×4.05 and ×3.73 in emission, ×3.75 and ×4.26
in the elaborator's whnf clock. **The design's premise holds on the tree the
implementation started from.**

### 10.2 The site, named (item 2)

`HEATHER_NF_SPIKE=<µs>` (`probes/nf_spike.patch@ef3961a`, `value-metrics` only) prints
every `Elaborator::whnf`, `whnf_tm` and `Elaborator::emit_ty` call that costs
more than the budget, with the item scope, the input's and output's bounded
`Debug` lengths and the elaborator frames that asked for it. Both clocks are
size proxies: `whnf` builds the reduct and `emit_ty` walks every node of what
it is handed. `--timings` is what opens the declaration scopes the `item=`
column reads; without it every record is attributed to `-`, which cost this
pass one round trip.

The exponent is **two calls per item**, and it is the same two in the library's
`complete_post` as in the probes (`probes/nf_site3.sh@ef3961a`, budget 20 µs,
milliseconds of self time, one record each):

| site | `qt_floor` | `cp_andt` | `qt_deep` | per layer |
|---|---|---|---|---|
| `whnf` at `build_ctor` | 5.4 | 492.6 | 2 213.5 | ×4.5 |
| `emit_ty` at `respell_spine < build_ctor` | 1.1 | 525.9 | 2 989.1 | ×5.7 |
| `whnf` at `matching::expose < synthesize_motive` | — | 113.7 | 140.9 | ×1.24 |
| every other record, summed | 1.5 | 13.3 | 107.3 | |

(the last row is every record the aggregator printed below the first three;
`qt_deep`'s 107.3 is 92.4 of it in one `ctor_here_expected` probe under the
same `wf_branch`. `qt_floor` has no combinator and reaches the same
`build_ctor` call one route over, under `elab_arm < case_tree`; the two rows
with a `Wf` match in them are the ones that scale.) The frames:

```text
whnf     < build_ctor < elab_check_skel_slots < check_lambda_at
         < elab_check_skel_slots < wf_branch < wf_case_tree < build_elim_wf
         < elab_match_wf < elab_match < elab_convoy
emit_ty  < respell_spine < build_ctor < …the same…
```

So, in the code:

- **The normalization site is `Elaborator::build_ctor`'s
  `let expected = self.whnf(cx, expected, span)?`** (`crates/elab/src/inductive.rs:1966`),
  reached when an arm body's constructor — `And(h, trivial)` — is checked
  against the branch type `tel.at(&inj, d)` handed down by `wf_branch`. The
  input is the match's motive instantiated at this constructor, printed as
  `El(case(…))`: a redex the reducer must fire, and firing it is where the
  `3.5ⁿ` object is built.
- **The emitter is the Σ/Sum spine of that reduct**: `spine(&expected, …)`
  decomposes it, `respell_spine` sends every component through the emission
  chokepoint, and `inject` writes them into the constructor value's
  `Inl`/`Inr` annotations, with `build_fields_skel` writing the rest into the
  `Pair` slots. That is §2.3's site shape, from the other end: `Pair×12` is
  this value, `App×22` is one component of it.
- **The motive is not the carrier.** The coordinator's first hypothesis —
  that a scrutinee-abstraction motive is abstracted out of a whnf'd expected
  type, and each branch's expected type is a copy of it — is refused by the
  clock: `matching::expose`'s whnf is 113.7 → 140.9 ms across a layer that
  multiplies everything else by 3.5. It is the **second** hypothesis that
  holds, one step further in than it was stated: the branch bodies are checked
  against a reduct, and what is written is not the lambda's domain but the
  *constructor value's* annotations.

### 10.3 Why §5 is not one site — the stop (item 2's second half)

The pre-normalization term **is** in hand at that call: `expected`, one line
above, un-normalized. It is nevertheless not what §5 needs, and the reason is
not plumbing:

> What `build_ctor` emits are the **components** of the reduct — the two
> summands of a `Sum`, the `fst`/`snd` of a `Σ`. The pre-whnf spelling is
> `El(case(…))`, whose sub-terms are not those components and do not
> correspond to them. The kernel's `Inl`/`Inr` and `Pair` rules take a
> former's components, not a term that reduces to the former, so there is no
> slot at this site into which "the application it started from" could be
> written.

§5's sentence — "keep the application as the spelling the annotation carries"
— presumes the annotation holds the type that was normalized. Here it holds a
piece of it. The mass inside those pieces is not a type either: it is the
**terms** the reply computed (the cursor and the value the combinator tower
produces), substituted into a type-code application. Their folded spelling
exists in principle — projections of the un-reduced reply — but recovering it
means the reducer telling its caller which sub-term of its output came from
destructuring which sub-term of its input. That is a provenance in
`reduce`/`oracle`, i.e. `crates/kernel`, and by the brief's own boundary this
round stops and reports rather than partially editing `crates/elab`.

Three consequences worth stating with the stop:

1. **The object is exponential, not exponentially repeated.** Resident memory
   tracks the queries (§6's rejection of hash-consing) and the emission
   chokepoint's own walk of it tracks them too (10.2's second row): a naming
   device over the reduct's components, the shape that fixed
   `issues/theorem-field-projection-oom`, buys the repetition factor and not
   the exponent. The exponent is in the reducer's output, and only not
   producing it removes it.
2. **The reducer's output is the substitution-expanded record tower.** Every
   layer of the tower rebuilds a record whose field types mention the previous
   layer's projections *with their annotations* — the same arithmetic as the
   projection OOM, one layer per combinator, which is what a base of ≈3.5
   looks like. `close_body`'s `App/Pair/Fst` shape (§2.3) is the same tower.
3. **The motive question (the coordinator's item 4) is moot for the fix and
   was not probed.** A motive constant in the scrutinee is refused by the code
   before any measurement — it is already `synthesize_motive`'s last fallback,
   reached only when abstraction fails, and the `Nil` branch of
   `match shape : rest(source,s.end)` type-checks precisely because the motive
   substitutes `Nil` into the reply and lets the tower compute. Keeping the
   un-normalized `Post(…, bind_at(…))` in the motive would leave the branch
   body facing a stuck type with only `shape` to transport along, which is a
   different proof, not a cheaper spelling of this one.

### 10.4 What this amends

- **§5 is amended, not withdrawn.** Its owner is right — the elaborator, at
  the boundary between normalizing to decide and emitting to record — and its
  site is now named to the line. What it cannot be is a substitution at
  `emit_ty`/`annotation_type`: the chokepoint is *downstream* of the reduct
  and is handed components, which is why routing this through
  `respell_ty_deep_in` (its first sentence) does not reach it. Read §5 with
  10.3's paragraph in place of "the machinery is the one that already exists".
- **§8 item 2 is answered** in both halves, and its stop is the one that
  fired. Items 3–8 were not reached: there is no changed binary to measure, so
  no curve, no per-item join, no rails, no `WALK_RESIDUE`, no bench. The full
  `scripts/test` was run once on the tree offered for review — which is
  `d53ec73` under `crates/` and `lib/` — as the check that the instrument left
  nothing behind: `== suite: 2696 passed, 0 failed, 5 ignored ==`.
- **§7's "proposed change" cost estimate is superseded**: this is not a slot's
  spelling and so it is not the shape the x86 gates refused twice. It is a
  reduction-provenance change in the kernel, and it needs its own design pass.

### 10.5 Two findings the spike produced in passing

- `emit_ty` at `respell_spine` spends 505 ms (`cp_andt`), 1 130 ms
  (`complete_post`) and 2 989 ms (`qt_deep`) walking one type — more than the
  `whnf` that built it — and returns a rewrite each time. The chokepoint has
  no short-circuit for a type whose components cannot respell; on this family
  that is a second full traversal of the exponential object per constructor
  value. Constant-factor, and its own issue.
- The declaration scopes that carry `item=` exist only under `--timings`
  (`crates/elab/src/stats.rs`'s `ITEMS`). Any future elaborator-side sampler
  has to be run with it or attribute nothing; worth a line in
  `docs/infrastructure/instrumentation-design.md`.
