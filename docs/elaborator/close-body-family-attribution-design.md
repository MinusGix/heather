# `close_body`, `expr_body`, `factor_body` and the two declarations: what the six million queries are — design

Attribution pass on the four unattributed rows of the showcase's conversion
bill, filed as the remainder of `docs/elaborator/projected-tuple-tower-design.md` §4.2:
candidate D moved `parser_primitives::complete_post` and **nothing else**, so
`calc_parser::close_body`, `expr_body`, `factor_body`, `number_grammar` and
the two declaration items `calc_parser::Grammar` and
`parser_contracts::Certified` do not go through the `build_ctor` reduct that
owns `complete_post`. Together they are 6.5 M conversion queries and ≈ 17 s of
serial kernel gate — more than `complete_post` — and this pass says what they
are instead.

Everything below was hand-run in this pass on one furnace E5 box, HEAD
`be365f3`, release with `--features value-metrics`, `--kernel-workers 1`, no
`--cache` anywhere: three furnace jobs, one instrument, six new reproducers.
`probes/cb_trace.sh@ef3961a`, `probes/cb_count.sh@ef3961a`, `probes/cb_decline.sh@ef3961a`,
`probes/t_cb*.hthr@ef3961a`, `probes/cb_agg.py@ef3961a` are what a reader re-runs, and
`probes/README.md@ef3961a`'s round section says in what order.

**The headline is that four of the six rows are one mechanism, it is not
`complete_post`'s, and it is a device that already exists and is declining.**
`close_body`, `expr_body`, `factor_body` and `number_grammar` spend half to
three quarters of their emitted nodes on **record field reads**, every dear
one of which took the `Fst`/`Snd` fallback walk because the named-projection
device declined at that receiver; the multiplier is **×14 per chained
receiver** and the per-read constant is **44× larger** for a record with an
unnameable function-typed parameter. Nothing on this path is normalized —
3.5 M queries at 22 conversion misses and 1 029 evaluator steps — so the
tower design's readback, which reads a *reduct* back from the value machine
at `build_ctor`, reaches none of them. The other two rows, `Grammar` and
`Certified`, are declaration items and are the price of the same device where
it *does* fire.

---

## 1. The instruments

Two, both `value-metrics`-gated and both reverted before this doc was offered:

- **`HEATHER_CONV_QUERY_TRACE=<item>[:N]`**, already in the tree since
  `d53ec73` (`crates/kernel/src/typing.rs`): every Nth conversion *query* the
  reflexivity shortcut answers for that item, with its head pair, the bounded
  `Debug` size of the type compared, that type's address, and the checker's
  own site stack. On a workload whose gate is a flat cost per query the
  queries are the datum and the misses are a remainder
  (`docs/kernel/conversion-query-traversal-design.md` §1).
- **`HEATHER_CB=1`** (`probes/cb_count.patch@ef3961a`, this pass's one source change):
  an exhaustive, unbudgeted **node counter**. One `cb decl` line per
  declaration — the tree size of exactly the `(statement, term)` pair the
  kernel is about to be handed, taken after the global substitution in
  `crates/elab/src/lib.rs` — and one `cb read` line per record **field read**
  (`Elaborator::project_field`), with the route it took (the named projection
  or the `Fst`/`Snd` fallback walk) and the tree size of the spine it built.
  The reused walker is `probes/tt_count.patch@ef3961a`'s `ttsimp::count_ty`, with a
  `count_tm` beside it.

  **Its one limitation, stated because a row in §5.0 shows it:**
  `probes/cb_agg.py@ef3961a` keys `cb decl` lines by the declaration's name and keeps
  the last, so an item that emits more than one pair is under-counted.
  Every row this doc argues from emits one; `checked_expr`, whose `decreases`
  lowering does not, is the visible exception and is not argued from.

**The item filter is the item's *bare* name.** `--timings` writes the module
in column 2 and the item in column 3, and both the query trace and the
elaborator's scopes compare against column 3 — `close_body`, not
`calc_parser::close_body`. A `module::item` spelling traces nothing and prints
no error; that cost this pass a round trip and is worth the line in
`probes/README.md@ef3961a`.

The sanity check every trace in this round passes — sampled lines × stride
against the item's own `conv_shortcut_hits`:

| item | samples × 128 | `conv_shortcut_hits` | error |
|---|---|---|---|
| `close_body` | 2 585 984 | 2 585 801 | +0.007 % |
| `expr_body` | 1 024 896 | 1 024 751 | +0.014 % |
| `number_grammar` | 1 101 056 | 1 100 958 | +0.009 % |
| `Grammar` | 458 880 | 457 050 | +0.40 % |
| `Certified` | 359 296 | 357 891 | +0.39 % |

---

## 2. The premise, re-measured on this tree

The showcase, serial, untraced, on HEAD (`probes/cb_trace.sh@ef3961a`, job 1):
**959 items, 64.66 s of item totals, 50.01 s of kernel gate, 212 318 misses,
16 762 944 queries, 4 697 239 evaluator steps.** The family, and its
structural siblings for scale:

| item | total ms | gate ms | misses | queries | steps |
|---|---|---|---|---|---|
| `parser_primitives::complete_post` | 11 184 | 7 010 | 14 210 | 3 681 039 | 246 498 |
| `calc_parser::close_body` | 6 773 | 5 454 | 7 318 | 2 585 801 | 90 912 |
| `calc_parser::factor_body` | 2 783 | 2 006 | 436 | 1 024 783 | 9 182 |
| `calc_parser::expr_body` | 2 727 | 1 981 | 420 | 1 024 751 | 9 150 |
| `calc_parser::number_grammar` | 2 653 | 2 123 | 14 289 | 1 100 958 | 366 547 |
| `calc_parser::checked_expr` | 1 581 | 1 038 | 17 995 | 520 342 | 325 493 |
| `calc_parser::Grammar` | 1 148 | 971 | 36 | 457 050 | 9 045 |
| `parser_contracts::Certified` | 814 | 642 | 36 | 357 891 | 5 320 |
| `calc_parser::sum_finish` | 368 | 304 | 593 | 112 563 | 127 623 |
| `calc_parser::product_finish` | 354 | 298 | 604 | 112 585 | 127 645 |
| `calc_parser::symbol_span` | 246 | 168 | 1 011 | 71 609 | 24 206 |
| `calc_parser::open_body` | 175 | 81 | 185 | 60 049 | 3 163 |
| `calc_parser::atom_body` | 161 | 113 | 88 | 84 162 | 4 911 |
| `parser_contracts::certify_at` | 84 | 48 | 210 | 34 196 | 4 137 |

The brief's table is reproduced to the unit, so the family is what it said it
was.

> **Reading this table later** (added 2026-09-17, `issues/timings-tsv-has-no-reader.md`).
> Its `queries` column is `conv_shortcut_hits` alone, not the sum of the three
> `Tc::conv_ty` outcomes that `scripts/timings` now calls `queries`; re-read it
> with `--columns shortcut`. Re-measured on that day's tree, the rows that do
> **not** go through the receiver chain reproduce to the unit —
> `complete_post` 3 681 039, `Grammar` 457 050, `Certified` 357 891,
> `symbol_span` 71 609, `certify_at` 34 196 — and the family's own rows have
> since halved, because `0245b31` taught the instance matcher to see through a
> quote: `close_body` 2 585 801 → 1 316 602 and 6 773 ms → 2 904 ms, `expr_body`
> and `factor_body` 1 024 7xx → 554 5xx. So this table is a record of its tree,
> not of the mechanism, and §3 onward is what carries over. Two rows of it are the round's first surprise and are worth reading
before §3:

- **`open_body` is `close_body`'s caller and costs 2.3 % of it.** It runs the
  same `result::fold`, over the same `Certified`, and hands its two receivers
  to `close_body`. What it does not do is *build* a `Certified` out of them.
- **`Grammar` and `Certified` are declarations** — a `record` line each, with
  no proof in them — and together they are 815 k queries, 1.96 s and
  **72 misses**.

---

## 3. The datum: the site histogram of queries

`probes/cb_trace.sh@ef3961a`, one traced process per item, `qt_agg.py` at stride 128.

### 3.1 By rule frame and head pair — five items, one profile

```text
item              App annot.  code form.  elim   binder   Ty/Ty  Pi/Pi  El(?)  other
close_body           98.9 %      1.0 %   0.005 %  0.005 %  53.1   36.9    9.0    1.1
expr_body            98.6 %      1.4 %   0.01  %  —        55.7   34.9    9.1    0.3
Grammar              99.5 %      0.03 %  —        0.5  %   52.1   34.8    9.9    3.2
Certified            99.4 %      0.1  %  —        0.5  %   54.9   37.2    7.8    0.1
number_grammar       96.2 %      1.8 %   1.9   %  0.03 %   48.6   30.6    7.8   13.0
(complete_post       96.5 %      3.2 %   0.06  %  0.02 %   54.2   35.7    9.7    0.4)
```

Read the first four rows and then the last: **the head-pair signature does not
identify a mechanism.** `Ty/Ty` a little over a half, `Pi/Pi` a little over a
third, `El(?)/El(?)` a tenth, inside the `App` rule, is what *every* item on
this workload looks like — a `record` declaration with 36 misses as much as a
proof-carrying `fn` with 7 318. It is the signature of the regime
(`docs/kernel/conversion-query-traversal-design.md` §2.2: the `App` rule checks a
`dom`, a `cod` and rebuilds a `Π`), not of what wrote the term. Attribution
here has to come from the emitter, and §5 is where it does.

`number_grammar` is the one row that breaks the pattern, and it breaks it in
the direction of `complete_post`: 1.9 % `Case`, 1.8 % `TmId` code formation,
4.9 % `Sigma/Sigma` and 4.8 % `Unit/Unit`, against 0.005 % / 0.5 % / 0.3 % /
0.02 % for `close_body`. It is also the only item of the five whose evaluator
is busy (366 547 steps against `close_body`'s 90 912 at 2.4× the queries).

### 3.2 By site shape — a projection chain, not a tuple tower

Collapsed site shapes (`qt_agg.py`'s `collapse`), the top rows of each:

```text
close_body   GlobalTm < App×14 < Snd×2 < Fst×2 < App×2 < Fst×2 < App×12 < Snd×2 < Fst×2 < App
             GlobalTm < App×16 < Fst×2 < App×2 < Fst×2 < App×12 < Snd×2 < Fst×2 < App
             GlobalTm < App×30 < Pair×9
expr_body    GlobalTm < App×22 < Snd×2 < Fst×2 < App×2 < Fst×2 < App×9
             GlobalTm < App×30 < Lam < App×4 < Lam < App×2 < Lam
             Var < App×39
Grammar      GlobalTm < App×39        /  GlobalTm < App×28 < Fst×2 < Lam×6
Certified    Var < App×39             /  App×25 < Fst×2 < Lam×6
number_grammar  GlobalTm < App×26 < Snd×2 < Fst×2 < TmId×2 < App×4 < Lam < App×2
                GlobalTm < App×22 < Snd×2 < Fst×2 < App×6 < Snd×2 < Fst×2 < Pair×3
```

`complete_post`'s shape is `App×22 < Pair×12 < Snd×2 < Fst×2 < App` — a
**twelve-deep `Pair` tower**, the record *value* the reduct rebuilt, with a
spine filling one of its fields. The family here has no such tower: `Pair`
runs of nine and fourteen appear in `close_body` at 0.1 % each, and what
repeats instead is `App×n < Snd×2 < Fst×2 < App×m < Snd×2 < Fst×2 < …` — an
application spine, a **two-entry field read**, another application spine, and
again. That is a chain of reads, each of whose receivers is the previous
read.

The two declarations are the same picture with the chain replaced by the
`λΘ. λv. fst(sndʲ v)` bodies the device registers: `App×25…39 < Fst×2 < Lam×6`
is one `D#projⱼ`/`D#tailⱼ`/`D#recfamⱼ` body — six binders (`Certified`'s
`Θ` is `⌜T⌝, ⌜A⌝, source, begin, relation`, plus `v`), a `Fst` off the spine,
and a thirty-node application spine inside the annotations.

### 3.3 The addresses, and the one `Π` that is repeated

`close_body`: 2 968 distinct addresses over 20 203 samples. The busiest single
type object is one heap `Ty 0`, four characters wide, standing as the `dom` of
**431 872** queries (16.7 % of the item), the second 181 504. Under them sit
the stack-built `Π`s of the `App` rule — and the largest of those is **776
characters** of bounded `Debug` (the budget saturates near 2 330), repeated
15 872 times; `expr_body`'s equivalent is **911** characters, 6 784 times.
A `Π` that wide, at a field read, is `Certified`'s function-typed `relation`
parameter domain written out: the object
`docs/elaborator/telescoped-record-projections-design.md` §5's amendment named as the
next slice, seen from the query side.

Size distribution, `close_body`: p50 **4**, p90 79, mean 49.4, max 2 388;
53.9 % of all its queries compare a type under eight characters wide, and
97.8 % of them sit at the trace's 40-frame stack cap.

## 4. The reproducers

`probes/t_cb1@ef3961a`…`t_cb6`, `-L lib/std -L lib/std/parser`, no `--cache`, one
process per file, untraced (`probes/cb_count.sh@ef3961a`, job 2). Every one of them is
under thirty lines and uses the **library's own** records — `Certified`, whose
third value parameter is function-typed, and `Success` for the control — so
nothing about the shape is modelled away. `t_pc3` and `t_pcr3` are the previous round's files, the same
three-receiver chain without and with that parameter.

| probe | item | what it is | queries | misses | steps | total ms | gate ms |
|---|---|---|---|---|---|---|---|
| `t_cb3` | `cb_one` | one receiver, no `le_trans` | 16 993 | 22 | 1 029 | 41.6 | 22.7 |
| `t_cb2` | `cb_two` | two chained receivers, one `le_trans` | 248 172 | 22 | 1 029 | 671.1 | 525.7 |
| `t_cb1` | `cb_full` | **three chained receivers, two `le_trans`** | 3 466 931 | 22 | 1 029 | 10 354.4 | 8 726.8 |
| `t_cb4` | `cb_nofold` | `t_cb1` without `result::fold` | 3 290 114 | 1 | 33 | 9 968.1 | 8 415.8 |
| `t_cb5` | `cb_trivrel` | `t_cb1` with a relation that ignores its cursors | 2 044 558 | 22 | 1 014 | 6 116.1 | 5 068.4 |
| `t_cb6` | `sb_nofold` | `t_cb4` on `Success` instead of `Certified` | 74 601 | 2 | 61 | 188.0 | 148.7 |

`cb_full` is **3 466 931 queries against the item's 2 585 801** — 1.34×, the
one component this probe writes twice that `close_body` writes once (its
`evidence` field repeats the `forward` chain, because the probe's relation
*is* `Le`). Every other column is the item's: 22 misses, 1 029 evaluator
steps. So the item is reproduced, and reproduced as a term-size measurement:
**nothing is being computed and nothing is being compared**. That is the
signature `docs/elaborator/telescoped-record-projections-design.md` §1 gives for the
tail-substitution exponent and for nothing else, and it is the opposite of
`complete_post` (14 210 misses, 246 498 steps).

Three readings, and they are §5's mechanism:

- **×14.0 per chained receiver**, over three points at a fixed everything
  else: 16 993 → 248 172 → 3 466 931 (×14.6, ×14.0). One more `Certified`
  whose `begin` is the previous one's `.end` multiplies the item by fourteen.
  `complete_post`'s curve is ×3.5 per combinator layer; this is a different
  and much steeper one.
- **`result::fold` is 5 %.** `cb_nofold` builds the same value from the same
  three receivers with no eliminator at all and keeps 95 % of the queries
  (and drops to **one** miss and 33 evaluator steps). The motive, the
  eliminator and the two lambdas are not the mechanism, which refutes the
  brief's `result::fold`-motive candidate outright.
- **The relation is 41 %.** `cb_trivrel`'s `CR` returns `True`, so the
  `evidence` field is `trivial` and the `relation` argument of every read is a
  constant function: 3 466 931 → 2 044 558 with the chain unchanged. That is
  factor 2 (§5), and the remaining 2.0 M is the chain itself.

---

## 5. The multiplier, and the two factors

### 5.0 The node counter: the item *is* its emitted term, and half of it is field reads

`HEATHER_CB=1` on the showcase (`probes/cb_count.sh@ef3961a`, job 2). The `TOTAL
nodes` column is the tree size of the `(statement, term)` pair the kernel is
handed, counted exhaustively at the emission chokepoint's exit; `reads` is
the number of record field reads `project_field` answered inside that item.

```text
item              stmt      term    TOTAL nodes    queries   q/node   reads
complete_post    10036   7551286      7561322     3681039     0.49        1
close_body        4496   5556122      5560618     2585801     0.47       47
number_grammar     615   2964898      2965513     1100958     0.37       10
factor_body       1853   2197816      2199669     1024783     0.47       50
expr_body         1853   2197736      2199589     1024751     0.47       50
product_finish    1836    265094       266930      112585     0.42       16
sum_finish        1831    265044       266875      112563     0.42       16
symbol_span        738    190925       191663       71609     0.37        5
atom_body         1341    166756       168097       84162     0.50       18
open_body         1929    127212       129141       60049     0.46       24
certify_at         844     71855        72699       34196     0.47        9
checked_expr       541      7992         8533      520342    60.98       31
```

**0.37–0.50 queries per emitted node, over a 90× range of items**, and the
`stmt` column is a thousandth of the `term` column everywhere — so the cost is
the *body*, not the type, and `docs/elaborator/complete-post-attribution-design.md`
§3.1's "the item's cost is the size of the term the kernel is handed" is
confirmed a second way, by counting the nodes rather than by dividing a clock.

And the field reads are where the nodes are:

```text
close_body      47 reads, 2 663 034 nodes in them (48 % of the item)
   Certified  walk   18 reads x 115 666.9 mean = 2 082 004   (max 801 510)
   Certified  ref    11 reads x  26 571.7 mean =   292 289   (max 116 182)
   Cursor     ref    18 reads x  16 041.2 mean =   288 741   (max 121 518)
expr_body / factor_body   50 reads, 1 122 084 nodes each
   Certified  walk   11 reads x  78 332.0 mean =   861 652   (max 230 280)
   Certified  ref    18 reads x  11 889.3 mean =   214 007   (max  46 942)
   Cursor     ref    21 reads x   2 210.7 mean =    46 425   (max  34 968)
number_grammar  10 reads, 2 182 482 nodes in them (74 % of the item)
   And        walk    2 reads x 705 439.0 mean = 1 410 878   (max 746 121)
   Exists     walk    3 reads x 221 662.7 mean =   664 988   (max 287 583)
   RecognizedHead walk 5 reads x 21 323.2 mean =   106 616   (max  44 951)
complete_post    1 read, 1 187 nodes
```

The probes carry it over unchanged (`probes/cb_decline.sh@ef3961a`'s last phase), and
being controlled they also give the per-read curve:

```text
probe    item        TOTAL nodes   queries  q/node  reads   Certified walk reads
t_cb3    cb_one           35 601    16 993    0.48     14    4 x     4 967.2
t_cb1    cb_full       7 331 837 3 466 931    0.47     48   22 x   148 516.3
t_cb4    cb_nofold     6 958 281 3 290 114    0.47     40   20 x   161 341.6
```

**Twenty-two of `cb_full`'s twenty-two `Certified` reads are `walk`** — the
same `instance-args` decline as the library's, reproduced in a thirty-line
file — and between one chained receiver and three the *mean size of one read*
goes 4 967 → 148 516 while the count goes 4 → 22. Factor 1 is both of those
at once: more reads, each of them bigger, ×12.8 per layer on their product.

Two things are decided here. **`complete_post` has one field read of 1 187
nodes** — its 7.5 M nodes are not projections at all, which is the other half
of §6's "different mechanism". And in this family **the reads that take the
`Fst`/`Snd` fallback walk carry the mass**: 18 of `close_body`'s 29
`Certified` reads are `walk`, and they are 4.4× the mean size of the 11 that
take the named projection and 78 % of its read nodes. The device
(`docs/elaborator/telescoped-record-projections-design.md`) is *declining* at these
receivers, and §7.1's decline listing names which reads, one for one.

The 4.4× is a ratio between two sets of reads and not a controlled
comparison — a read deeper in the chain is bigger whichever route it takes,
and the two sets sit at different depths — so read it as "the mass is in the
declined reads", which the counts say outright, and not as "the route is
worth 4.4×". What the route is worth is a slice's measurement, and item 4 of
§8 is how to take it.

### 5.1 Factor 1 — ×14 per chained receiver

Three points on `Certified`, everything else fixed (`t_cb3`/`t_cb2`/`t_cb1`):
16 993 → 248 172 → 3 466 931, **×14.6 and ×14.0**. The previous round's
`probes/t_pcr3.hthr@ef3961a` — the same record, the same chain, and *no* constructor
and no `result::fold`, only `a.forward` / `le_trans(…)` — gives the same
curve on its own three items: `qchain1` 4 464 → `qchain2` 105 437 → `qchain3`
1 561 870, **×23.6 and ×14.8**, at **zero** conversion misses throughout.

A "chained receiver" is one binder whose record type is instantiated at the
previous binder's field: `inner: Certified<…>(source, op.end, CR)`. That is
the library's own idiom — `close_body` has three (`op`, `inner`, `close`),
`expr_body` and `factor_body` have two (`left`, `op`), `open_body` and
`atom_body` have one — and the items rank by that count: 60 049 (`open_body`) and 84 162
(`atom_body`) at one, 1 024 751 / 1 024 783 (`expr_body`/`factor_body`) at
two, 2 585 801 (`close_body`) at three. The items are a *ranking*, not a
curve: their bodies differ in everything else too (`close_body`'s two nested
`le_trans` against `expr_body`'s one, `open_body`'s zero), which is what the
probes hold fixed and why the controlled ×14 is quoted from them.

### 5.2 Factor 2 — the telescope's own domains, and the one that has no name

The same chain, the same depth, on records that differ only in their
telescope:

| record | its telescope | three-receiver chain | queries |
|---|---|---|---|
| `Success<T,A>(source,begin)` | `⌜T⌝ ⌜A⌝ source begin` | `t_cb6`'s `sb_nofold` | 74 601 |
| `Cert<T>(source,begin)` (`t_pc3`) | `⌜T⌝ source begin` | `chain3` | 45 083 |
| `Certified<T,A>(source,begin,relation)` | + **`relation`** | `t_cb4`'s `cb_nofold` | 3 290 114 |
| the same, `relation` applied | | `t_pcr3`'s `qchain3` | 1 561 870 |

**44.1× for one telescope entry** (`cb_nofold` over `sb_nofold`: the same
three receivers, the same two `le_trans`, the same `.end`/`.forward`/`.value`
reads, one constructor each). The counter says the two probes differ in
**route** as well as in size, and the two are not separable by these runs:
`sb_nofold`'s twelve `Success` reads all take the named projection
(mean 6 606 nodes), `cb_nofold`'s twenty `Certified` reads all take the walk
(mean 161 342). So the 44× is "a record with a function-typed parameter, as
the elaborator handles it today" — which is the number a fix has to beat —
and not a decomposition into "the domain is big" and "the matcher declines".
§7.1 says which of the two is which owner's.

The cleanest pair is the previous round's two files, which differ in nothing
else: `t_pcr3`'s `qchain3` and `t_pc3`'s `chain3` are the same three-receiver
chain with the same fields, one on `Certified` and one on a `Cert` without the
function-typed parameter. **Twenty-five reads each**, eleven of them on the
record: 11 × 156 596 nodes (all `walk`) against 11 × 4 279 (all `ref`) —
**36.6× per read**, 3 303 206 emitted nodes against 90 785, 1 561 870 queries
against 45 083, zero conversion misses on both sides.

The entry is `Certified`'s **function-typed**
value parameter, whose domain
`(source: List<T>) -> Cursor<T>(source) -> Cursor<T>(source) -> A -> Type`
is the 776-to-911-character `Π` §3.3 found repeated in the trace. A value
parameter of function type **has no name today**
(`docs/elaborator/telescoped-record-projections-design.md` §5's closing paragraph), so
the emission chokepoint has nothing shorter to write, and what it writes goes
into every `dom`/`cod` of every read's spine — which factor 1 then copies
fourteen times per layer.

The sub-factor inside it is the relation's own body: `t_cb5`, where `CR`
returns `True` rather than `Le(begin.offset,end.offset)`, is 2 044 558 against
`t_cb1`'s 3 466 931 (−41 %) with the chain unchanged. The domain is dear
because it is unnameable; the argument is dear because it is a type.

### 5.3 The emitter, named to the line

**`Elaborator::project_field`, `crates/elab/src/inductive.rs:2539`** — every
node §5.0 counted is written by one of its two routes, and both write the same
arithmetic.

**The fallback walk** (the `else` of that function, `inductive.rs:2614`
onwards, 78 % of `close_body`'s read nodes) is the one
`issues/theorem-field-projection-oom.md` named: per spine entry it takes the
`Σ`'s `fst`/`snd`, writes them into the `Fst`/`Snd` node's `fst_ty`/`snd_ty`
annotations, and then substitutes the projection it just built into the tail
for the next entry —

```rust
cur = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&proj)));
```

— so entry *j*'s annotations contain *j* copies of the receiver, and the
receiver at a chained binder is the previous read's whole walk. That is the
tail-substitution exponent, unchanged, at the receivers where the device did
not fire.

**The named-projection route** (`rec_proj_ref_at`, `gendefs.rs:2019`, into
**`saturate`, `gendefs.rs:3847`**) is four to ten times cheaper per read and
still has the same shape:

```rust
head = Term::App { fun, dom_level, cod_level, dom, cod, arg };
cur  = cod.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg)));
```

Two consequences, and together they are the multiplier:

- the `cod` of App node *i* is the **whole remaining telescope**, so a spine
  of `n` arguments writes the telescope's domains on the order of `n²/2`
  times — this is the constant factor, and `relation`'s domain is the
  dominant term in it (§5.2);
- `cur` has each argument **substituted in** before the next node, so an
  argument that is itself a read spine is copied once per later node —
  and at a chained receiver the `begin` argument *is* the previous read's
  whole spine. That is the ×14 (§5.1), and it compounds per layer.

Nothing is normalized on this path: `cb_nofold` is **one** conversion miss and
**33** evaluator steps for 3.3 M queries. The object is not a normal form and
no reducer produced it; it is the *argument substitution of a telescope*,
written as a tree.

---

## 6. The verdict, per item

**`close_body`, `expr_body`, `factor_body` — one mechanism, a sibling of
`complete_post`'s at a different emitter.** Not the same mechanism: no
`→ Type` body is being matched on, there is no `build_ctor` reduct (which is
why candidate D moved them by exactly zero), and the evaluator is idle —
`t_cb4` is 3.3 M queries at **one** miss and **33** evaluator steps. The same
disease: a graph written down as a tree, because the elaborator has no way to
say "this sub-term again". Where `complete_post`'s tree comes out of the
rewriter's reduct, this one comes out of **`project_field`** — 48 % of
`close_body`'s emitted nodes and 51 % of `expr_body`'s are its field reads,
and 78 % of those nodes are in the reads whose named projection *declined*
and fell back to the `Fst`/`Snd` walk with its tail substitution. The two
factors: **×14.0 per chained receiver** (three controlled points, §5.1) ×
**the per-read spine, 44× larger for a record with an unnameable
function-typed parameter** (§5.2). Emitter: `Elaborator::project_field`'s
fallback walk for the dear reads, `saturate` for the rest; the decline is
`instance-args` on `Certified`, 18 / 11 / 11 times.

**`number_grammar` — the same mechanism, a different declaration shape and a
different decline.** Its ten field reads carry **74 %** of its emitted nodes:
two `And` reads of 705 439 nodes each, three `Exists` reads of 221 663, five
`RecognizedHead` of 21 323, all ten on the fallback walk. What differs is why
the device declined — `And` and `RecognizedHead` hit the **receiver gate**
(`receiver_admits_reference` on a bare `Var`), which
`docs/elaborator/telescoped-record-projections-design.md` §4 deliberately kept for
non-dependent telescoped records because the x86 certificates cannot afford
δ + β per read. So its share is the *gate's* bill on the parser side and not
the matcher's, and it is the one row of the family whose fix has a measured
party on the other side (§7.1).

Its query profile is also the family's odd one out — 1.9 % `Case`, 1.8 %
`TmId` code formation, 4.9 % `Sigma/Sigma`, 14 289 misses and 366 547
evaluator steps — which is what a `Grammar(Number(w), trivial, …)` costs
around the reads: `Grammar`'s `valid` field is `WellFormed(derivation)`, a
`→ Type` body that matches on its argument
(`docs/showcase/calc_parser.hthr:45`), so `complete_post`'s mechanism is
present here too, at a one-layer scrutinee. On the node counter it is the
remaining 26 %, and this pass did not instrument `build_ctor` for this item;
what the counter settles is that it is the minority.

**`Grammar`, `Certified` — a third thing, already owned, and the *price* of
the other rows' fix.** These are declaration items: a `record` line each, 36
misses each, no proof in them. Their queries are the gate checking the
`3·nfields + 1` Ψ definitions `register_rec_projs` mints — §3.2's
`App×25…39 < Fst×2 < Lam×6` is one `D#projⱼ`/`D#tailⱼ` body, `Θ`'s six
binders and the annotations over them. That is
`issues/record-projection-defs-declaration-cost.md` exactly, with `Certified`
already in its table at 8.4 → 866.4 ms on 2026-09-15 (this pass reads 814 ms
and 357 891 queries; `Grammar`, a five-field record the issue does not list,
is 1 148 ms and 457 050). It is paid once per library module image and
replayed thereafter. **No slice here** — and a warning for the slices in §7:
making the device fire more often makes these two rows *bigger*.

---

## 7. The fix, and whose it is

### 7.1 The decline is the lever

Every dear read in §5.0 is a read the **named-projection device declined**.
The
decline listing (`HEATHER_GENDEF_DECLINES=1`, `probes/cb_decline.sh@ef3961a`) says
which decline it is per read, and that decides the owner. `project_field`'s rows for
the family's items (`probes/cb_decline.sh@ef3961a`, job 3; the count is reads, the
suffix on the reason is the field index):

```text
  12  close_body      Certified        instance-args-1      (+2 at -0, -2, -3 each)
   6  expr_body       Certified        instance-args-1      (+2 at -0, -3; +1 at -2)
   6  factor_body     Certified        instance-args-1      (+2 at -0, -3; +1 at -2)
   7  open_body       Certified        instance-args-1      (+1 at -0, -3)
   3  number_grammar  RecognizedHead   receiver-gate-0      (+1 at -1, -2)
   2  number_grammar  Exists           instance-args-1      (+1 at -0)
   1  number_grammar  And              receiver-gate-0      (+1 at -1)
   6  checked_expr    Pair             receiver-gate-1      (+4 at -0)
```

and over the whole file: `Parser` 100 and `And` 28 `receiver-gate`,
`Certified` **49** `instance-args`, `Grammar` 11 and `Exists` 7 the same,
`ErrorView` 2 `no-projection-def`.

The counts match the counter's route split read for read — `close_body`'s 18
`instance-args` declines are its 18 `walk` reads; `expr_body`'s and
`factor_body`'s 11 are their 11; `number_grammar`'s 5 `RecognizedHead` + 3
`Exists` + 2 `And` are its 10 — so the two instruments agree and the family
splits into **two declines with two different owners**:

- **`Certified` (and `Exists`, `Grammar`) decline at `instance_args`** — the
  hole matcher cannot recover the instantiation's arguments from the
  receiver's type. That is `docs/elaborator/telescoped-record-projections-design.md`
  §2.3's amendment, the "two spellings" boundary, which is already filed as
  the next slice and whose price this round measures: it is 78 % of
  `close_body`'s read nodes. The listing names the arms it dies on —
  `instance_match Certified identity-match-El/Nat` 33 times in `close_body`
  and 15 each in `expr_body`/`factor_body`, `hole-match-Sigma/El` 8 and 11,
  `instance_match Result hole-match-Sum/Sigma` 6 — so the slice has a
  reproducer for each before it starts.
- **`And` and `RecognizedHead` decline at the receiver gate** —
  `receiver_admits_reference` refusing a bare `Var`, the 2026-09-13 narrowing
  that `docs/elaborator/telescoped-record-projections-design.md` §4 deliberately kept for
  **non-dependent** telescoped records because the x86 certificates
  (`caller_native_memory_same_27/28`) cannot afford δ + β per read. So
  `number_grammar`'s share is not free the way the first is: it is the gate's
  bill, arriving on the parser side, and lifting it needs that trade
  re-measured on both workloads rather than a spelling change.

### 7.2 What no fix can be

- **Not a kernel rule, a memo or a conversion shortcut.** 22 misses and
  1 029 evaluator steps at 3.5 M queries (`t_cb1`); 0 and 0 at 1.56 M
  (`t_pcr3`'s `qchain3`). There is nothing to decide faster. The gate is
  0.47 queries per emitted node and that ratio is the whole item.
- **Not a library spelling, as far as this round can say.** The chain *is*
  the library's idiom — a cursor that moves is a new `Certified` at the old
  one's `.end` — and nothing shorter was found to write in the showcase. This
  one is an expectation and not a datum: no library variant was measured
  here, and the nearest measured negative (`t_qt4`, 0.13 %) is at the other
  round's site.
- **Not the tower design's readback, as designed.** §6 of
  `docs/elaborator/projected-tuple-tower-design.md` installs a sharing-preserving
  readback *from the value machine* at `build_ctor`'s whnf, for the
  components of a reduct. Here there is no reduct to read back: the walk does
  call `whnf` — once per spine entry, to expose the next `Σ` — but what it
  *writes* is not that reduct, it is the tail with the projection it just
  built substituted in, and `saturate` writes a telescope's domains with the
  arguments substituted in. Both are `LocalSubst`, not the value machine. A
  readback installed at `build_ctor` therefore reaches **none** of these four
  items — which is exactly what candidate D measured when it moved
  `complete_post` alone and left all four byte-identical.

  What *does* transfer is the readback's **other half**: the memo that mints
  a Ψ name for a sub-term it is asked to spell more than once
  (`docs/elaborator/projected-tuple-tower-design.md` §6's (b)). A chained receiver is
  precisely a sub-term spelled many times, so the same device at
  `project_field`'s two exits would collapse factor 1 — and the two slices in
  §7.3 are cheaper and should be measured first, because they may leave
  nothing worth minting.

### 7.3 What a fix is

Two, in the order their evidence supports.

1. **Make the matcher recover `Certified`'s arguments** — the
   `instance-args` decline of §7.1, i.e. the two-spellings boundary
   `docs/elaborator/telescoped-record-projections-design.md` §2.3's amendment already
   filed as the next slice, with `identity-match-El/Nat` and
   `hole-match-Sigma/El` as the arms to start from. What it reaches: 18 of
   `close_body`'s 29 `Certified` reads and 78 % of its read nodes, 11 of 29
   and 77 % in `expr_body`/`factor_body`, 22 of 22 in `t_cb1`. This is a
   continuation of a landed device, not a new mechanism, and it is the
   cheapest thing here. (`number_grammar`'s `receiver-gate` declines are
   **not** in it and must not be swept in: that gate is load-bearing for the
   x86 certificates, §7.1.)
2. **Name a declaration's function-typed value-parameter domain** — the
   follow-up `docs/elaborator/telescoped-record-projections-design.md` §5 filed on
   2026-09-15 and whose trigger has already fired. §5.2 prices it at **44×**
   on an identical three-receiver chain (`Certified` against `Success`), which
   is far above what the `Pi/Pi` row it was filed on suggested. Owner: the
   emission chokepoint plus a new `GenDef` kind for the domain.

Both are the same sentence as every round in this family — *write a name, not
the object* — and neither needs the kernel. What they do **not** remove is
factor 1's ×14 itself: a named domain shrinks the thing being copied, and a
fired device replaces a walk with a spine, but the chained receiver's argument
is still written into each annotation of each read. If the two together do not
flatten the `t_cb3`/`t_cb2`/`t_cb1` curve, the remaining device is the tower
design's **minting** half (a Ψ name per sub-term spelled more than once)
installed at `saturate` — same idea, different site, and it should be costed
only once the two cheap slices have been measured.

---

## 8. Verification items for the implementer's first hour

1. **Re-take §2's premise table** on the tree you start from. Item names are
   bare in column 3 of `--timings`; the family is `close_body`, `expr_body`,
   `factor_body`, `number_grammar`, `Grammar`, `Certified`.
2. **`probes/cb_count.sh@ef3961a`'s probe table before anything else**: `t_cb3`,
   `t_cb2`, `t_cb1` must reproduce 16 993 / 248 172 / 3 466 931 queries at 22
   misses. If the miss counts have moved, the tree is not this one and the
   whole attribution has to be re-run.
3. **The curve is the gate, not the seconds.** A slice that halves
   `close_body` and leaves `t_cb1`/`t_cb2` at ×14 has bought a constant on an
   exponential; say so in its own §.
4. **The route split is the cheap progress meter.** `HEATHER_CB=1` plus
   `probes/cb_agg.py@ef3961a`: `Certified walk` reads must fall to zero for slice 1,
   and the surviving `ref` reads' mean size is what slice 2 moves.
5. **The per-item join over all 959 rows**, as the tower round's §4.2 did:
   a spelling change at `project_field` is met by every reader that
   reconstitutes a former, and ten unrelated items regressed the last time one
   moved without the audit.
6. **`Grammar`/`Certified` should not move**, and watching them is how you
   find out that a slice did something other than what it said. Registration
   is unconditional — the Ψ bindings are minted at the declaration whether or
   not any use site takes them (`docs/elaborator/telescoped-record-projections-design.md`
   §4's own argument) — so a slice that only changes *which route a read
   takes* leaves these two rows where §2 has them. A slice that moves them has
   changed registration, which is a different change with a different issue
   (`issues/record-projection-defs-declaration-cost`).
7. **Do not read `checked_expr`'s row in §5.0 as a finding.** The counter
   keeps one `cb decl` line per declaration *name*, and an item that emits
   more than one pair — a `decreases` lowering mints helpers — keeps only the
   last. That is why its 8 533 nodes sit against 520 342 queries where every
   other row is near 0.47 per node. Either sum the lines per name or read
   that item elsewhere; nothing in this doc rests on it.

---

## 9. Status

**Design only.** No slice is implemented. The one source change is the node
counter of §1, reverted before this doc was offered; `probes/cb_count.patch@ef3961a`
is the patch and `probes/cb_base/@ef3961a` the pristine originals. `probes/cb_*.sh@ef3961a`,
`probes/t_cb*.hthr@ef3961a`, `probes/cb_agg.py@ef3961a` and the round section of
`probes/README.md@ef3961a` are what a reader re-runs. Nothing in `lib/`, the fixtures
or the rails was touched, and no commit was made.

What is now attributed, and what is not:

- **Attributed.** `close_body`, `expr_body`, `factor_body` (§6, one
  mechanism, two factors, two named declines), `number_grammar` (the same
  mechanism at the receiver gate, with the `build_ctor` minority unmeasured),
  `Grammar` and `Certified` (the device's registration, an existing issue's
  row). Between them that is the 6.5 M queries the brief named.
- **Not attributed, and newly visible.** `checked_expr` (§8 item 7), and the
  `respell_ty_at False no-closed-code` rows the decline listing puts inside
  this family's items — 420 in `number_grammar`, 244 in `close_body`, 150
  each in `expr_body`/`factor_body`. Neither is costed here.
- **Not attempted.** Any slice. §7.3's two are in the order their evidence
  supports, and the first of them is a continuation of a device that has
  already landed twice this month.

## Note, 2026-09-16: the showcase's type spelling changed under this table

`docs/showcase/calc_parser.hthr` now names the tier's reply type once
(`fn Checked(level, source, begin) -> Type`) instead of writing
`Result<Certified<…>,Failure<…>>` at each of twenty-five uses. The family's
per-item counts above were taken before that. Measured either side of the
change, `close_body` loses 1 816 conversion queries and `expr_body` and
`factor_body` about 6 400 each, while `number_grammar`'s counts are identical
— so the table's *ranking* and its argument are untouched, but a fresh
parent is needed before any new number is compared against these.
`docs/elaborator/complete-post-attribution-design.md` §10.7 has the measurement.
