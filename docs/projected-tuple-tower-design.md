# The projected tuple tower: what the exponent actually is — design

Design pass with a measured spike, on
`issues/elab-emits-normal-form-of-matched-type-argument`, the successor of
`docs/conversion-query-traversal-design.md` §10 (the round that stopped at the
site). The question it was given: the reduct `Elaborator::whnf` builds at
`build_ctor` is a projection chain applied to a literal tuple tower, un-fired,
because the rewriter fires redexes at the head only — so firing them deeply,
with no δ, should collapse the object. Verify that, then design.

**The reading is refuted, by its own instrument.** Firing every
`Fst`/`Snd`-of-`Pair`, every β of an applied `Lam` and every `case` of a
constructor in the reduct, to a fixed point, with no δ, removes **25–45 %** of
its nodes and leaves an object that still grows **×3.6 to ×3.9 per combinator
layer**. The un-fired redexes are a constant factor. The exponent is in the
βι-**normal form itself**: it is exponential as a *tree* and linear as a
*DAG*, and the term language the elaborator emits into has no way to write a
DAG. §3 is the re-derivation; §4 is the spike measured end to end anyway,
because it is a real constant and the numbers are the round's.

Everything below is hand-run in this pass on one furnace E5 box, release with
`--features value-metrics`, `--kernel-workers 1`, no `--cache`, one process
per file. `probes/tt_count.sh`, `probes/tt_slice.sh`, `probes/tt_D.patch`, and
`probes/README.md`'s round section say in what order.

---

## 1. The instrument

`probes/tt_D.patch` adds one elaborator-owned module, `crates/elab/src/ttsimp.rs`:
an exhaustive node counter over kernel `Term`/`Type`, and a **δ-free deep
simplifier** with exactly three rules — `fst (pair a b) ⇝ a`, `snd … ⇝ b`,
`app(λx. t; s) ⇝ t[s/x]`, `case(inl a; …) ⇝ c_l[a]` — applied bottom-up to a
fixed point. No δ, no `El` decode, no `Vec`/`Fin` unrolling, no recursor: the
three rules the reading named, and nothing that could change a spelling any
structural reader anchors on.

It is called at exactly one site, `Elaborator::build_ctor`'s reduct
(`crates/elab/src/inductive.rs:1966`, the call
`docs/conversion-query-traversal-design.md` §10.2 named), and `HEATHER_TT`
picks what it does there:

- **unset** — nothing is called; the binary is the parent's code path (the
  control run in §4 confirms this to the unit);
- **`count`** — the reduct is counted, simplified, counted again, and the
  *original* is kept. One line per reduct: pre and post node counts, the
  `Fst`/`Snd`-on-`Pair`, `App`-on-`Lam` and `case`-on-constructor counts on
  both sides, and the simplifier's own microseconds;
- **`fire`** — the simplified reduct is what `spine`, `respell_spine`,
  `inject` and `build_fields_skel` see. That is candidate D.

The counter is a tree count with no budget — unlike the bounded `Debug`
(`crates/kernel/src/fmt.rs`, which saturates at 512 nodes and was the previous
round's only size proxy), and unlike the clocks, which are proxies for size
rather than size.

---

## 2. The counts

`probes/tt_count.sh` (four files) and `probes/tt_slice.sh`'s fifth point,
`HEATHER_TT=count`, the item's **own** `build_ctor` reduct — the largest
record of the run that is not the library's:

| probe | item | nodes, pre | nodes, post | post/pre | proj | β | case | simp |
|---|---|---|---|---|---|---|---|---|
| `t_qt2` | `qt_floor` | < 2 814 | — | — | — | — | — | — |
| `t_qt1` | `qt_pure` | 390 717 | 294 309 | 0.753 | 20 | 0 | 0 | 42 ms |
| `t_cp9` | `cp_andt` | 1 756 377 | 1 057 635 | 0.602 | 92 | 18 | 0 | 265 ms |
| `t_qt3` | `qt_deep` | 7 219 017 | 4 012 407 | 0.556 | 380 | 90 | 0 | 1 632 ms |
| `t_qt5` | `qt_deeper` | 29 069 577 | 15 831 495 | 0.545 | 1 532 | 378 | 0 | 8 665 ms |

The library's `complete_post`, re-elaborated as the control in every one of
these runs, reads **2 634 824 → 1 586 711** nodes (0.602), 138 projections and
27 βs, in every run, to the unit.

Three readings of that table, and they are the round:

- **The node count *is* the query count.** `qt_pure` is 390 717 nodes against
  390 503 conversion queries; `qt_deep` 7 219 017 against 7 928 179;
  `qt_deeper` 29 069 577 against 29 447 197 — one reduct, one item's whole
  gate, within 10 %. `docs/conversion-query-traversal-design.md` §3.2 inferred
  a flat cost per node from a clock; this counts the nodes.
- **The pre-firing curve is the exponent**, ×4.50, ×4.11 and ×4.03 per
  combinator layer — the same curve as queries, emission, whnf clock and RSS.
- **So is the post-firing curve**: ×3.59, ×3.79, ×3.94. Firing every redex of
  the three named kinds removes a quarter to a half of the object and **none
  of its growth rate**. There are 92 projections in a 1.76-million-node
  reduct; they carry 700 000 nodes between them, and what is left is still
  3.8× per layer.

**The coordinator's reading is therefore refused.** "Fire the projections and
each layer's tuple mentions the layer below's fields, not the layer below" is
true node for node and does not help: the tuple has three fields, each
mentioned once, and each of them is an expression over the layer below's
three fields. Three references per layer to the layer below is 3ⁿ whether the
references are spelled `Fst(Pair(…))` or spelled out.

---

## 3. The re-derivation: exponential as a tree, linear as a DAG

What the rewriter builds, one combinator layer at a time
(`lib/std/parser/parser_combinators.hthr:25,:43,:48`): the `Ok` branch of each
layer rebuilds `Success(f(s.value), s.end, s.forward)`, so firing that layer's
`case` substitutes the layer below's record into a body that mentions it three
times. Substitution **copies**. After one layer there are three copies of the
layer below; after two, nine; the measured base is ≈3.5–4 because the
annotations (`App.dom`/`App.cod`, `Pair.fst_ty`/`snd_ty`, `Fst.snd_ty`) are
themselves types over the same fields and multiply with them.

Write the same object as a graph and it is small: **three distinct components
per layer**, each referring to the three below it — `3n` nodes plus the
constants, linear in the nesting. The exponential is entirely the cost of
writing that graph as a tree.

That is the mechanism, and it decides the design, because it says what a fix
must do and what no fix can do:

- **No post-pass can fix it.** Any rewrite that is handed the reduct has
  already paid for it — in the rewriter's own allocation (`elab_whnf_ns`,
  2.5 s at `t_qt3`), in the peak memory it took to hold it, and in the walk.
  D is the best such post-pass there is (it fires every redex there is) and it
  is a constant.
- **No sharing *representation* can fix it either, on its own.** The
  `Rc`-sharing the emitted term already has (§2.4 of the traversal doc: 4 382
  distinct type objects over 28 759 samples) does not survive de Bruijn
  shifting under binders, which is why resident memory tracks the tree count
  and why `docs/conversion-query-traversal-design.md` §6 rejected hash-consing
  **on the memory column**. That rejection stands and this round sharpens it:
  hash-consing an object that was built as a tree is the wrong end; the graph
  has to be what is *built*.
- **What can fix it is a spelling with names in it.** `Term` has no `let` and
  no explicit substitution (`grep Let crates/kernel/src/term.rs` finds only
  the modal `LetBoxTy`/`LetBoxTm`),
  but it has something with the same effect and no metatheory bill: a **Ψ
  definition**, `GlobalTm { var, subst }` / `GlobalTy`, whose δ the kernel
  unfolds lazily and glues (`crates/kernel/src/value.rs:1103`,
  `issues/kernel-lazy-delta-and-run-arithmetic`). A generated declaration per
  distinct component — the device that already spells
  `D#payloadₖ`/`D#suffixₖ` and the per-instantiation type codes — writes the
  DAG. Three declarations per combinator layer, each mentioning the three
  below by name, is the linear spelling this obligation has and the
  elaborator currently cannot say.

---

## 4. The spike: candidate D measured end to end

`probes/tt_slice.sh`. One binary, two behaviours (`HEATHER_TT` unset = the
parent's path, `fire` = D). Two controls say the unset path really is the
parent's: `target/heather_parent` (HEAD, parked before the edit synced) on
`t_cp9` reads 8 860 misses / 2 395 753 queries / 162 499 steps, the unset run
reads the same three to the unit, and the unset showcase reads
212 318 / 16 762 944 / 4 697 239 — `docs/complete-post-attribution-design.md`
§10.2's numbers exactly.

### 4.1 The curve, `off` → `fire`

| probe | item | queries | misses | steps | total ms | gate ms | `elab_whnf` ms | `decl_emit` ms | maxrss |
|---|---|---|---|---|---|---|---|---|---|
| `t_qt2` | `qt_floor` | 6 495 → 6 495 | 21 → 21 | 738 → 738 | 27.2 → 27.5 | 12.0 → 12.3 | 6.5 → 6.3 | 1.0 → 0.9 | 1.41 → 1.03 GB |
| `t_qt1` | `qt_pure` | 390 503 → 295 983 | 1 469 → 853 | 27 174 → 19 550 | 1 339 → 1 117 | 681 → 474 | 263 → 268 | 64 → 55 | 1.41 → 1.04 GB |
| `t_cp9` | `cp_andt` | 2 395 753 → 1 712 165 | 8 860 → 5 717 | 162 499 → 112 270 | 6 888 → 5 504 | 4 306 → 3 096 | 637 → 635 | 448 → 319 | 1.41 → 1.03 GB |
| `t_qt3` | `qt_deep` | 7 928 179 → 4 792 739 | 33 780 → 15 111 | 525 244 → 299 245 | 25 797 → 18 683 | 15 330 → 9 893 | 2 568 → 2 659 | 1 625 → 918 | 2.78 → 1.79 GB |
| `t_qt5` | `qt_deeper` | 29 447 197 → 16 504 349 | 128 043 → 49 782 | 1 917 588 → 991 145 | 100 054 → 83 079 | 62 261 → 42 487 | 10 897 → 11 114 | 5 776 → 4 259 | 9.54 → 5.54 GB |
| `t_qt4` | `qt_named` | 7 917 550 → 4 782 110 | 33 771 → 15 102 | 525 260 → 299 261 | 25 312 → 20 903 | 15 212 → 10 855 | 2 573 → 2 765 | 1 617 → 1 130 | 2.78 → 1.80 GB |
| `t_cp1` | `cp_full` | 3 681 039 → 2 484 760 | 14 210 → 7 908 | 246 498 → 157 815 | 11 008 → 8 091 | 7 271 → 4 759 | 902 → 905 | 688 → 467 | 1.46 → 1.09 GB |
| `t_cp18` | `cp_twice` | 4 965 897 → 3 256 927 | 21 347 → 10 098 | 331 907 → 202 982 | 14 915 → 10 355 | 10 119 → 6 416 | 945 → 933 | 1 008 → 606 | 1.86 → 1.32 GB |

Read it by the ratios:

- **Queries fall 24–44 %** (0.76, 0.71, 0.60, 0.56 down the curve), and
  `t_qt4` stays within a tenth of a percent of `t_qt3` on both sides — the
  §8-item-6 negative of the previous round still holds, so D is not secretly
  doing what naming the reply would.
- **The exponent stays.** `cp_andt` → `qt_deep` → `qt_deeper` is ×3.31 and
  ×3.71 on the parent path and ×2.80 and ×3.44 on D's: the base moved from
  ≈3.5 to ≈3.1, and one more identity `map_at` still costs three times the
  whole item. That is §2's post-firing curve seen through the gate.
- **Resident memory does move** — 9.54 GB to 5.54 GB at `t_qt5` — which the
  brief predicted it could not. The reduct is what is held, and the fired one
  is smaller.
- `elab_whnf_ns` is **flat** (the rewriter still builds the same object; the
  simplifier's own time is charged outside that bracket, and §2's `simp`
  column is what it costs: 8.7 s at `t_qt5`), and `decl_emit_ns` **falls**
  30–45 %, because the chokepoint then walks the smaller object.

### 4.2 The showcase

Serial (`--kernel-workers 1`), and at the default gate width:

| | off | fire |
|---|---|---|
| serial, item totals / kernel gate | 64.29 s / 49.57 s | **62.35 s / 47.74 s** |
| serial, wall / maxrss | 65.50 s / 2.39 GB | 63.51 s / 2.38 GB |
| default width, item totals / gate | 73.35 s / 55.40 s | 71.78 s / 54.19 s |
| default width, wall / maxrss | 32.71 s / 7.06 GB | 30.47 s / 7.07 GB |
| misses / queries / steps | 212 318 / 16 762 944 / 4 697 239 | 205 617 / 15 534 538 / 4 598 150 |

and the named items, serial, `total ms / misses / queries`:

| item | off | fire |
|---|---|---|
| `complete_post` | 11 160 / 14 210 / 3 681 039 | **8 762 / 7 908 / 2 484 760** |
| `close_body` | 6 765 / 7 318 / 2 585 801 | 6 888 / 7 318 / 2 585 801 |
| `expr_body` | 2 705 / 420 / 1 024 751 | 2 742 / 420 / 1 024 751 |
| `factor_body` | 2 780 / 436 / 1 024 783 | 2 867 / 436 / 1 024 783 |
| `number_grammar` | 2 552 / 14 289 / 1 100 958 | 2 554 / 14 289 / 1 100 958 |
| `checked_expr` | 1 574 / 17 995 / 520 342 | 1 562 / 17 995 / 520 342 |
| `Grammar` | 1 149 / 36 / 457 050 | 1 218 / 36 / 457 050 |
| `Certified` | 809 / 36 / 357 891 | 799 / 36 / 357 891 |

**D moves one item of the showcase and no other.** Every other named row is
byte-identical in misses, queries and steps; `close_body`, `expr_body` and
`factor_body` — the three the quote slice could not reach either — do not
move at all, because their obligations do not go through a `build_ctor`
reduct. The whole-run 7.3 % of queries is `complete_post`'s 32.5 %.

**And ten items regress.** The 944-row join: misses rise on ten
(`list::mem_map` 250 → 266, `list::mem_append_l` 241 → 258,
`parser_primitives::selected_head` 181 → 207, seven more of the same family),
conversion queries rise on one (`list::append_nil_elim` 1 845 → 1 906), and
evaluator steps rise on ten. These are the reducts whose redexes are
`case`-of-constructor rather than projections (§2's `case` column: 18 per
`list::mem_*` reduct) — firing them writes a *different* spelling into the
constructor value, and the kernel then misses where it used to hit. The
summed head-pair table moves 212 157 → 205 456 misses over the same 52 rows,
with six pairs rising (`El(?)/Wf`, `Fin/Sum`, `Pi/Pi`, `Vec/Sigma`,
`Vec/Unit`, `Vec/Vec`).

So D is a real 25–44 % on the exponential family, a 7 % on the showcase, and
it **fails the standing per-item gate** as written. §5 is where that verdict
goes.

---

## 5. The candidates

### D — the δ-free deep simplifier at the emitter

Measured above: 24–44 % of the queries and up to 42 % of the resident memory
on the exponential family, 7.3 % of the showcase's queries, 1 429 lines of
exhaustive walk in the elaborator, and one spelling change whose consequences
are the ten regressed items of §4.2.

**Not chosen, and not proposed as the first slice.** Four reasons, in order of
weight:

1. It banks a constant against the evidence for the exponent, which is the
   refusal `docs/conversion-query-traversal-design.md` §5 and
   `docs/complete-post-attribution-design.md` §6 both made for the typed-`App`
   rule and the reflexivity fast path, on larger shares than this. The
   showcase's `complete_post` is 11.2 s and would be 8.8 s; it is still the
   largest item, still exponential, and the next combinator layer costs ×3.4
   on D's own curve.
2. **It regresses ten items**, so it does not pass the gate the last two
   rounds were held to (`probes/cp_gate.sh`'s reading: no item's misses,
   queries or steps may rise). The mechanism is understood — firing
   `case`-of-constructor in a `list::mem_*` reduct writes a different
   spelling, and the kernel misses where it hit — and it is fixable by firing
   projections only, at the cost of some of the gain. It is not a defect to
   be patched inside this round: it is the sign that the pass is a *spelling*
   change made for a size reason, which is the shape
   `issues/emission-site-respell-audit` exists to catch.
3. Its cost lands where this family can least afford it. The simplifier walks
   and rebuilds the whole exponential object at every constructor value —
   8.7 s of it at `t_qt5`, 0.4 s at every elaboration of `complete_post` — and
   that is a *third* full traversal, after the rewriter's construction and the
   chokepoint's walk (`issues/emit-ty-rewalks-normalized-type`). It pays for
   itself today only because the kernel's per-node cost downstream is larger.
4. Everything it removes is inside the object the real fix does not build. It
   is dead the day §6 lands, and a 1 400-line exhaustive walk over both kernel
   sorts is a maintenance surface that every new kernel variant must answer
   to.

It stays as `probes/tt_D.patch` with this table, and the coordinator may file
it as a triggered accumulator issue (`perf-work-as-accumulator-issues`): if a
customer needs `complete_post`'s 2.4 s before §6 lands, this is the lever, it
is measured, and its first task would be the ten items.

### E — spell the reduct from the value machine

`oracle.rs` already asks `eval::whnf_value_ty` first and re-runs the rewriter
only to *spell* the answer, precisely because the value machine is not
pathological where the rewriter is. The proposal is to drop the second half:
read the whnf value's components back into syntax in the elaborator.

**A naive readback is not a fix, and this round can say so with numbers.**
Readback produces a normal form; §2 measured the normal form; it is
exponential. A readback that expands `TmClo`s as it meets them writes the same
tree the rewriter writes, one traversal later.

**A readback that preserves sharing is the fix**, and it is the only candidate
that can produce §3's linear spelling, because the linear object exists only
as a graph and **the value domain is where that graph is**: `TmClo` nodes are
shared by pointer (`crates/kernel/src/value.rs`'s `Env`/`TmClo`/`ElimSpine`),
the arena already memoizes on `*const TmClo` (`ValueArena::term_cache`), and a
glued neutral carries its folded global beside its unfolding
(`VNeutral::unfold`). A readback memoized on closure identity, which mints a
**generated Ψ definition** for every sub-value it is asked for more than once
and prefers a glued global's folded name to its unfolding, reads the graph as
a graph: three declarations per combinator layer, each naming the three below.

Against `docs/nbe-conversion-design.md` §7, explicitly, because the brief asks
and because the answer is not "it does not apply":

- §7's decision is that **the kernel** gains no readback, and its invariant is
  "no `eval ∘ readback` round-trip **in the kernel**". An elaborator-owned
  readback produces elaborator syntax, which the kernel then evaluates exactly
  as it evaluates every other thing the elaborator writes. The invariant is
  untouched, literally and in spirit: the grep-checkable absence of a
  `readback` symbol in `crates/kernel` survives, and no value produced inside a
  conversion is turned into syntax that that conversion then evaluates.
- §7's *reasons*, however, transfer as warnings rather than as refusals. The
  one that bites is the one §7 does not state because the kernel never had it:
  a readback's output is a normal form, and normal forms are where the
  exponent lives. That is why the sharing memo is not an optimization of this
  candidate but its whole content, and why an implementation that forgets it
  will measure no change at all (which is a cheap first-hour check, §9 item 2).
- §7 already lists the oracle as a customer and already admits one
  value→syntax step: a former with **no** sub-structure (`Nat`, `Ty l`,
  `Unit`, …) is read straight off the value. This is that door opened wider,
  with the naming as what keeps the exponent out of it.

What the crate boundary needs: `Val`, `VTy`, `VNeutral`/`Head`/`ElimSpine`,
`TmClo`, `Env` and `Eval::force`/`force_ty` are already `pub`; what is new is
that the elaborator would read *structure* where today `oracle.rs` reads only
*shapes*, and would have to hold the arena's lifetime across the readback
(today each probe builds a fresh `ValueArena` and drops it). The risk is the
one `Elaborator::whnf`'s own comment names: the structural readers and the
guards that hand out references anchor on registered lowerings' **inline
identity** (`unspell_here`, `unspell_sum_components`, `tag_of`), so the
readback must land on the spellings they recognize — which is the same
obligation `emit_ty` already discharges, and the same audit
`issues/emission-site-respell-audit` records.

### F — the kernel-side alternatives

- **A constructor value annotated with the whole expected type** (a checked
  form the kernel whnfs itself) would move the problem rather than remove it:
  the kernel would then build the same reduct in *its* rewriter, per
  constructor value, and the elaborator's exponent would become the kernel's.
  It also breaks the annotation discipline ch. 04 keeps and `DESIGN.md`
  restates — every form is fully annotated so that everything but `box`
  infers, and the sub-structures are recursor-reachable; an annotation that
  must be reduced before it can be read is not recursor-reachable syntax.
  Rejected.
- **A `let`/explicit-substitution node in `Term`** is the honest name for what
  §3 says is missing, and it is still rejected: it is a DeLaM syntax extension
  with a metatheory bill in ch. 05's syntactic operations, ch. 06's reduction
  and ch. 07's logical relations, all of which Heather owes for every
  extension it has already taken (`issues/kernel-v1-extensions`), and
  `docs/nbe-conversion-design.md` §14 has already refused it once —
  "comparable metatheory bill, worse novelty". The point of §3's Ψ-definition
  reading is that **the sharing node already exists** at the global level,
  with its metatheory paid: a defined global under a local substitution is
  ch. 04 syntax, its δ is ch. 06 reduction, and the kernel's laziness and
  gluing are already built for it. A `let` would be a second, redundant way to
  say the same thing.

### G — smart constructors inside the rewriter or substitution

`crates/kernel/src/reduce.rs` is the **specification**: ch. 06 verbatim, and
the differential oracle the value machine is measured against
(`docs/nbe-conversion-design.md` §2, §11.2, and the `subst_laws` property
tests). A `Fst`-smart-constructor in `subst.rs` or a fire-on-rebuild rule in
`reduce.rs` would make the rewriter no longer the book's reduction, which
costs the kernel its only differential gate to save an elaborator-side
spelling. Rejected on that ground, as the brief expected. The narrower version
— "the elaborator wants a *different* reduction from ch. 06's" — is exactly
why D lives in `crates/elab` and why E's readback would too.

---

## 6. The chosen mechanism, and its owner

**The elaborator, at the same boundary §5 of the traversal doc named, with the
readback of candidate E as the device and a name as the unit of sharing.**
When a `→ Type` body's `match` forces the elaborator to drive a term to a
constructor, the components it then emits must be read back from the **value**
the machine already produced, through a readback memoized on closure identity
that (a) prefers a glued global's folded name over its unfolding, and (b)
mints a generated Ψ declaration — the existing `D#…` device, under the
constructor telescope's local substitution — for every sub-value it is asked
to spell more than once, so that what is written down is the graph and not its
expansion. The kernel needs nothing new: a defined global under a local
substitution is ch. 04 syntax whose δ it already unfolds lazily and glues, and
`docs/nbe-conversion-design.md` §7's invariant is about the kernel's own
internals and stays true. The measured bar is not seconds but the **shape**:
`t_cp9`, `t_qt3` and `t_qt5`'s node counts, queries, emission clock and
resident memory must stop multiplying by 3.5 per identity `map_at` — and the
first hour's check is that the emitted obligation's node count for `qt_deep`
is a small multiple of `qt_pure`'s and not 18× it.

How the other whnf sites fare under it: `matching::expose`'s whnf, which the
previous round measured at 113.7 → 140.9 ms across a layer that multiplies
everything else by 3.5, is **not** on this path and does not change — the
motive is not the carrier (§10.2 there). This round's instrument does not
speak to that site — it is installed at `build_ctor` and nowhere else — so
that clock is still the evidence, and a readback installed more widely would
have to re-measure it. The checking sites in `crates/elab/src/lib.rs` (the `Var`
arm's erased-universe check, the expected-type harvest,
`anonymous_ctor_expected`, `ctor_here_expected`) read a *shape* and throw the
spelling away; they keep the rewriter and the stuck-spelling budget the
2026-09-05 round gave them. Only the emission path changes.

What meets the changed spelling — the 2026-09-10 lesson, that a spelling
change regresses every reader that reconstitutes a former against it: the
`tag_of`/`spine`/`decoded` triple in `inductive.rs`; `unspell_here` and
`unspell_sum_components` in `Elaborator::whnf`; `emit_ty` and
`respell_ty_deep_in`'s component walk, which must see *through* a minted name
as it sees through `D#payloadₖ`; `emission_walk`'s slot list; the image codec
and `ModuleDelta`'s dependency identity, because a generated declaration is a
new Ψ binding that has to be in the image and in the dependency test; and the
`WALK_RESIDUE` list in `crates/elab/tests/ir_v1.rs`, which may only shrink.

§4.2's ten regressed items are what that list looks like when it is not
discharged: D changed one spelling at one site and ten unrelated items lost
conversion hits. A readback changes the spelling of *every* component it
names, so the audit is not optional and its cheapest form is the per-item
join, run early and often.

---

## 7. Rejected shapes, with reasons

- **Firing the redexes deeply (D).** §4, §5: measured — one showcase item,
  ten small regressions, and a constant against ×3.4 per layer on its own
  curve. Kept as a patch, not proposed.
- **A naive readback from the value domain.** §5 E: it writes the normal form,
  and §2 measured the normal form. This is the most valuable negative of the
  round, because "read it back from the values" is the obvious proposal and it
  is wrong without the memo.
- **Hash-consing the emitted term.** `docs/conversion-query-traversal-design.md`
  §6 rejected it on the memory column; §3 here says why more precisely — the
  graph must be *built*, and an object built as a tree has already cost its
  size before any consing sees it.
- **Naming the reply in the library** (`t_qt4`, 0.13 %), **naming the
  component again**, **a kernel memo or conversion rule**, **a
  pointer-identity fast path**, **flattening the library's combinator
  chains**: all measured or argued in the two previous rounds, none revisited
  here, all still refused for the reasons recorded there.
- **A `let` node, a whole-type constructor annotation, a smart constructor in
  `reduce.rs`/`subst.rs`**: §5 F and G.

---

## 8. Cost, and the boundaries not moved

**This pass.** One module (`crates/elab/src/ttsimp.rs`) and two call lines
(`mod ttsimp;`, and the call in `build_ctor`), all of it inert with
`HEATHER_TT` unset — the §4 control run is the check that "inert" is literal.
The tree offered for review has it **reverted**; the patch is
`probes/tt_D.patch` and the pristine originals are `probes/tt_base/`. Nothing
in `lib/`, the fixtures, the `WALK_RESIDUE` list or the x86 rails was touched,
and no commit was made.

For the record, since a declined patch may be picked up later:
`scripts/test --fast -p heather-elab` **on the spike** is
`== suite: 1961 passed, 0 failed, 5 ignored ==` (`probes/tt_fast.sh`). That is
the fast lane, which replays module images an earlier build wrote, so it says
the change breaks no elaborator test — not that it is landable. What would
have to be run before it lands is the full `scripts/test`, and §4.2's ten
regressed items would have to be answered first anyway.

**The proposed change** (§6) moves what the frontend emits, so it is the shape
that needs the full `scripts/test` and not `--fast`, the x86 certificate gates
at two sizes per item, `WALK_RESIDUE` shrinking only, and `scripts/bench
--check` through the `--save`/apply/`--check` dance. It also adds Ψ bindings,
which puts it in front of the image codec, the dependency identity and
`psi().bindings.len()`'s fixtures — none of which the last three rounds had to
move, and all of which this one probably does.

**Not proposed to change:** `reduce.rs` (G), `Term` (F), the conversion
algorithm, the receiver gate, the three projection devices, the quote layer,
and `docs/nbe-conversion-design.md` §7's decision, whose invariant §5 argues is
untouched rather than amended.

---

## 9. Verification items for the implementer's first hour

Stop and report if any of these fires.

1. **Re-confirm the counts before touching anything.** `probes/tt_count.sh`
   and `probes/tt_slice.sh`'s fifth point, with `HEATHER_TT=count`: `qt_pure`
   390 717, `cp_andt` 1 756 377, `qt_deep` 7 219 017, `qt_deeper` 29 069 577
   nodes pre-firing, and the post-firing column within a point or two of
   0.75 / 0.60 / 0.56 / 0.55. The bar's bar is the **curve**: pre
   ×4.50 / ×4.11 / ×4.03, post ×3.59 / ×3.79 / ×3.94. A single pair is a
   slope, not an exponent (`rail-pass-is-a-floor`).
2. **The readback without the memo, measured first.** Before building the
   naming device, read one reduct back naively and count it. It must come out
   at §2's pre-firing count, within the constant the rewriter's annotations
   add. If it comes out *smaller*, the value domain is doing something this
   design did not account for and the rest of §6 has to be re-argued.
3. **The minted names must be what the structural readers see.** `tag_of` on a
   named component, `unspell_here` on a reference to one, `emit_ty`'s
   idempotence over one: a component the readback names and a component it
   does not must elaborate to the same accepted term, or the round is writing
   two spellings for one thing (the boundary the 2026-09-16 instance-matcher
   round spent itself on).
4. **The counts, not the seconds**, and the shape, not the count: `qt_deep`'s
   emitted node count must be a small multiple of `qt_pure`'s. `t_cp1`'s
   3 681 039 queries and `close_body`'s 2 585 801 are the absolute sub-bars;
   the showcase is 16 762 944.
5. **No item may regress** across the 944 joined showcase rows — misses,
   queries, steps (`probes/tt_slice.sh`'s join is the shape).
6. **`t_qt4` must stay within a percent of `t_qt3`.** If naming the reply in
   the library suddenly matters, the change is doing something other than §6.
7. **The x86 rails at two sizes per item**, `WALK_RESIDUE` shrinking only, the
   full `scripts/test`, and the bench dance. A new Ψ binding per component is
   exactly the shape `issues/per-instantiation-projection-boundaries` boundary
   2 refused twice: cheap to compare, dear to compute through.
8. **The four axes** (`docs/testing-generated-terms.md`) on the new pin: a
   literal and a **neutral** scrutinee, an **open** element type with its
   closed control, a **checking** position, and a negative control. The pin is
   `t_qt2`-against-`t_qt3` in shape — one identity `map_at` between them, and
   the emitted obligation's node count does not multiply. A unit-sized version
   pins nothing (the 2026-09-16 round dropped one for that reason); the probes
   are the cost gate and this doc is where they live.

---

## 10. Status

Design, with one measured spike that is **not** proposed to land. §11 is the
implementation pass that followed it (2026-09-16): the verification items are
confirmed, the unit of sharing is measured, and the readback's first stage is
built, flagged and measured end to end. The reading
the brief handed this pass is refuted by its own instrument (§2), the exponent
is re-derived (§3), candidate D is measured end to end and declined with its
table (§4, §5), and the chosen mechanism is the sharing-preserving readback of
§6, whose first obligation is to fail fast: a readback without the memo will
measure nothing, and item 9.2 is how the implementer learns that in an hour
instead of a round.

What this hands on:

- `issues/elab-emits-normal-form-of-matched-type-argument` keeps its charter
  and gains its mechanism: the emitted normal form is exponential **as a
  tree** and linear as a graph, so the fix is a spelling with names in it, not
  a rewrite of the tree. Its 2026-09-16 log entry's "reduction provenance in
  `crates/kernel`" reading is narrowed: the provenance that is needed is the
  value machine's closure identity, which the elaborator can read without the
  kernel gaining anything.
- `issues/emit-ty-rewalks-normalized-type` gains a second customer and a
  sharper statement: the chokepoint's walk is one of *three* full traversals
  of the same exponential object (rewriter, chokepoint, kernel), and D would
  have made it four.
- The memory rule "computed-hypothesis shortcuts pay twice" gains its limit
  case: when the elaborator normalizes and writes the result down, every phase
  pays per node of a tree that has a linear graph inside it.

---

## 11. Implementation (2026-09-16): the spike, and stage one of the readback

The implementation pass of §6. It ran §9's items 1–3 first, which **confirm**
the design, and then built the readback itself in two stages: the value→syntax
spelling (landed here, behind a flag, measured end to end) and the naming
(designed here with its Ψ-entry mechanism and its measured target, **not**
built). Everything below is measured on the same furnace E5 box as §4 unless
a table says "local", release with `--features value-metrics`,
`--kernel-workers 1`, no `--cache`, one process per file;
`probes/rb_slice.sh` and `probes/README.md`'s round section say in what order.
The tree offered for review carries both instruments and is **inert** with
`HEATHER_RB` unset; `probes/rb_base/` holds the pristine copies.

### 11.1 The spike: the naive count, the graph count, the curve (§9 items 1–3)

`crates/elab/src/rbcount.rs` (`HEATHER_RB=count`) — which carries §1's
exhaustive syntax counter, redex columns dropped, for its `reduct` column —
walks the whnf **value** at
`build_ctor` the way a readback would — forcing a 0-binder sub-structure,
applying a `k`-binder one to `k` fresh neutrals, with
`crates/kernel/src/conv/dom/values.rs`'s binder arities, and reading a glued
neutral at its **folded** head. Both columns come from one walk: memoizing
`count = 1 + Σ count(children)` on closure identity computes the size of the
*tree* a naive readback writes, in the *graph*'s time, and the memo's
population is the graph.

| probe | item | reduct (§2, pre-firing) | naive readback | graph | shared nodes |
|---|---|---|---|---|---|
| `t_qt1` | `qt_pure` | 390 717 | 332 848 | 26 043 | 546 |
| `t_cp9` | `cp_andt` | 1 756 377 | 1 304 352 | 61 181 | 1 103 |
| `t_qt3` | `qt_deep` | 7 219 017 | 4 967 022 | 80 519 | 1 430 |
| `t_qt5` | `qt_deeper` | 29 069 577 | 19 617 702 | 99 857 | 1 757 |
| library | `complete_post` | 2 634 824 | 1 957 109 | 62 058 | 1 132 |

1. **§2's counts re-confirm to the unit** on this tree — every `reduct` column
   above is §2's number exactly, and the curve is ×4.50 / ×4.11 / ×4.03.
2. **The naive readback is the normal form**, as §5 E said: 0.85 / 0.74 / 0.69
   / 0.67 of the rewriter's own reduct — the annotation constant, *below* it
   rather than above because the readback fires the redexes §4 measured at
   25–45 % — and on the same curve, ×3.92 / ×3.81 / ×3.95 per layer. Not
   smaller in kind; the STOP of item 2 does not fire.
3. **The graph is linear**: 26 043 → 61 181 → 80 519 → 99 857, i.e. ×2.35,
   ×1.31, ×1.24 and about +19 000 nodes per combinator layer at the tail
   against ×4 in the tree. At `qt_deeper` the tree is **196×** its own graph.
   §3's re-derivation stands and §6 has its basis.

### 11.2 What the unit of sharing has to be — two measurements §6 did not have

The same walk prices §6's open choice ("a sub-value visited twice; or every
closure of a layer") directly: for a threshold `T`, name every shared node
whose naming saves at least `T` nodes, bottom-up, and count what is emitted —
the root's term plus every minted body, a reference costing 3 nodes.

| item | T=0 (every shared node) | T=64 | T=1 024 |
|---|---|---|---|
| `qt_pure` | 546 names / 37 630 nodes | **40 / 34 681** | 20 / 41 267 |
| `cp_andt` | 1 103 / 84 916 | **30 / 79 298** | 14 / 84 622 |
| `qt_deep` | 1 430 / 111 614 | **36 / 104 309** | 18 / 109 915 |
| `qt_deeper` | 1 757 / 138 312 | **42 / 129 320** | 22 / 135 208 |
| `complete_post` | 1 132 / 86 191 | **31 / 80 477** | 14 / 86 207 |

- **The unit is "shared *and* worth at least ~64 nodes", not "shared".**
  Naming every twice-spelled sub-value is both 30× more declarations *and*
  slightly worse in nodes than naming the few dozen that pay: a name costs its
  body plus a reference per use, and most shared nodes are small.
- **Thirty to forty declarations per reduct** collapse 1.96 M emitted nodes to
  80 477 — and the emitted curve is the graph's, ×2.29 / ×1.32 / ×1.24. §6's
  first-hour check, "`qt_deep`'s emitted node count is a small multiple of
  `qt_pure`'s and not 18× it", comes out at **×3.0** against ×18.5 in the
  rewriter's reduct.
- **Ψ growth, per declaration**: over the whole showcase (8 092 `build_ctor`
  reducts) the T=64 rule names **152** sub-values in total — 31 in
  `complete_post`, 12 each in `product_grammar` and `sum_grammar` (over 14
  reducts apiece), 3 in `paren_grammar`, **zero** in the 900-odd other items,
  including every `omega::cutsat_*` (1 087 reducts, not one shared node worth
  naming). That is the number
  `issues/record-projection-defs-declaration-cost` has to cover, and it is two
  orders below that issue's own customers — but its cost is per *binding
  gated*, so it is the next round's measurement, not this one's claim.
- **A naming device restricted to codes does not work.** The obvious
  conservative rule — mint only what is already a type or a type *encoding*,
  whose statement is `Ty l` and needs no inference — was measured on the same
  walk: `complete_post` goes to 14 names / **1 442 433** nodes,
  `qt_deep` to 15 / 3 571 257. The heavy shared nodes are *terms* that are not
  encodings. So §6's device must be able to name a **term at an arbitrary
  type**, and the type must come from the **position** — kernel syntax is
  fully annotated (ch. 04), so every sub-structure's type is in the former
  above it — rather than from the value, which does not carry one.

### 11.3 Stage one: the readback, spelled but not named

`crates/elab/src/rbemit.rs` (`HEATHER_RB=fire`) is §5 E's readback with the
sharing memo on the *elaborator's* copy (one `Rc` per distinct sub-value) and
**no minting**. It is installed at `build_ctor` only. Two rules, both
discovered by the library failing to elaborate without them, and both §6's own
doctrine read at a new place:

- **An `El` at a glued encoding is kept folded.** Forcing it decodes the
  definition the encoding names, and the registry's whole reason for naming a
  lowering is that `El (D#tycode^δ)` is the spelling every structural reader
  anchors on. This is §6's preference (a) at the type level.
- **`Elaborator::whnf`'s two rules apply to the readback's answer too**: a
  reference to a registered lowering is the registry's copy and is not read
  back at all, and a sum of the whole-type code's components is respelled
  inline (`unspell_sum_components`). Without the second, `tag_of` fails on
  `Bool`: the value machine leaves `El (D#payload₀^δ) + El (D#suffix₀^δ)`
  folded where the rewriter had decoded it, and no structural reader sees a
  tag through that.
- A **stuck** head is declined outright, which is `oracle.rs`'s own rule, and
  so is any value with no bounded syntax (a compressed `Nat` run past 4 096
  over a neutral tail, a bit run, a code recursor's elimination). A decline
  keeps the rewriter's reduct. Over every probe and the showcase: **zero**
  declines at `build_ctor`.

`off` is the parent's path to the unit (`t_cp9` off reads 8 860 / 2 395 753 /
162 499 against the parked HEAD binary's, and §4.1's `off` column).

| probe | item | total ms | gate ms | `elab_whnf` | `decl_emit` | misses | queries | steps | maxrss |
|---|---|---|---|---|---|---|---|---|---|
| `t_qt2` | `qt_floor` | 27.6 → 31.9 | 12.2 → 11.4 | 7.1 → 11.1 | 0.9 → 1.1 | 21 → 8 | 6 495 → 6 430 | 738 → 651 | 1.41 → 0.99 GB |
| `t_qt1` | `qt_pure` | 1 363 → 1 188 | 691 → 558 | 265 → 327 | 65 → 48 | 1 469 → **48** | 390 503 → 289 582 | 27 174 → 6 930 | 1.41 → 0.99 GB |
| `t_cp9` | `cp_andt` | 6 909 → 5 682 | 4 347 → 3 167 | 704 → 917 | 415 → 298 | 8 860 → 2 414 | 2 395 753 → 1 689 132 | 162 499 → 67 920 | 1.41 → 0.99 GB |
| `t_qt3` | `qt_deep` | 25 544 → 15 636 | 15 404 → 8 810 | 2 547 → 3 100 | 1 622 → 632 | 33 780 → 3 626 | 7 928 179 → 4 706 040 | 525 244 → 131 810 | 2.78 → 1.73 GB |
| `t_qt4` | `qt_named` | 25 813 → 16 070 | 15 399 → 8 874 | 2 569 → 3 091 | 1 611 → 650 | 33 771 → 3 617 | 7 917 550 → 4 695 411 | 525 260 → 131 826 | 2.78 → 1.73 GB |
| `t_cp1` | `cp_full` | 11 007 → 7 812 | 7 318 → 4 681 | 936 → 1 168 | 654 → 383 | 14 210 → 2 532 | 3 681 039 → 2 445 182 | 246 498 → 80 752 | 1.46 → 1.04 GB |
| `t_cp18` | `cp_twice` | 14 902 → 9 883 | 10 078 → 6 214 | 964 → 1 245 | 1 021 → 543 | 21 347 → 2 637 | 4 965 897 → 3 200 804 | 331 907 → 92 882 | 1.86 → 1.27 GB |
| `t_qt5` | `qt_deeper` | 101 388 → 53 012 | 62 305 → 29 902 | 11 058 → 11 746 | 5 860 → 1 782 | 128 043 → **6 460** | 29 447 197 → 16 164 444 | 1 917 588 → 331 910 | 9.54 → 5.26 GB |

Read it against §4.1, which is candidate D's column on the same probes:

- **It is not "no change at all".** §5 E predicted an unmemoized readback
  "will measure no change", and that is the one prediction of the design this
  pass corrects. On queries it is D's equal (`qt_deep` 4 706 040 against D's
  4 792 739); on **misses** and **steps** it is not close to D — misses fall
  9.3× at `qt_pure`, 19.8× at `qt_deeper`, steps 3.9× and 5.8× — because the
  spelling is a *deep* normal form with the registry's names kept folded, so
  the kernel hits where it used to miss. Resident memory falls with it
  (9.54 → 5.26 GB), and `decl_emit_ns` 3.3× (the chokepoint walks a smaller
  object).
- **The exponent stays, exactly as §5 E said it would.** `cp_andt` →
  `qt_deep` → `qt_deeper` is ×3.31 / ×3.71 in queries on the parent and
  ×2.79 / ×3.43 here; in steps ×3.23 / ×3.65 against ×1.94 / ×2.52; in gate
  ×3.54 / ×4.04 against ×2.78 / ×3.39. §6's bar — the ratios must fall
  *toward 1* in queries and steps and gate — is **not met**. One identity
  `map_at` still costs three times the item. The naming is the whole of the
  remaining distance, and §11.2 says how far it goes: 104 309 emitted nodes
  at `qt_deep` against 34 681 at `qt_pure`.
- `elab_whnf_ns` **rises** by roughly what the readback costs (2 547 → 3 100
  at `qt_deep`), because the site still runs the rewriter *and* the readback:
  stage one is installed after `Elaborator::whnf` rather than in place of it,
  deliberately, so that a decline is the parent's behaviour at the same site.
  A landed version skips the rewriter there, and that clock is the size of the
  gain it would take.
- `t_qt4` stays within **0.23 %** of `t_qt3` on both sides (§9 item 6): naming
  the reply in the library still does not matter.

The showcase, serial and at the default gate width:

| | off | fire |
|---|---|---|
| serial, item totals / kernel gate | 51.10 s / 38.05 s | **50.50 s / 36.92 s** |
| serial, wall | 52.08 s | 51.52 s |
| default width, item totals / gate | 58.72 s / 42.75 s | 58.00 s / 41.31 s |
| default width, wall / maxrss | 28.69 s / 4.95 GB | 27.60 s / 4.59 GB |
| misses / queries / steps | 207 075 / 14 533 673 / 4 624 434 | 189 401 / 13 215 537 / 4 420 603 |

and the named items, serial, `misses / queries`: `complete_post`
14 210 / 3 681 039 → **2 532 / 2 445 182**; `close_body` 2 707 / 1 318 201 →
2 687 / 1 316 861; `expr_body` 365 / 558 836 → 345 / 557 496; `factor_body`
381 / 558 868 → 361 / 557 528; `checked_expr` 17 995 / 520 342 →
17 943 / 520 258; `number_grammar`, `Grammar` and `Certified` unchanged to the
unit. As with D, **one item of the showcase moves and the rest are noise** —
the whole-run 9.1 % of queries is `complete_post`'s 33.6 %.

**And the per-item gate fails, in D's own shape.** Of the 944 joined rows,
misses rise on 14 (`list::append_nil_elim` 88 → 96, `list::rev_involutive`
356 → 357, twelve more of the same family, all +1 except that one), queries
rise on 1 (`list::append_nil_elim` 1 845 → 1 888) and steps rise on at least
30 (the listing is capped; `list::append_nil_elim` +568,
`calc_parser::number_selected` +172, the rest +2 to +5). The summed head-pair
table moves 206 914 → 189 240 misses over 52 rows, with five pairs rising
(`El(?)/Wf` 37 563 → 37 597, `Pi/Pi` 3 693 → 3 734, `Wf/El(?)` 790 → 805,
`Wf/El^δ` 8 → 32, `Wf/Wf` 11 → 17). The mechanism is §6's own audit line: a
readback changes the spelling of every component it writes, and a `list::*`
proof whose reduct the rewriter left weak-head now meets a deep normal form.
So stage one is **kept behind its flag** and is not proposed to land on its
own.

### 11.4 The naming: how the minted declarations would enter Ψ

What §6 asked to be said, now that §11.2 has priced it and stage one has shown
what the spelling has to be. Three findings constrain it:

1. A mint must name a **term at an arbitrary type** (§11.2's negative), and
   the type comes from the position, so the readback that mints is
   **type-directed**: it carries the type its parent's annotation gives it.
   The minted binding is then `Δ ⊢ body : T` — for the common case, a code,
   `Δ ⊢ ⌜T⌝ : Ty l`, which is what every existing device in `gendefs.rs`
   registers.
2. `Δ` is §6's "constructor telescope's local substitution" — `cx.gamma` —
   extended, for a sub-value under `k` of the tower's own binders, by the
   binder types the readback has just spelled; the use site is `u^δ` with `δ`
   the identity substitution of that context, which costs one node plus the
   substitution and carries **no annotations** (unlike an application).
3. The mint happens **during** expression elaboration, where the elaborator is
   `&self` and Ψ's indices are relative to its current length — so an eager
   push would invalidate every global reference the declaration emitted
   earlier. This is exactly the blocker
   `issues/record-projection-defs-declaration-cost` records for lazy
   projection registration, and it names the precedent: `meta_pushed`'s
   `RefCell`.

The mechanism this design proposes for it is the **goal arena's**
(`crates/elab/src/goals.rs`), which already solves the same problem for holes
and is the only device in the elaborator that lets Ψ grow across an item:

- `configure(written, reserved)` reserves a block at the innermost end of Ψ
  *before* the declaration is elaborated, and every reference emitted during
  it is already numbered past that block (`gen_ref`, `resolve` and
  `gen_def_of` all offset by `goal_arena.base()`);
- entries are allocated through `&self` into a `RefCell`, each with its own
  local context — a goal's binding is `GlobalBinding::Tm { ctx: goal.cx.gamma,
  …, body: None }`, and a mint's is the same with a **body**, so that
  `goal_arena.world()`'s padded Ψ makes the minted definition unfoldable by
  the elaborator's own whnf and conversion as soon as it is minted;
- at commit the block is *realized* rather than substituted away: the mints
  are pushed into Ψ (through the gate, as `push_gen_def` does), and the
  declaration's term is strengthened with a `GlobalSubst` whose mint entries
  are references to the bindings just pushed — the same `apply_global` +
  `strengthen_global` pass that already retires the goal block, with different
  entries. A mint that overflows the reserved block declines and the component
  stays inline, which is stage one's behaviour and is always safe.

What that leaves for the round that builds it, in the order the audit wants
them: the image and `ModuleDelta`'s dependency identity for a binding that is
not keyed by a declaration's tag (every `GenDef` today is), the cache identity
(`docs/cache-v1-design.md` §4 gives a generated definition its own), and the
per-item join — which stage one already fails on 14 small `list::*` rows, so
the naming round inherits that debt rather than creating it.

### 11.5 Tests, and what was not run

`crates/elab/src/rbemit.rs`'s own four (`docs/testing-generated-terms.md`'s
axes, scaled to what stage one is): a **literal** scrutinee whose computation
runs and lands on the rewriter's former; a **neutral** scrutinee, declined at
the head and spelled **folded** one level down, which pins §6's preference
(a); an **open** codomain read back under its binder against its closed
control, which pins the one structural difference from the rewriter — the
readback's answer is a *deep* normal form, so a `Vec` at a canonical length
steps under a binder where the weak-head rewriter leaves it; and a negative
control, a compressed successor program over a neutral tail past the cap,
which is **declined** rather than guessed at.

The full `scripts/test` is green on the furnace box — `== suite: 2701 passed,
0 failed, 5 ignored ==`, the four above being the new ones — and no fixture
moved: `WALK_RESIDUE` and the `psi().bindings.len()` fixtures are untouched,
because with the flag off the elaborator emits exactly what it emitted. (On
the desktop the same suite dies `INCOMPLETE` in `crates/cli`'s binary target
under parallel scheduling; it dies there on the **pristine** tree too, 2 688
passed against this tree's 2 692, so it is the box and not the change.)

`scripts/bench --check` on the desktop, where the committed baseline was
recorded, flags one row — `nat/step-once:256` 116 ns → 145 ns — beside
uniform improvements elsewhere (`wf/check-tree` 0.63–0.66×,
`check/generated-terms` 0.76×). `crates/kernel` is byte-identical to HEAD in
this tree, so both columns are the same compiled kernel and the whole table is
machine drift, not a change (`desktop-bench-gate-for-constants`).

Not run, because stage one is flagged off and is not proposed to land: the x86
rails at two sizes per item. They are the naming round's gates, and §8's list
of what a landing owes is unchanged.
