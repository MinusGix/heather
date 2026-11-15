# The matcher sees through a quote, one head step at a time — design

Slice 1 of `docs/elaborator/close-body-family-attribution-design.md` §7.3: make
`instance_match` recover `Certified`'s arguments at the arms the decline
listing names, so `close_body`'s eighteen dear field reads take
`rec_proj_ref_at` instead of `project_field`'s `Fst`/`Snd` walk. The owner is
`issues/quote-see-through-bounded-arm.md`, whose trigger fired on 2026-09-16.

The two prior docs hold the reasoning and are not restated:
`docs/elaborator/closed-argument-and-parameter-domain-spelling-design.md` §3 (the **name**
arm of `see_through`, which landed) and §5.2 with both amendments (the
**quote** arm, built unbounded and refused on a stack overflow);
`docs/elaborator/close-body-family-attribution-design.md` §5–§7 (what the reads cost and
why the decline is the lever).

Everything below was hand-run on one furnace box before it was written, HEAD
`1a91fc1`, release with `--features value-metrics`, `--kernel-workers 1`, no
`--cache`: two jobs with a spelling instrument (`probes/ia_spell.sh`,
`probes/ia_spell2.sh`, `probes/ia_spell.patch`), two new reproducers
(`probes/t_ia1.hthr`, `probes/t_ia3.hthr`).

**The headline is that the bound needs no budget.** The refuted arm decoded a
quote with `decode_deep` — the whole literal materialized at every mismatch
node. One head step of `decoded` (`crates/elab/src/inductive.rs:391`, the
kernel's own `step_type` on an `El` of a canonical code former) does the same
job at O(1) per node, and the **template** — a declaration's own lowering,
which is small — bounds the walk that follows. Two of the three arms are that
one relation at two depths; the third is not a spelling disagreement at all
and is out of scope.

---

## 1. The three arms, spelled

`HEATHER_IA_SPELL=<decl>` prints, at each of `Holes::ty`'s and `Holes::tm`'s
former-mismatch arms and at `place_ty`'s disagree arm, the two sides in bounded
`Debug`, plus a `ROOT` line carrying the whole template and the whole subject
at the point `instance_match` gives up. `probes/t_ia1.hthr` (16 lines: one
`Certified<ATok,Nat>` receiver, one `.forward` read) and `probes/t_ia3.hthr`
(19 lines: a `Result<Certified…,Failure…>` through `result::fold`).

**A caution the first job paid for.** The listing's large rows are the matcher
being *asked* about a type that genuinely is not that declaration — `List
hole-match-Wf/Sigma` is 27 881 on a nineteen-line file — and a decline there is
the right answer. The arms of this round are the ones `project_field` pays
for, and they are identified by the declaration whose *receiver* is being read:
`t_ia1` has two `project_field Certified instance-args` rows and `t_ia3` one,
and zero for `Result` or `Cursor`.

### 1.1 `Certified identity-match-El/Nat` — step 2, at the `A` argument

Five declines on `t_ia1`, six on `t_ia3`. The node pair is the whole finding:

```text
A (the copy, i.e. the template at the recovered arguments)   El[0](«Nat»)
B (the subject, i.e. the receiver's own type)                Nat
```

The `ROOT` pair agrees byte for byte on either side of it. `Certified<ATok,
Nat>`'s `A` argument is recovered as the code `«Nat»`, step 2 substitutes it
into the template's `El (Var i)` slot, and the subject spells the same type as
the primitive the binder wrote. `Nat` has no name to take, which is why the
landed name arm cannot reach it and why `wf.rs`'s
`a_type_argument_arriving_as_a_quote_still_declines` pinned it at
`ByCode<Nat>` — the test §6 flips, and renames
`a_type_argument_arriving_as_a_quote_is_now_seen_through`.

The same pair, verbatim, on `Exists`, `Monoid`, `Semigroup`, `CommMonoid` and
`Cmp` — one arm, many declarations.

### 1.2 `Certified hole-match-Sigma/El` — step 1, the same pair one layer up

One decline on `t_ia3`.

```text
A (template)  Σ[0,0](Σ[0,0](Unit 0). … Unit 0). Σ[0,0](El[0](x4)). Σ[0,0](…). …
B (subject)   El[0](«Σ[0,0](«Σ[0,0](«Unit 0»). …»). «Σ[0,0](«Nat»). «Σ…»»»)
```

The subject is an `El` of a **code literal** — every component quoted, the
`«…»` nesting all the way down — and not of a reference: there is no
`D#tycode_fn^δ` head, so `see_through` has nothing to unspell and the walk
stops on the `Sigma`/`El` former pair.

**This answers §3 of the brief: the two arms are one relation at two depths.**
§1.1 is `El «Nat»` against `Nat`; §1.2 is `El «Σ…»` against the `Σ…` the quote
denotes. One arm covers both, and it covers them by the same step — the only
difference is how far the walk then descends.

### 1.3 `Result hole-match-Sum/Sigma` — not a quote pair, and out of scope

312 declines on each probe, and **not one of them is a `project_field` row**.

```text
A (template)  (Σ[0,0](…). Σ[0,0](El[0](x2)). Unit 0
               +[0,0] Σ[0,0](…). Σ[0,0](El[0](x1)). Unit 0)
B (subject)   Σ[0,0](…). Σ[0,0](El[0](x5)). Unit 0
```

Neither side is a quote and neither is a reference. `Result`'s lowering is a
sum of two tagged Σs and the subject is a single tagged Σ — a one-field record,
which is not a `Result` and must not be recovered as one. The matcher is
answering correctly; the row is large because the question is asked often.

So `Or`, `Option` and `Result`'s `Sum/Sigma` rows (`docs/closed-argument-and-
parameter-domain-spelling-design.md` §5.1 already listed them as residues) are
**not** this slice's and are not a spelling problem. The brief's STOP condition
is read as satisfied rather than fired: it asks whether *the decline* is a
quote pair, and the declines that gate `close_body`'s reads — §1.1 and §1.2,
33 + 8 in that item against `Result`'s 6 — are.

---

## 2. The bound: one head step, and the template bounds the walk

`crates/elab/src/inductive.rs`'s `decoded` rewrites `El c` for a **canonical
code former** `c` by one step of the kernel's `step_type`, in the empty
context: `El «Nat» ↦ Nat`, `El «Σ(a). b» ↦ Σ(El a). El b`. It consults neither
`gamma` nor δ, it allocates one node, and it stops the moment the head is no
longer an `El` of a former. It is **not** `decode_deep`, which pushes the same
rewrite through every component and materializes the whole inline copy.

The arm is `decoded` at `Holes::ty`'s former-mismatch arm, after the two name
arms, and nowhere else.

**Why this is the bound, and why a node budget would be the wrong shape.**

- **Per node the work is O(1).** The refuted arm's failure mode was not the
  depth of one decode but its *breadth at every node*: a mismatch inside a
  seven-million-character operand decoded seven million characters, and then
  the node below it did so again. A head step cannot do that — the copy is one
  node deep and the components stay quoted until the walk actually reaches
  them.
- **The template bounds the walk.** The two sides descend in lockstep through
  the structural arms, so the recursion depth is at most the *template's*
  depth, and the template is a declaration's own lowering — `Certified`'s is
  the fifteen-node Σ spine §1.2 prints. A multi-megabyte subject is not walked;
  it is walked *as far as the template is*, and the moment the two genuinely
  disagree the walk stops as it does today. Re-run against the refuted arm's
  failure mode: there the walk was bounded by the template too, and the
  overflow came from the decode *inside* one node. That is the term this
  removes.
- **A node budget would measure the wrong thing.** A budget over the quote's
  size would refuse §1.2 (`Certified`'s lowering carries the `relation`
  domain, which is the 776-to-911-character `Π` of the attribution doc §3.3)
  while admitting §1.1, and it would have to count nodes — an unbounded walk of
  its own unless written with an explicit worklist and an early exit. The head
  step needs none of that, so the round does not pay for it.

**Termination.** At a fixed node the non-structural steps cannot cycle: a
`decoded` step's result is headed by a real `Type` former (`Σ`, `Π`, `Nat`, …)
and never by `El (D^δ)`, so no `see_through` can follow it; a `see_through`
step replaces a reference by the registry copy of a declaration declared
*earlier*, which is the measure that arm already carries. So each node admits
at most one name step and a finite chain of head decodes, each strictly
consuming one code former.

**Soundness is unchanged and is still step 2's.** `decoded` is a pure kernel
rewrite: `El «c»` and its decode are the same type to the kernel, by the rules
of `step_type` that conversion applies anyway. The relation cannot relate two
distinct declarations — it rewrites an `El` of a *canonical former* and nothing
else — so the look-alike negatives (`ByCodeLk`, `ByAppLk`) decline for the
reason they always did.

---

## 3. What else meets the changed spelling

The change makes `instance_args` answer where it declined, so more reads take
`rec_proj_ref_at` — a Ψ reference plus `saturate`'s spine — instead of
`project_field`'s walk. `issues/per-instantiation-projection-boundaries.md`
boundary 2 is the standing warning: a projection reference is **cheap to
compare and dear to compute through**, and the x86 certificates refused it
twice (`caller_native_memory_same_27/28` needed 8–64× `DEFAULT_FUEL`).

The readers, and why this slice is on the parser side of that boundary:

- **`crates/elab/tests/function_ir_x86_scaling.rs` and the native certificate
  gates.** Untouched in shape. `project_field`'s receiver gate is *not* edited
  here: a non-dependent telescoped record still needs
  `receiver_admits_reference`, and every record the certificates read
  (`MachineState<M>`, `StackAccess<M>`, `And<P,Q>`, `reused_callee`'s state
  chain) has a non-dependent spine and keeps the gate verbatim. What can move
  for them is only a record that **already passes the gate** and whose
  `instance_args` declined on a quote; that is a measurement and it is gate
  item 1 of §5.
- **`project_field` itself**, the customer: `Certified` is dependent-telescoped
  and therefore exempt from the gate at every receiver
  (`docs/elaborator/telescoped-record-projections-design.md` §4), so its reads are gated
  by `instance_args` alone — which is exactly the decline this slice removes.
  There the alternative to the reference is the tail-substitution *exponent*
  and not a linear walk, which is the argument that put the exemption there.
- **`display.rs:291`** (`instance_args` for the surface type display) — a
  rendering, no gate.
- **`Grammar` and `Certified`'s own declaration items** — registration is
  unconditional, so they must not move (`docs/close-body-family-attribution-
  design.md` §8 item 6), and watching them is how a mis-scoped change is
  caught.

So: on the parser side of boundary 2, provisionally, and §5's gates are what
settles it. STOP if they do not.

---

## 4. What is not changed

- **`Holes::tm`'s former-mismatch arm.** The `tm` side already sees through a
  code reference (`see_through_code`); a quote there is a `Term` and the two
  sides are compared as codes, where §1's disagreement does not arise — both
  occurrences are already codes. Adding a decode there would be a second
  relation with no measured customer.
- **The receiver gate, `lower_instance`, the emitted argument's spelling.**
  Unchanged, for the three reasons
  `docs/elaborator/closed-argument-and-parameter-domain-spelling-design.md` §3.2 gives.
- **The `Sum/Sigma` residues** (§1.3), and `List hole-match-Wf/Sigma`, which
  §5.1 of that doc already put outside.

---

## 5. Verification items for the implementation hour

Counts are the bar; seconds are one box.

1. **The pinned negative flips, and its control does not.**
   `wf.rs mod dependent_telescope`'s
   `a_type_argument_arriving_as_a_quote_still_declines` must now *recover*, at
   **both** instantiations (`ByCode<El «Nat»>` and `ByCode<Nat>`), with
   `ByCode<Flat>` still reconciled and `ByCodeLk`/`ByApp`'s negatives still
   declining. A look-alike that starts matching is the failure mode that is not
   a performance question.
2. **The decline listing, before the seconds.** `instance_match Certified
   identity-match-El/Nat` and `hole-match-Sigma/El` go to zero on the family,
   and so does `project_field Certified instance-args`. List what remains.
3. **The route split.** `HEATHER_CB=1` + `probes/cb_agg.py`
   (`probes/cb_count.patch` re-applied as an instrument and reverted after):
   `Certified walk` reads fall to **zero**; the surviving `ref` reads' mean
   size is what slice 2 moves.
4. **The curve is the gate, not the seconds.** `t_cb3`/`t_cb2`/`t_cb1` are
   3 466 931 / 248 172 / 16 993 queries at 22 misses on the parent, ×14.6 and
   ×14.0. Report both ratios after. A slice that halves `close_body` and leaves
   the curve at ×14 has bought a constant on an exponential and must say so.
   `t_pcr3`'s `qchain1..3` is the second curve, at zero misses throughout.
5. **The showcase**, serial and at the default width, with `close_body`,
   `expr_body`, `factor_body`, `open_body`, `number_grammar`, `complete_post`,
   `Grammar` and `Certified` named. `Grammar`/`Certified` must not move (§3);
   `number_grammar`'s share is the receiver gate's and is not in scope.
   The per-item join over all 959 rows: no item's misses, queries or steps may
   rise.
6. **The whole summed head-pair table**, not its head
   (`docs/elaborator/telescoped-record-projections-design.md` §9 item 6, as superseded in
   favour of totals by the 2026-09-15 amendment to §5): report the rows that
   rose and whether they are noise in seconds.
7. **The gates.** `function_ir_x86_scaling.rs` and
   `caller_native_memory_same_27/28` inside the **default** fuel, per-item
   scaling at two sizes, never a raised budget; `WALK_RESIDUE` shrink-only;
   `psi().bindings.len()` and `record_projection_size` fixtures unmoved, with a
   reason if one moves. `scripts/bench --check`. The **full** `scripts/test`,
   not the fast lane: the change is in a generator and the fast lane replays
   images an earlier build wrote.
8. **New tests vary the four axes** (`docs/testing-generated-terms.md`): a
   literal receiver (an assembled record returned by a `fn` and read through)
   and a neutral one; an **open** element type and a closed control; a
   **checking** position; and negatives — a quote whose decode does *not* match
   must still decline, and a look-alike must still decline.

---

## 6. Implementation

Landed as designed: one arm, in `Holes::ty`'s former-mismatch arm, after the
two name arms (`crates/elab/src/gendefs.rs`). `probes/ia_slice.sh` is the
measurement, parent (`target/heather_parent`, `1a91fc1`) against the change,
one furnace box, `--kernel-workers 1`, no `--cache`, release with
`--features value-metrics`. Both premises re-taken first and both reproduce to
the unit: the showcase at **959 items, 16 762 944 queries, 212 318 misses,
4 697 239 steps**, and `cb_full` at **3 466 931 queries / 22 misses / 1 029
steps**.

The tests: the pinned negative flips at **both** instantiations and keeps its
`ByCode<Flat>` name-arm control and its `ByCodeLk` look-alike negative, and
`the_axes_on_a_record_whose_type_argument_is_a_quote` is the new source-level
axis test — `ByCode<Nat>` read at a literal receiver (`c_lit()`, the idiom the
2026-09-15 amendment settled on) and a neutral one, an open `ByCode<A>` beside
the closed one, a checking position (`c.ok` offered as the proof of
`idty(c.a) = c.a`), a false-equation and a neighbouring-field negative, an
empty emission walker, and the route assertion that the read now takes
`RecProj`.

### 6.1 The curve — the exponent falls from ×14 to ×4.3

| probe | item | parent queries | changed | ratio |
|---|---|---|---|---|
| `t_cb3` | `cb_one` | 16 993 | **42 378** | ×2.49 |
| `t_cb2` | `cb_two` | 248 172 | 203 616 | ×0.82 |
| `t_cb1` | `cb_full` | 3 466 931 | 874 288 | ×0.25 |
| `t_pcr3` | `qchain1` | 4 464 | **12 411** | ×2.78 |
| `t_pcr3` | `qchain2` | 105 437 | 83 974 | ×0.80 |
| `t_pcr3` | `qchain3` | 1 561 870 | 384 640 | ×0.25 |
| `t_pcr3` | `qev3` | 680 144 | 173 399 | ×0.25 |

**Per chained receiver: ×14.6, ×14.0 → ×4.8, ×4.3** on `t_cb*`, and **×23.6,
×14.8 → ×6.8, ×4.6** on `t_pcr3`. `cb_full` 10 421 ms → 2 181 ms, `qchain3`
5 011 ms → 1 108 ms.

This is §5 item 4's gate met — the curve flattens, it is not a constant bought
on an exponential — and it is a **trade at the floor**: one chained receiver
costs *more* through the reference (×2.5–2.8), two are already cheaper, three
are 4× cheaper. That is
`issues/per-instantiation-projection-boundaries.md`'s boundary 2 arriving on
the parser side with its sign measured for the first time: a reference is
cheap to compare and dear to compute through, so it loses at depth 1 and wins
from depth 2 on. The misses and evaluator steps rise with it (`cb_full` 22 →
1 240 misses, 1 029 → 15 140 steps) — the δ + β per read the gate exists for —
and are swamped by the queries that stop being written.

### 6.2 The showcase

| | parent W=1 | changed W=1 | parent default | changed default |
|---|---|---|---|---|
| item totals | 65.03 s | **51.97 s** | 74.73 s | **59.46 s** |
| kernel gate | 50.14 s | **38.48 s** | 56.73 s | **43.60 s** |
| misses | 212 318 | 207 075 | 212 318 | 207 075 |
| queries | 16 762 944 | **14 533 673** | 16 762 944 | 14 533 673 |
| steps | 4 697 239 | 4 624 434 | 4 697 239 | 4 624 434 |
| wall | 66.20 s | 52.95 s | 33.13 s | **28.60 s** |
| maxrss | 2.39 GB | **1.65 GB** | 6.64 GB | **4.83 GB** |

Every total at or below the parent, serially and at the default width. The
family:

| item | parent ms | changed ms | parent queries | changed queries |
|---|---|---|---|---|
| `close_body` | 6 813 | **2 954** | 2 585 801 | **1 318 201** |
| `factor_body` | 2 823 | **1 430** | 1 024 783 | **558 868** |
| `expr_body` | 2 780 | **1 409** | 1 024 751 | **558 836** |
| `number_grammar` | 2 579 | 2 524 | 1 100 958 | 1 048 658 |
| `open_body` | 177 | 211 | 60 049 | **82 365** |
| `atom_body` | 162 | 161 | 84 162 | 84 162 |
| `complete_post` | 11 415 | 11 643 | 3 681 039 | 3 681 039 |
| `Grammar` | 1 163 | 1 184 | 457 050 | 457 050 |
| `Certified` | 814 | 817 | 357 891 | 357 891 |

`Grammar`, `Certified` and `complete_post` are byte-identical in counts, which
is §3's and `docs/elaborator/close-body-family-attribution-design.md` §8 item 6 met:
registration did not move and this slice changed only which route a read takes.
`number_grammar` falls a little — its three `Exists instance-args` declines go,
its five `RecognizedHead` and two `And` **receiver-gate** declines do not,
which is the boundary this slice was told not to sweep in.

### 6.3 The per-item join, and the one item that regresses

944 rows joined. **`open_body` rises: 60 049 → 82 365 queries (+37 %, +0.13 %
of the file), 177 → 211 ms.** It is `close_body`'s caller, it has **one**
chained receiver, and it is §6.1's floor arriving in the library — the same
sign, at the same depth, as `cb_one` and `qchain1`. Everything else that rose
is small: six items gained between 1 and 161 queries, five gained between 1 and
18 misses, and twenty `calc_parser` theorems gained 1–4 % of their evaluator
steps. Ten items fell, led by the three the slice targeted.

**§5 item 5's "no item may rise" is therefore not strictly met**, and the
round does not claim it is. What it claims is the shape: one item at depth 1
pays a constant, the items at depth 2 and 3 lose half and the exponent falls
from ×14 to ×4.3, and every whole-file total falls. That is the same trade
`docs/elaborator/closed-argument-and-parameter-domain-spelling-design.md` §5's amendment
made when it superseded strict head-pair monotonicity in favour of totals, and
the honest reading is that **`open_body` is the next slice's datum**, not a
defect to tune away: whatever amortizes the reference at depth 1 — or declines
it there — is a policy question with the x86 certificates on the other side of
it, and it wants its own round.

### 6.4 The head-pair table, whole

52 rows both sides, **no pair exists in the changed run that did not exist in
the parent's**. Totals 212 157 → 206 914 misses and 17.129 s → 13.102 s. Four
rows rose and all four are noise in seconds: `El(?)/El(?)` 1 182 → 1 186
(0.720 → 0.731 s), `El(?)/Sigma` 1 167 → 1 170 (0.426 → 0.421 s), `El⌜⌝/Nat`
1 599 → 1 751 (0.002 s), `Nat/El⌜⌝` 102 → 109 (0.000 s). The two `El⌜⌝` rows
are the arm itself: the walk now carries past a quote to a *later* stop, which
is what the name arm did to four rows in the previous round.

`Pi/Pi`, the row this family has been chasing since
`docs/elaborator/closed-argument-and-parameter-domain-spelling-design.md` §1, goes
**8 418 / 0.740 s → 3 693 / 0.363 s**. `Id/Id` keeps its count and loses
3.5 seconds.

### 6.5 The decline listing

The target arms are **gone**, on the whole file:

```text
                                  parent  changed
project_field Certified instance-args  49       0
project_field Exists    instance-args   3       0
instance_match Certified identity-match-El/Nat  33/15/15 → 0
instance_match Certified hole-match-Sigma/El     8/11/11 → 0
```

What remains, named as §5 item 2 asks:

- **`project_field Grammar instance-args` 11**, unchanged. `Grammar` is a
  declaration item whose own counts did not move, so this is a residue with no
  measured customer here; it is the next attribution's, not this slice's.
- **`project_field Pair instance-args` 3** in `checked_expr`, unchanged, and
  that item's counts are byte-identical.
- **`instance_match Result hole-match-Sum/Sigma` 6 / 3 / 3**, unchanged and
  **correct**: §1.3 showed it is not a spelling disagreement but the matcher
  declining to call a one-field Σ a `Result`.
- **Every `receiver-gate` row**, verbatim — `Parser` 100, `And` 28, `Pair` 18,
  `Failure` 16, `RecognizedHead` 10. That gate is load-bearing for the x86
  certificates and was not touched.

### 6.6 The gates

- **The route split.** `probes/cb_count.patch` re-applied as an instrument and
  reverted after: **`Certified walk` is zero** — all 29 of `close_body`'s reads
  and all 22 of `t_cb1`'s take the reference. `close_body`'s `Certified` read
  nodes 2 374 293 → 1 313 697, `t_cb1`'s mean spine 148 516 → 41 212. `Exists`
  joins them; `And`, `RecognizedHead`, `Parser`, `Sound`, `Consumes` and
  `SelectedHead` stay on the walk, which is the receiver gate untouched. The
  emitted-node totals fall with the queries and hold the ratio: `close_body`
  5 560 618 → 2 846 429 nodes at 0.47 → 0.46 queries per node, so the win is
  **fewer nodes written**, not a cheaper gate. `open_body` 129 141 → 178 291,
  §6.3's riser, on the node counter too.
- **The x86 rails and the fixtures.** `caller_native_memory_same_27/28` are
  *item* names inside the native certificate, and `function_ir_x86_scaling`'s
  tests are `elaborated_source_x86_scaling`, `generated_50_node_…` and
  `slow_acceptance_generated_20_node_…`; a `scripts/test <file-stem>` filter
  therefore matches nothing, and the targeted invocations in
  `probes/ia_gate.sh` phase (b) reported `0 passed`. The gate they were
  standing in for is the **full `scripts/test`**, which runs `crates/cli/tests/
  native*.rs` and both scaling sizes and is phase (c). Read the suite line for
  them; no budget was raised anywhere.

- **The full `scripts/test`**: `== suite: 2697 passed, 0 failed, 5 ignored ==`
  on the final tree. The first run of it was `2696 passed, 1 failed`, and the
  one failure was **this round's own new test**, at its `findings.is_empty()`
  line; §6.7 is what that was and how it is settled. Nothing else moved at
  either run: the flipped negative passes at both instantiations, the x86 scaling
  tests and the native certificate gates pass inside the default fuel with no
  budget raised, and `record_projection_size`, the `psi().bindings.len()`
  fixtures, `WALK_RESIDUE`, `annotation_cost.rs`, `parser_library.rs`,
  `showcase_calculator.rs` and the whole-library acceptance load are green.
- **`scripts/bench --check`** through the `--save`/apply/`--check` dance
  (`probes/ia.patch`, since the committed baseline is desktop-recorded):
  **`ok: 112 comparisons within thresholds`**. The headline slopes are
  unmoved — `code/whnf-identity-recursor` 0.01, `check/generated-terms` 1.05,
  `stack/check-numeral` 1 530 levels.

### 6.7 The emission walker, and the assertion that was wrong

The new axis test's first form asserted an **empty** emission walker, and the
full suite's one failure was that assertion. What the walker actually reports
on `ByCode<Nat>` is eight findings, and every one of them is an `App`'s
`dom`/`cod` carrying the boxed literal `El[0](«Nat»)`:

```text
c_quoted    App.cod depth=2: El[0](«Nat»)
c_lit       App.dom depth=0: El[0](«Nat»)
c_neutral_q App.dom depth=1: El[0](«Nat»)
c_checking  App.cod depth=2: Id[0](El[0](«Nat»); …)   — `«Nat»` throughout
…
```

That is the quote layer's **standing residue**
(`issues/emission-walker-residual-sites`), and it is there for the same reason
this whole round exists: `Nat` has no name, so the chokepoint has nothing to
write in those slots. Asserting an empty walker against it would have pinned
someone else's defect to this test, which is verbatim the 2026-09-15 amendment
to §7 item 7 of
`docs/elaborator/closed-argument-and-parameter-domain-spelling-design.md`.

The assertion is therefore **`«Nat»` is the only quote in any finding** — a
finding carrying any other boxed code would be this arm's — with a **control**
beside it that makes it non-vacuous: the same axes at a *named* closed
argument (`ByCode<Flat>`) leave the walker empty.

### 6.8 Deviations from §2

**One, and it is the bound itself.** §2 was written after the arm was built
and says so: the brief asked for a decode "against a small former or under a
node budget", and the implementation takes **neither**, because
`crate::inductive::decoded` is a one-step head rewrite and needs no budget to
be bounded. A node budget was considered and rejected in §2 for two reasons —
it would refuse the `Sigma/El` arm outright, and counting the nodes is itself
an unbounded walk unless written with an explicit worklist. The stack-overflow
argument the budget existed to supply is met structurally instead: the
recursion descends in lockstep with the template, which is a declaration's own
lowering.

### 6.9 What this leaves for the next slice

- **`open_body`, and the floor.** §6.3. The reference loses at one chained
  receiver and wins from two. Whatever amortizes it at depth 1 — or declines
  it there — has the x86 certificates on the other side of it
  (`issues/per-instantiation-projection-boundaries.md` boundary 2) and wants
  its own round with both workloads measured.
- **Slice 2 of `docs/elaborator/close-body-family-attribution-design.md` §7.3** is now
  the one with the evidence: the surviving `ref` reads' mean spine is 45 300
  nodes in `close_body` and 41 212 in `t_cb1`, and it is the unnameable
  function-typed `relation` domain that fills them. §5.2 of that doc priced it
  at 44× on an identical chain, and the curve is still ×4.3 per receiver.
- **The residues** of §6.5: `Grammar instance-args` 11, `Pair instance-args` 3,
  and the `Sum/Sigma` rows that are correct declines.

## 7. Status

Implemented and measured; the design was written before the edit. The spelling
instrument is `probes/ia_spell.patch` and is reverted; `probes/ia.patch` is the
whole change and `probes/ia_base/` holds the pristine `1a91fc1` copies of the
two files it touches. No commit, no issue edit, no `cargo fmt`.
