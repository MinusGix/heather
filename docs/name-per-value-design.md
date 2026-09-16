# One name per value: the free-variable-scoped mint — design

Design pass with a measured instrument, on
`issues/elab-emits-normal-form-of-matched-type-argument`, the successor of
`docs/projected-tuple-tower-design.md` §12. That round stopped on a sentence:
the heavy shared sub-values of the tower "are not closed — they mention the
binders they sit under", one name per *depth* is all they can have, and
§11.2's 80 477 "was never reachable by any emitter". The reading this pass was
given says the sentence overreaches. A value that is **one pointer** reached
under two binder chains cannot depend on either chain's binders — a closure
under a binder is a different object and `Env` entries are values — so a mint
abstracted over **exactly its free variables** is one name per *value*,
referenced under any chain by `u^δ` with δ supplying that chain's own
variables, and depth-independent by construction.

**The reading holds, and it is the missing order of magnitude.** Measured on
the emitter's own graph, with the threshold §11.2 fixed: `complete_post` emits
**89 132** nodes against §12.3's best 708 206 and §11.2's predicted 80 477;
`qt_deep` **115 125** against 574 472; and the per-layer ratio
`qt_pure → cp_andt → qt_deep` is **×2.47 / ×1.31**, which is the *value
graph's* curve (§11.1's ×2.35 / ×1.31) and not the emitter's ×2.54 / ×2.61.
§6's first-hour check, "`qt_deep`'s emitted node count is a small multiple of
`qt_pure`'s and not 18× it", comes out at **×3.23** against the predicted ×3.0
and §12.3's ×6.6. **Not one** shared value that clears the threshold is
reached under a chain missing one of its free variables, on any probe or on
any of the showcase's `build_ctor` reducts.

§12.5's `min=` column was the same rule asked one level too shallow — a
smaller Δ over syntax that was *already keyed per depth*, so it shrank the
contexts and never merged the occurrences — and that is why it bought 6 %
instead of 8×. What §12.5's `HEATHER_RB_MERGE` refuted is an emitter that
merges occurrences *without* re-indexing, which it says itself; the
re-indexing is the mechanism and it was never measured. §12's sentence is
withdrawn to its true scope in §3.

Everything below is measured **locally** — the numbers are node counts and are
machine-independent; no clock is quoted — release with
`--features value-metrics`, `--kernel-workers 1`, `--timings`, no `--cache`,
one process per file, under `(ulimit -v 8388608 -t 1800; …)`.
`probes/nv_table.sh`, `probes/nv_showcase.sh` and `probes/README.md`'s round
section say in what order.

---

## 1. The instrument

`crates/elab/src/rbcount.rs`, `HEATHER_RB=fv` — one new mode on §11.1's
value-graph walk, and the only source change in this pass. The walk itself is
unchanged and its `rb count` line still reads §11.1's two columns. What the
mode adds is, per graph node:

- its exact **free-variable set** `fv`: the `Head::Var` identities reachable
  through the value — through `Env` entries and closure bodies, transitively —
  less the ones the node itself opened. A bottom-up fold over the graph, so in
  the graph's time;
- what is in scope at it **on every path**, the intersection over its
  occurrences of (the ambient Γ ∪ the binders opened above it), and — the
  instrument's own self-test — what is in scope on *some* path, the union;
- the emitted count under the rule the pass exists to price: **one mint per
  value, `Δ = fv`, a reference charged `1 + |fv|` nodes**, over the same
  bottom-up fold §11.2 used; plus an `ideal=` column that repeats it with the
  scope test waived, and a `flat3=` column at §11.2's flat reference cost, so
  the two columns are comparable to that table.

Three keyings, because the answer depends on which graph is being asked about
and the pass turns on telling them apart:

- **`HEATHER_RB_FVSPLIT=1` (with `HEATHER_RB_FVDEPTH=1`): the emitter's own.**
  `rbemit.rs` keys a sub-structure on `(CloId, d)` and re-reads an *out-of-line*
  forced value — a neutral's substitution entry, a `Vec`'s length — at the
  depth it meets it at, with no memo at all (`rbemit.rs`'s `shared`). This
  mode keys the counter the same way. **It is the column to read**, and the
  check that says so is that its `naive` reproduces §12.3's `naive` column —
  the exact node count of the readback's own syntax — to the unit on all four
  rows.
- **Default: unique binder identities.** Every opening takes its own identity
  from a counter rather than the walk's depth, and every node is keyed on
  closure identity alone. Depths alias — two branches at the same depth call
  different binders `17` — so this is the only keying in which a scope test is
  exact rather than positional.
- **`HEATHER_RB_FVDEPTH=1` alone: §11.1's graph**, where `naive`, `graph` and
  `shared` come back to the unit and the scope test degenerates to "is the
  chain long enough".

The checks, all of which pass:

| check | result |
|---|---|
| `naive`/`graph`/`shared` = §11.1's, depth keying | 332 848 / 26 043 / 546; 1 304 352 / 61 181 / 1 103; 4 967 022 / 80 519 / 1 430; `complete_post` 1 957 109 / 62 058 / 1 132 (it moves ±0.1 % with which probe file the library is checked beside — the three `t_*` rows do not move at all) |
| `naive` = §12.3's readback syntax, split keying | 293 908 / 1 056 154 / 4 006 444 / 1 584 491 — **all four to the unit** |
| `closed` (values with `|fv| = 0`) on `complete_post` | **7**, §12.5's seven closed nodes, from the other side |
| `opaque`, `basevar`, `decl` | **0** everywhere |

The last row matters for the design and not only for the instrument: no
threshold-clearing value's mass includes embedded syntax whose variables the
walk cannot resolve (a code payload, a `TyApp` argument), none mentions the
abstract prefix `g`, and none is one of the compressed-run or pending-algebra
shapes `rbemit.rs` declines. A landed device inherits no new decline class
from any of the three.

---

## 2. The decisive table

T = 64, the threshold §11.2 measured and §12.3 re-confirmed. Split keying —
the emitter's. `Δ = fv` is the rule with the scope test enforced; it is equal
to the `ideal` column on every row, because **`bad = 0`**.

| probe | item | naive | graph | shared | ≥T | **Δ = fv** | §11.2 predicted | §12.3 best |
|---|---|---|---|---|---|---|---|---|
| `t_qt1` | `qt_pure` | 293 908 | 26 920 | 531 | 35 | **34 / 35 651** | 34 681 | 73 236 |
| `t_cp9` | `cp_andt` | 1 056 154 | 68 974 | 1 065 | 20 | **20 / 88 053** | 79 298 | 217 492 |
| `t_qt3` | `qt_deep` | 4 006 444 | 90 240 | 1 374 | 24 | **24 / 115 125** | 104 309 | 574 472 |
| library | `complete_post` | 1 584 491 | 69 756 | 1 094 | 22 | **21 / 89 132** | 80 477 | 708 206 |

- **The shape.** ×2.47 / ×1.31 per combinator layer, against §11.1's value
  graph at ×2.35 / ×1.31 and §12.3's emitter at ×2.54 / ×2.61. The second
  ratio is the one that discriminates: 1.31 against 2.61. §6's bar — the
  ratios must fall *toward 1* — is met for the first time in four rounds.
- **The size.** 2.1× / 2.5× / 5.0× / **7.9×** against §12.3's best, and
  against the *rewriter's* reduct — the object the parent path hands the
  kernel — `complete_post` goes 2 634 824 → 89 132, **29.6×**.
- **Against §11.2's prediction**, +2.8 % / +11.0 % / +10.4 % / +10.8 %. The
  prediction was low for a reason worth writing down: it was computed on the
  *merged* graph, which merges an out-of-line forced value across depths, and
  no emitter can (§1). 89 132, not 80 477, is the honest ceiling of this
  mechanism on `complete_post`, and it is reached.
- **Twenty to thirty-five declarations per reduct**, which is §11.2's own
  estimate of how many are worth naming; the `≥T` column is lower than
  §11.2's because the split graph's shared values are individually smaller,
  not because fewer are nameable.

**Over the whole showcase** (8 092 `build_ctor` reducts, exactly §11.2's and
§12.3's count): 6 195 shared values, **344** clearing T = 64, **`bad` = 0**,
302 of them closed (`|fv| = 0`), and **336 mints in 16 items** — the two
grammar builders 83 each, `complete_post` 21, four more grammars 20 each,
`grammar_sound` 16, six bodies 10 each, and 2–4 in three small ones. The whole
run emits **1 053 845** nodes against §12.3's 1 768 398 for the same 8 092
reducts. As in every round since §4, one family of items moves and the rest is
arithmetic: the showcase total is 1.7× because most reducts have nothing worth
naming, and `complete_post` alone is 7.9×.

**`Δ` is small.** Mean `|fv|` over the threshold-clearing values is **2.4 to
2.7** and the maximum is **5**, against §11.4's "Γ extended by every binder
above it", which on these items is 17 to 31 entries. That is the reference
cost — `1 + |fv|` rather than `1 + |Γ| + depth` — and it is also why the
`flat3=` column (§11.2's flat 3-node reference) is within 0.1 % of it: at this
width the two are the same number, so none of the gain is an artefact of the
cost model.

---

## 3. The verdict on the reading, and what §12 got wrong

**Not one clean counter-example exists.** Across the four probes in all three
keyings and across the whole showcase, no shared sub-value that clears the
threshold is reached under a binder chain that does not contain all of its
free variables (`bad = 0` in split keying — on the four probes and on all 344
of the showcase's threshold-clearing values; `badc = 0`, the same test
restricted to values with no contaminated ancestor, in the other two). The
premise the
reading rests on — that a value which is one pointer under two chains depends
on neither chain's binders — is what the value graph actually looks like.

§12's own instrument could not see this, and the reason is exactly one
asymmetry between the two walks. `rbcount.rs`'s counter memoizes an
out-of-line forced value on its **address alone**, merging its occurrences at
every depth, while `rbemit.rs` re-reads one at the depth it meets it at. In
the merged graph one to three shared values per reduct are reached under
chains of different **length** — the value carries a variable one occurrence
has no binder for at all — and every scope failure the instrument reports in
that keying is downstream of one of those (`badc = 0`, `solo` 24–116 of
26 000–80 000 nodes). Key the counter the emitter's way and they are **gone**:
`unb = 0`, `short = 0`, `solo = 0`, `bad = 0`, and `naive` snaps to §12.3's
column to the unit. So the cross-length sharing was a property of §11.1's
*memo*, not of the object — which also says that §11.2's 80 477 was priced
over sharing an emitter cannot spend, and §2's 89 132 is what is actually
there.

What §12.5 measured, restated: a minimal Δ over syntax keyed per depth is
worth 6 %, and merging across depths *without re-indexing* is worse than not
merging. Both are true. Neither is evidence about a mint whose body is scoped
in `Δ = fv` and whose every occurrence carries its own δ, because no instrument
in that round could write one. §12.5's closing sentence — "the price of a
sharing the term language cannot express" — is withdrawn: the term language
expresses it as `u^δ`, which is ch. 04 syntax the kernel already unfolds
lazily and glues, and §2 is the price.

---

## 4. The mint

The shape the measurement licenses. Nothing here is built; this is what the
implementation pass takes.

**`Δ` is the value's free variables, in level order, closed up.** For a chosen
node, `Δ` holds the ambient Γ entries and the fresh neutrals its body actually
reads, each with its own type — and an entry's type is itself a value the
readback spells, so it may itself be named. A mint's `Δ` may therefore
reference mints below it, which is the same nesting §12.7's
`strengthen_global(body, mint_cap − j)` already arranges: a mint is scoped in
`Ψ ++ mints[0..j]` at mint time. The types come off the **values** the walk
already opened (the closure's own binder types), not off `slots_tm`/`slots_ty`'s
`Scope` table, which is what §12.1's second condition needed and what §12.6's
seven refusals were attributed to.

**The reference is `u^δ`, and δ is per-occurrence.** This is the whole
mechanism and the one thing §12.5's merge mode did not do. The body is scoped
in `Δ` and nothing else, so one body serves every occurrence; what differs
between occurrences is δ, which supplies each chain's variables at their
indices *there*. A reference costs `1 + |fv|` nodes and carries no annotations,
unlike an application. A substitution **tail** inside a named body is not a
dependency: `rbemit.rs`'s `subst` writes `δ̂ = d` because a value drops the
ambient length (`value.rs`'s `VTail`), and in a mint that length is `|Δ|`,
which re-scoping supplies for free — measured, in that `basevar = 0` and
`opaque = 0` leave no case where it does not.

**The Ψ-entry arithmetic does not change.** §11.4's reserve / allocate through
`&self` / realize at commit on the goal arena, and §12.7's block arithmetic —
the mint block below the goal block, `allocate`'s `goal_base − 1 − k` and
`strengthen_global(solution, goal_base)` unchanged, `global_abs_of`,
`gen_ref`, `gen_def_of`, `resolve` and `refresh_delta_psi` taking the *total*
padding, `semantic_oracle` seeing the minted bodies — are stated for *a* `Δ`
and say nothing about which. A smaller `Δ` is a smaller `ctx` on the same
`GlobalBinding::Tm`. A mint that overflows the reserved block declines and the
component stays inline, which is stage one's behaviour and always safe.

**Typing** keeps §12.6's route: kernel syntax is fully annotated, so
`typing::infer_term` gives the statement and the readback supplies only `Δ`.
§12.6's control stands — `HEATHER_RB_CHECK=1` typed the readback's own answer
on 6 627 of 6 627 roots — so the refusals there were about `Δ`, and this pass
changes where `Δ` comes from. Whether the refusal rate falls is the first
measurement the implementation pass owes.

**The readers audit is §6's, unchanged and undischarged.** A mint is a new Ψ
binding, so: the `tag_of`/`spine`/`decoded` triple, `unspell_here` and
`unspell_sum_components`, `emit_ty` and `respell_ty_deep_in` seeing *through* a
minted name as they see through `D#payloadₖ`, `emission_walk`'s slot list, the
image codec and `ModuleDelta`'s dependency identity for a binding that is not
keyed by a declaration tag, `docs/cache-v1-design.md` §4's cache identity, and
`WALK_RESIDUE` shrinking only. Stage one's fourteen small `list::*` rows
(§11.3) are inherited debt, not new.

---

## 5. Rejected shapes, with reasons

- **A minimal Δ over the innermost `k` entries** (§12.5). Measured there at
  6 %, and §3 says why: it is this rule read one level too shallow, shrinking
  the context of a name that is still one per depth. Superseded, not refused.
- **Merging occurrences without re-indexing** (`HEATHER_RB_MERGE`, §12.5).
  Refuted there, still refuted, and §4's second paragraph is the difference.
- **Naming the closure and applying it to the fresh neutral** (a λ-lifted
  mint), the fallback the brief named for a failing reading. Not needed: with
  `bad = 0` there is no occurrence whose chain lacks a variable the body
  reads, so there is nothing for the extra abstraction to supply. It also
  costs an `App`'s two type annotations per use where `u^δ` costs none, which
  is the reference-cost column.
- **Naming shared *types* through a code** (§12.1 item 1, §12.4). Still worth
  about 2 %, still cheap and idiomatic (`code.rs`'s `code_of` *is* `⌜T⌝` and
  `code_of(El t) = t` reads a named child straight through), still not what
  the round was short of. Independent of `Δ = fv` and can land separately.
- **A threshold other than 64**, re-asked on the split graph: T = 16 names
  30–39 and is within 0.3 % of T = 64's emitted count, T = 0 is 0.8–1.4 %
  worse, T = 1 024 is 4–5 % worse. §11.2's unit survives its third asking and
  T = 16 is a tie, not an improvement.
- **Anything that changes `rbcount.rs`'s own memo to the merged keying.**
  §3: it merges sharing no emitter can spend, and §11.2's 80 477 is that
  memo's number rather than the object's.

---

## 6. Verification items for the implementer's first hour

Stop and report if any of these fires.

1. **The instrument's checks before anything is built**
   (`probes/nv_table.sh`): `naive` in split keying equal to §12.3's column on
   all four rows, `naive`/`graph` in depth keying equal to §11.1's,
   `closed = 7` on `complete_post`, `opaque = basevar = decl = 0`. If `naive`
   in split keying is not §12.3's, the walk and the emitter have drifted apart
   and §2's table is not about the object the emitter writes.
2. **`bad` must be 0.** One threshold-clearing shared value reached under a
   chain missing a free variable is the reading failing, and §4's `Δ` is wrong
   before any of it is built. `badc` (the same test in the merged keying,
   restricted to values with no contaminated ancestor) must also stay 0.
3. **The per-layer ratio, not the count.** ×2.47 / **×1.31**, and
   `qt_deep / qt_pure` at ×3.23. A landed device at ×2.5 on the *second*
   ratio is §12.3 again with smaller constants, whatever its absolute number.
4. **The absolute sub-bars**: `complete_post` ≤ ~90 k emitted, `qt_deep`
   ≤ ~115 k, and 20–35 mints per reduct. An emitted count near 700 k is the
   per-depth device; near 1.3 M is the merge.
5. **`|Δ| ≤ 5`, mean ≈ 2.5.** A mint whose context is the size of Γ means the
   device is scoping in the chain again rather than in the value.
6. **`HEATHER_RB_TYPE=1` must refuse fewer than §12.6's 7 of 19**, and every
   refusal must remain a decline rather than an error.
7. **Every landing gate of §8 and §12.7**: the full `scripts/test`, the x86
   rails at two sizes per item, `WALK_RESIDUE` shrinking only, the bench
   `--save`/apply/`--check` dance, the image and dependency identity, and the
   per-item join over the showcase's 944 rows — which stage one already fails
   on fourteen `list::*` rows and which this device inherits.

---

## 7. Status

Design, with a measured instrument and **no** implementation. The mint of §4
is not built; §12's device stays inert behind `HEATHER_RB=name`; the
instrument is `crates/elab/src/rbcount.rs`'s `HEATHER_RB=fv` mode and is
**inert** with `HEATHER_RB` unset, with `HEATHER_RB=count`'s line unchanged so
§11.1's and §12.3's runs are still reproducible from this tree. No commit, no
fixture moved, no issue edited. `probes/nv_table.sh` and
`probes/nv_showcase.sh` are the two jobs. `scripts/test --fast -p heather-elab`
is `== suite: 1971 passed, 0 failed, 5 ignored ==`; the full suite was not run,
because the pass adds no test and nothing on the default path moved — the
control that says so is `HEATHER_RB=count`'s line, which still reads §11.2's
`qt_pure` row (40 names / 34 681) on this tree.

`issues/elab-emits-normal-form-of-matched-type-argument` keeps its charter and
its mechanism is now named to the end: the fix is a spelling with names in it;
a name whose Δ is every binder above it is one name per depth and grows
(§12.3); a name whose Δ is **what its body actually reads** is one name per
value, and the emitted count then follows the value graph's curve. What the
implementation pass owes is the device, its typing, and §6's audit — not
another measurement of the unit.
