# probes/ — untracked scratch for the K1 design pass

Hand-measurement inputs for `docs/native-bitvector-values-design.md`.
Nothing here is part of the build or the suite; the directory is untracked.

## Re-measuring the probe table (§2 of the design doc)

**A fresh `--cache-dir` is mandatory.** The declaration cache is keyed on the
*proof obligation term*, not on the item's name or the file's bytes, so a
second run of the same theorem — even renamed, even in a file with a changed
comment — is answered from cache and reports zero kernel time and zero
evaluator steps. That is how a first measurement silently becomes a table of
zeros. Always point `--cache-dir` at a directory you just removed.

One furnace job, all six files in one process (about three seconds warm):

```
furnace run -- bash -c 'rm -rf /tmp/pc1;
  (ulimit -v 6291456 -t 900;
   HEATHER_TIMINGS=- target/release/heather check --cache --cache-dir /tmp/pc1 \
     -L lib/std -L lib probes/t_*.hthr 2>&1 | grep -E "^item\tt_")'
```

Columns of interest in the TSV (1-based, as `cut -f` counts): 4 `total_ns`,
8 `kernel_gate_ns`, 41 `conv_shortcut_hits`, 43 `conv_misses`, 46
`eval_steps`, 47 `eval_delta_steps`.

## The before column (§1)

```
furnace run -- bash -c '(ulimit -v 8388608 -t 1800;
  HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
    examples/x86-native/reused_callee.hthr caller --callee leaf \
    --arg 21 --arg 1 -o /tmp/k1/caller --cache-dir target/native-test-images \
    --kernel-workers 1 --timings /tmp/k1/t.tsv)'
furnace run -- python3 probes/agg.py /tmp/k1/t.tsv
```

`agg.py` groups item rows into families and prints the run totals. The binary
must be `cargo build --release -p heather-cli --features value-metrics`.

**Use a fresh `--cache-dir` for a before/after pair, not the warm
`target/native-test-images`** (learned 2026-09-13, round 2). The warm images
directory is populated by whatever ran last, and a run against it reported
**3 476** item rows while the same command against an empty directory
reported **5 001** — so a before taken warm and an after taken after a
rebuild are not the same measurement, and the difference is larger than any
effect worth measuring. `probes/measure.sh` is the cold recipe: it removes
its cache directory, runs the workload under the ulimit, and prints
`agg.py`. Run it once on the pre-change tree (`git stash`) and once on the
post-change tree, back to back on the same instance. A cold run is ~100 s.

Note also which column is which: in the `--timings` TSV, field 4 is
`total_ns` and field **8** is `kernel_gate_ns`. Field 5 is not the gate.
Serialize furnace jobs: a second launch's sync clobbers the first's outputs.

## Files

- `t_a1_lib_xor.hthr` — `bitvec::bxor` on literals, widths 8/16/32/64.
- `t_a2_raw_xor.hthr` — the same fold over `[Bool; n]`, wrappers inlined by
  hand: what a library respelling alone would buy.
- `t_a3_literal.hthr` — no operation at all, just a literal against itself:
  the Σ-η conversion floor.
- `t_a4_lib_add.hthr` — `bitvec::add`, the carry-threading shape.
- `t_c1_tonat.hthr` — `toNat` of a literal, the consumer into `Nat`.
- `t_c2_is_zero.hthr` — `is_zero_bits(bxor(a, b))`, the certificate's unit,
  equal and differing operands and a zero literal.
- `agg.py` — family aggregation for a `--timings` TSV.

## Running `scripts/bench --check` on furnace

The remote checkout is an rsync'd tree, **not a git repository** — `git diff`
there fails with "Not a git repository", so the `--save`-before /
apply / `--check` dance cannot use git remotely. It also has to happen inside
**one** `furnace run`: the baseline `--save` writes stays on the remote, and
the next run's sync restores the committed `baseline.tsv` over it.

What works: write the working diff to `probes/k1.patch` locally (the
directory syncs), then one job that copies the new untracked files aside,
`patch -p1 -R --batch < probes/k1.patch`, `scripts/bench --save`, re-applies
with `patch -p1 --batch`, restores the new files, and runs
`scripts/bench --check`. Round 2 got `ok: 112 comparisons within
thresholds` this way. Nothing lands in the repo, so there is no baseline to
`git checkout` afterwards.

## Round 4 files (K1, `docs/bitvector-literal-entry-design.md`)

- `t_p2_lit_split.hthr` — P2. `p2_def_n` is the literal in a *definition*
  (elaboration + kernel check, no conversion); `p2_lit_n`/`p2_rec_n` add one
  Vec/Vec Sigma-eta. Subtract `p2_def_n` to see what packing costs.
  A bare `[a, b] = [a, b]` in a theorem's type parses as a vector TYPE —
  hence the `vid` wrapper.
- `t_p3_ofnat.hthr` — P3. `ofNat(n, k)` against the same value as a
  `from_bits` literal, with the literal-against-itself control.
- `t_p3b_ofnat_parts.hthr` — which suspect in `ofNat` costs: the truncation,
  the powers list, the width. (`list::length` is spelled `list_len`.)
- `t_p3c_ofnat_halves.hthr` — the respelling: `ofNatH`, low bit by parity and
  the rest at `nat::half`. 5.7x at width 64. The design's recommendation.
- `t_p4_mov_imm64.hthr` — P4. `canonical_bytes(MovRI(R9, imm))` three ways.
  Needs `model.hthr` copied under its harness name; the scripts do
  `cp lib/std/arch/x86_64/model.hthr /tmp/archL/x86_64.hthr` and add
  `-L /tmp/archL`.
- `t_p4b_mov_half.hthr` — P4 with every `ofNat` replaced by `ofNatH`.
- `t_p5_born.hthr` — the same value born packed (`all_ones`/`zero`, which the
  round-3 class produces as a `BitRun`) against the same value written out.
- `r4p1.sh` … `r4p6.sh` — one furnace round trip each. `r4p5.sh` is the cold
  whole-workload run.

**Seconds and steps move in opposite directions on `ofNat`** (design 1.5):
gate `-67%` while `eval_steps` `+3x`. Gate on `kernel_gate_ns`, field 8.

## A library before/after pair needs two BUILDS, not two file swaps

`crates/cli/src/native.rs` bundles every `lib/std/*.hthr` with `include_str!`,
and `build-x86` refuses a source library that differs from the bundled one
(`error: source module 'bitvec' differs from the compiler's bundled proof
library`). So a whole-workload before/after over a *library* change is: swap
the file in, **rebuild**, run cold; swap the other file in, rebuild, run cold —
`probes/s1b.sh` is that shape, with `probes/bitvec_before.hthr` and
`probes/bitvec_after.hthr` as the two columns. `heather check -L lib/std …`
does not compare, so the probe files need no rebuild.

For a *kernel* change the columns are `patch -p1 -R` / `patch -p1` around
`probes/step2.patch` with a build each side, all inside one job
(`probes/s2.sh`) — the same dance the bench section describes.

## `probes/step2.patch` — the `Nat`-state transducer arm (round 4, step 2)

Built, tested and **refused on cost** (design §10.7): `+1.0 %` of the whole
workload's kernel gate against the step-1-only column, cold, one job. Kept
here rather than discarded; `git apply probes/step2.patch` restores it,
including the `DESIGN.md` clause and the four axis tests in
`eval/transduce.rs` (all 16 tests in that module pass with it applied).
The patch charges one fuel unit per bit in `fire_nat_state`; the version
measured did, and the version here does not — the loop performs the fold's
own step applications, which charge themselves, so charging again could
refuse on fuel what the structural path paid for. That difference is fuel
accounting only and does not move the measurement.

`probes/s2.sh` is the before/after recipe for it; `probes/s2bench.sh` is the
`--save` / apply / `--check` dance, which was not needed since the change did
not land.

## Round: telescoped dependent record projections (2026-09-15, pass 2)

`p2_*.sh` are this round's furnace scripts; `probes/p2_base/` holds pristine
copies of the parent (HEAD) versions of every changed `crates/` file, which is
what the `scripts/bench --save` / apply / `--check` dance and the
parent-vs-changed controls swap in and out (the remote checkout is not a git
repository — see the bench section above).

- `p2_parent.sh` — build the **parent** binary once and park it at
  `target/heather_parent`, then restore and rebuild the changed tree. Run this
  first on a fresh instance; `target/` persists between jobs and every
  before/after table then runs both binaries in one job on one box.
- `p2_table.sh` — the round's bar: reproducers (`t_pc1`…`t_pc4`, `t_pcev3`,
  `t_pcr3`), the showcase at `--kernel-workers 1`, the head-pair table and the
  default gate width, each for both binaries. `TAG=` names the output
  directory. **A fresh `--cache-dir` per probe file**, because the declaration
  cache is keyed on the obligation term and two probe files declare the same
  records — sharing one directory zeroes the declaration items.
- `p2_listing.sh` — `HEATHER_GENDEF_DECLINES=1` on `t_pc1` and the showcase,
  grouped by (site, declaration, reason). No `--cache`: a replayed image skips
  elaboration and prints nothing.
- `p2_round2.sh` — `p2_table.sh` then `p2_listing.sh` in one job.
- `p2_gate.sh` — the per-module split of the showcase's seconds, a conv-miss
  trace, then `scripts/bench --save` on the parent / `--check` on the change /
  full `scripts/test`, all in one job.
- `p2_fails.sh`, `p2_diag2.sh` — the full suite with the failure **names** and
  the per-test panic blocks; `scripts/test | tail -N` drops both.

**The head-pair table is printed once per module.** Summing the blocks is the
run's table; `grep … | head` samples one module and misranks the rows.

## Round: complete_post attribution (2026-09-16, `docs/complete-post-attribution-design.md`)

Six furnace round trips, in order; `cp_*.sh` are the scripts and `t_cp*.hthr`
the reproducers. Every script ends with `== MARKER done` and prints what it
wants read, because the remote output directories (`probes/out_cp*`) are not
synced back.

- `cp_premise.sh` — job 1, the premise check. The showcase at
  `--kernel-workers 1`, **untraced** and with no `--cache`, `--timings` to a
  file; prints the TSV header with 1-based indices, `complete_post`'s whole row
  as `name = value`, every item row of the parser modules, the run's top items,
  the module rows and the run row. Read this before any trace: a traced run
  inflates the item's `total_ns` about 2.6×.
- `cp_trace.sh` — job 2, the trace read. `HEATHER_CONV_MISS_TRACE=complete_post`
  with `HEATHER_VALUE_METRICS=1`, then four views of the same 110 851 records:
  `trace_agg.py`'s head-pair and group tables, **whole records bucketed by the
  `expected len=… inferred len=… first difference at …` signature** (the
  `s4_excerpt.sh` read — `trace_agg` truncates at 260 characters and hides the
  excerpt), the `site:` lines crossed with the head pair, and the **sum of the
  traced misses' milliseconds**. That sum against the item's kernel gate is the
  round's first finding and the reason the script exists: the misses are under
  half of it.
- `cp_repro.sh` — job 3, the reproducer table (`t_cp1` … `t_cp6`).
- `cp_spec.sh` — job 4, decomposing the spec (`t_cp7` … `t_cp10`).
- `cp_and.sh` — job 5, the `And` isolated (`t_cp11` … `t_cp14`).
- `cp_declines.sh` — jobs 6 and 7 in one trip: `HEATHER_GENDEF_DECLINES=1` on
  `t_cp1` and `t_cp2` grouped by (site, declaration, reason) **and by the
  listing's fifth field**, the declaration scope — which is how the round found
  that neither listing charges a single row to the probe's own theorem — then
  the `CONV_MISS_TRACE` head pairs of the two single-component variants.
- `cp_eqty.sh` — job 8, the equation's element type (`t_cp15`, `t_cp16`).
- `cp_slot.sh` — job 9, what the argument slot charges for (`t_cp17`, `t_cp18`).
- `cp_record.sh` — job 10, the record respelling (`t_cp19`).

**No `--cache` anywhere in this round.** Every probe file pays the library
prefix afresh (~37 s of the ~40–56 s wall) and the prefix is subtracted by
reading the item rows out of `--timings`, never the wall. That is deliberate:
the declaration cache is keyed on the proof obligation term, nineteen variants
of one statement are exactly the population where "are these two obligations
the same term?" is the question one does not want to be answering by accident,
and 37 s per file is cheaper than one silently zeroed row. Every run also
re-elaborates `parser_primitives::complete_post` itself, so each of the ten
jobs carries the library item as its own control on the same box: it reads
15.5–16.1 s of kernel gate and 110 851 misses in all of them.

The files, in the order the design's §3 table lists them:

- `t_cp1` — the base: `complete_post`'s statement and proof verbatim under a
  new name. Reproduces the library item **to the unit** (110 851 misses,
  5 726 206 conversion-shortcut hits, 7 675 169 evaluator steps).
- `t_cp2` — `CompleteSpec` replaced by the plain `relation`; `t_cp3` — the
  `eof_at`/`map_at` continuation replaced by `pure_at`; `t_cp4` — the floor,
  no combinator in the conclusion.
- `t_cp5` — the base with `T`/`A` closed; `t_cp6` — with `relation` a named
  declaration instead of a parameter. Both are negative results.
- `t_cp7` — `CompleteSpec` re-declared in the probe file (the control for what
  follows); `t_cp8` the equation conjunct alone, `t_cp9` `And<relation,True>`,
  `t_cp10` the relation applied and wrapped in a `→ Type` of its own.
- `t_cp11` `And<True,True>`, `t_cp12` `And<True,equation>`, `t_cp13` `And`
  replaced by a file-local two-field record, `t_cp14` `And` nested one deeper
  over closed leaves.
- `t_cp15`/`t_cp16` — the equation moved from `List<T>` to `Nat`.
- `t_cp17` — the smallest binder-dependent argument, `nat::Le` of two cursor
  offsets; `t_cp18` — the same argument twice.
- `t_cp19` — the two conjuncts moved out of type-argument slots and into the
  **field types** of a telescoped dependent record with value parameters only.

**Read the table by counts, not by seconds.** Across the whole family the
kernel gate is 2.46–2.95 µs per conversion query at every size from 3 840
queries to 7.8 M, so `kernel_gate_ns` carries no information that
`conv_shortcut_hits` does not; what a variant changes is how many nodes the
kernel is handed.

## Round: quote the respelled type (2026-09-16, `docs/complete-post-attribution-design.md` §10)

Five furnace jobs, in order; one job at a time, and **every job's whole output
redirected to a local file** — job 1's log was read through `tail -200` and
the tables above the record dumps were lost, which cost a round trip.

- `cp_park.sh` — job 1, before any `crates/` edit: copy `target/release/heather`
  (HEAD, value-metrics) to `target/heather_parent`, then read `t_cp1`'s trace.
  The parked binary is the parent column everywhere below; the remote checkout
  is an rsync and not a git repository, so there is no other way to get one.
- `cp_spike.sh` — job 2, §8 item 1. The trace tables again from the parked
  parent, then the change built and run with `HEATHER_QUOTE_SPIKE=1`: one line
  per `quote_type_at` call saying whether `emit_ty` respelled it and by how
  much. 30 of 121 calls on `t_cp1`. The spike's STOP condition did not fire.
- `cp_slice.sh` — job 3, the bar: `t_cp1/2/9/12/17/18` both binaries, the
  showcase serial and at the default width, the whole summed head-pair table
  both sides with the rows that rose, and the decline listing.
- `cp_rise.sh` — job 4, the four head-pair rows that rose, attributed to the
  items that carry them (the report prints `item … count=` lines under each
  bucket; summing them across the per-module blocks is the attribution).
- `cp_gate.sh` — job 5, detached: the per-**item** diff of the showcase (no
  item's misses, queries or steps may rise), the full `scripts/test`, and the
  `--save` / apply / `--check` bench dance. `probes/cp.patch` is the diff the
  dance reverse-applies; `probes/cp_base/` holds the pristine parent copy of
  every `crates/` file the round touched.
- `cp_bench.sh` — the bench dance alone, for re-running it without the suite.
- `cp_final.sh` — job 6: the tree left for review (the spike's `eprintln!`
  removed) re-verified on its own — the showcase serial row and the full
  `scripts/test`, so the suite that passed and the tree that ships are one.

**`--fast` is not a lane for this round**: the change is in what the frontend
emits, and the fast lane replays module images an earlier build wrote.

## Round: where the conversion queries come from (2026-09-16, `docs/conversion-query-traversal-design.md`)

Four furnace jobs, in order, one at a time; `qt_*.sh` are the scripts,
`t_qt*.hthr` the new reproducers and `qt_agg.py` the aggregator. Every script
ends with `== MARKER done` and prints what it wants read — `probes/out_qt*`
is not synced back.

- `qt_trace.sh` — job 1, the instrument and its **sanity check**. Builds
  release with `value-metrics`, then runs `t_cp1/t_cp2/t_cp17/t_cp12/t_cp9`
  under `HEATHER_CONV_QUERY_TRACE=<item>:128`. The first thing to read in the
  log is `samples × 128` against the item's `conv_shortcut_hits` column: the
  round's five probes agree to within 0.03 %, and if that line disagrees the
  instrument is wrong and nothing else in the log may be attributed.
- `qt_probe.sh` — job 2, the multiplier. The trace deepened to 40 site frames
  (job 1's stacks were 100 % at the 12-frame cap, so the spine length was
  unread) and carrying the **address** of the type compared; then `t_qt1`,
  `t_qt2`, `t_qt3` — `t_cp9`'s component with the enclosing reply shortened to
  one combinator, to none, and lengthened by one identity `map_at` — with
  `t_cp9`, `t_cp2`, `t_cp1` as controls and `close_body` traced out of the
  showcase.
- `qt_scale.sh` — job 3, the two factors separated. The same family
  **untraced**, whole TSV row per item: the point is that `decl_emit_ns` and
  maxrss scale with `conv_shortcut_hits`, which is what rules out "the kernel
  is re-walking a shared term" and rules in "the elaborator wrote one that
  big". Also the SHAPE tables (site runs collapsed) for `t_cp1` and
  `close_body`.
- `qt_curve.sh` — job 4: `t_qt4` (the reply named — a negative, 0.13 %),
  `t_cp3`/`t_cp4` re-measured on the post-slice binary, `t_qt5` (five
  combinator layers, 29.4 M queries, 9.5 GB — run it under a 32 GiB rail, not
  the probe default), then `scripts/test --fast`.

**Read `qt_agg.py`'s tables by count, in queries.** Every count it prints is
already multiplied back by the stride. The three views that carried this
round: *by rule frame* (the answer — 96.5 % `App`, 3.2 % code formation),
*by site SHAPE with runs collapsed* (`App×22 < Pair×12 < Snd×2 < Fst×2 < App`;
the uncollapsed table is 6 000 keys of `App < App < App …` and says nothing),
and *the address histogram* (one `Ty 0` object standing for 17 % of an item's
queries).

**The identity `map_at` is the instrument, not a shape anyone would write.**
`t_qt3` and `t_qt5` add `map_at(source,middle, INNER, λ (i: Nat) => i)` layers
that compute nothing and change no type; each one multiplies the whole item by
≈3.5×, in queries, in emission, in the elaborator's whnf clock and in resident
memory. That is the round's finding and it is why the curve needs five points
and not two.

## Round: emit the application, not its normal form (2026-09-16, implementation pass of `docs/conversion-query-traversal-design.md`)

Four furnace jobs, in order, one at a time. The round **stopped at the spike**
(design §8 item 2, §10.3), so there is no changed binary and no before/after
table: `crates/` is `d53ec73` and the instrument lives in `probes/nf_spike.patch`.

- `nf_spike.sh` — job 1, design §8 item 1: park `target/release/heather` at
  `target/heather_parent`, then `t_qt2`/`t_cp9`/`t_qt3`/`t_qt5` untraced, whole
  TSV row each. Three points before anything is touched; §10.1 is its table.
  `t_qt5` needs a 32 GiB rail (9.54 GB resident, 130 s wall).
- `nf_site.sh` — job 2, the spike itself. Superseded by `nf_site2.sh`: its
  inline `awk` keyed the grouping on the wrong field and its record dump cut
  the site off the end of the line. Kept as the shape of the first attempt.
- `nf_site2.sh` — job 2b, the same run read through `probes/nf_agg.py`.
- `nf_site3.sh` — job 3, **the table that named the site**: the spike applied to
  the curve (`t_qt2`/`t_cp9`/`t_qt3`) at a 20 µs budget, aggregated per item.
  Two calls carry the whole exponent; `matching::expose` does not.
- `nf_site4.sh` — job 4, `in_len` beside `out_len` and the input's whole
  bounded spelling, for the "is the pre-whnf term in hand" half.
- `nf_agg.py` — the aggregator: records over a floor, grouped by (what, item,
  site) with count/total/worst, then the costliest records with both lengths.
- `nf_spike.patch` — the instrument. `git apply probes/nf_spike.patch`, build
  with `--features value-metrics`, run with `HEATHER_NF_SPIKE=<µs>`.
- `nf_base/` — pristine `d53ec73` copies of the two files the patch touches.

**`--timings` or no attribution.** The declaration scopes the spike's `item=`
column reads (`crates/elab/src/stats.rs`'s `ITEMS`) are only maintained while
the elaborator is collecting rows, which is what `--timings` turns on. Job 2b
ran without it and attributed all 165 records to `-`; that cost a round trip.

**The bounded `Debug` saturates at ~2 330 characters** (512 nodes,
`crates/kernel/src/fmt.rs`), so `in_len`/`out_len` separate "small" from "big"
and nothing beyond. The size proxy that does scale is the **clock**: `whnf`
builds the reduct and `emit_ty` walks every node of it, and both track the
3.5× per combinator layer.

## Round: the projected tuple tower (2026-09-16, design pass + spike for `docs/projected-tuple-tower-design.md`)

Two furnace jobs, in order, one at a time. The round's product is the doc; the
spike (candidate D) is measured and **declined**, so `crates/` is back at
`d59f477` and the change lives in `probes/tt_D.patch`.

- `tt_count.sh` — job 1: park `target/release/heather` at
  `target/heather_parent`, build the spike, and run the **node-count
  instrument** (`HEATHER_TT=count`) over `t_qt2`/`t_qt1`/`t_cp9`/`t_qt3`, then
  a `HEATHER_TT=fire` smoke test against the parent on two files. The counter
  is exhaustive and unbudgeted, which is what the bounded `Debug` and the
  clocks are not.
- `tt_slice.sh` — job 2: candidate D end to end. The curve
  (`t_qt2`/`t_qt1`/`t_cp9`/`t_qt3`/`t_qt4`/`t_cp1`/`t_cp18`/`t_qt5`), the
  fifth count point (`t_qt5` under the instrument, 32 GiB rail), the showcase
  serial and at the default width, the 944-row per-item join, and the whole
  summed head-pair table. One binary, two behaviours: `HEATHER_TT` unset is
  the parent's code path (the parked binary is the control that says so),
  `fire` is D.
- `tt_D.patch` (`tt_count.patch` is the same file, since the instrument and
  the spike are the same module under two `HEATHER_TT` values) — one module
  (`crates/elab/src/ttsimp.rs`) plus `mod ttsimp;` and one call in
  `build_ctor`. `git apply probes/tt_D.patch`, build with
  `--features value-metrics`, then pick with `HEATHER_TT=count|fire`. Inert
  when unset.
- `tt_fast.sh` — job 3: `patch -p1` the spike onto the remote checkout (which
  is an rsync, not a git repo) and run `scripts/test --fast -p heather-elab`
  on it, so the declined patch's suite state is on record: 1961 passed.
- `tt_base/` — pristine `d59f477` copies of the two files the patch touches.

**Read the instrument's lines by the item's own reduct, not by the sum.** Every
run re-elaborates the library, so `parser_primitives::complete_post`'s
2 634 824 → 1 586 711 node record appears in all of them; the probe's own item
is the row that moves with the curve. The summed line is a sanity check on the
redex counts (`proj`/`beta`/`case` must all reach 0), not a measurement.

**The counter is a tree count.** That is the round's whole point: the reduct is
exponential as a tree and linear as a graph, so a count that shared would have
measured the wrong thing.

## Round: the `close_body` family (2026-09-16, design pass for `docs/close-body-family-attribution-design.md`)

Two furnace jobs, in order, one at a time. The round's product is the doc; the
only source change is the node counter, which is reverted (`cb_count.patch`,
pristine originals in `cb_base/`).

- `cb_trace.sh` — job 1: the premise (the showcase serial with `--timings`)
  and `HEATHER_CONV_QUERY_TRACE` for `close_body`, `expr_body`, `Grammar`,
  `Certified` and `number_grammar`, each its own process, aggregated by
  `qt_agg.py` (frame table, head pairs, collapsed site shapes, addresses).
- `cb_count.sh` — job 2: the reproducers (`t_cb1`…`t_cb6`, plus the existing
  `t_pc3`/`t_pcr3`) and the **node counter** `HEATHER_CB=1` over the showcase
  and four of the probes, aggregated by `cb_agg.py`.
- `cb_decline.sh` — job 3: `HEATHER_GENDEF_DECLINES=1` over the showcase and
  three probes (why each dear field read took the fallback walk), then the
  probes' own node counts (`cb_agg.py … all`, since a probe's items are named
  after its fns and the default filter is the showcase's family).
- `cb_count.patch` — the instrument, self-contained (it carries
  `ttsimp.rs` from `tt_count.patch` plus a `count_tm`, so apply this one
  alone: `git apply probes/cb_count.patch`, build with
  `--features value-metrics`, run with `HEATHER_CB=1`). Two print sites: the
  emitted `(statement, term)` pair per declaration in `lib.rs`, and one line
  per record field read in `project_field`, with its route (`ref` = the named
  projection, `walk` = the `Fst`/`Snd` fallback). `cb_base/` holds the
  pristine `be365f3` copies of the two tracked files it touches.
  **`cb_agg.py` keys `cb decl` lines by name and keeps the last**, so an item
  that emits more than one pair (a `decreases` lowering) is under-counted;
  `checked_expr` is the visible case.
- `t_cb1`…`t_cb6` — `close_body`'s shape on the real library `Certified`:
  three chained receivers (`t_cb1`), two (`t_cb2`), one (`t_cb3`), the same
  three without `result::fold` (`t_cb4`), with a relation that ignores its
  cursors (`t_cb5`), and on `Success` instead of `Certified` — the record
  whose parameters are all value-typed (`t_cb6`).

**The item filter is the BARE item name.** `--timings` writes the module in
column 2 and the item in column 3, and both `HEATHER_CONV_QUERY_TRACE` and
the elaborator's own scopes compare against column 3: `close_body`, never
`calc_parser::close_body`. The `module::item` spelling the docs' tables print
traces nothing, prints no error, and costs a round trip.

## Round: the matcher sees through a quote (2026-09-16, implementation of `docs/instance-match-quote-arm-design.md`)

Slice 1 of `docs/close-body-family-attribution-design.md` §7.3. Three furnace
jobs, in order, one at a time. The change is two arms in `Holes::ty`'s
former-mismatch arm (`crates/elab/src/gendefs.rs`) plus the flipped pinned
negative and one new axis test in `crates/elab/src/wf.rs`; `probes/ia.patch` is
the whole diff and `probes/ia_base/` the pristine `1a91fc1` copies.

- `ia_spell.sh` — job 1: park `target/release/heather` at
  `target/heather_parent`, build the **spelling instrument**
  (`probes/ia_spell.patch`) and print, at each of `Holes::ty`'s and
  `Holes::tm`'s former-mismatch arms and at `place_ty`'s disagree arm, the two
  sides in bounded `Debug`. `HEATHER_IA_SPELL=1` for every declaration.
- `ia_spell2.sh` — job 1b, and the one that reads: `HEATHER_IA_SPELL=<decl>`
  filtered to one declaration, plus the `ROOT` lines (the whole template and
  the whole subject at the point `instance_match` gives up). Job 1's 4 000-line
  cap was eaten by `List`'s 27 881 declines before `Certified`'s five were
  reached.
- `ia_slice.sh` — job 2, the bar: the flipped unit tests, the curve
  (`t_cb3`/`t_cb2`/`t_cb1`, `t_pcr3`'s `qchain1..3`, the two new reproducers),
  the showcase serial and at the default width with the family named, the
  959-row per-item join, the whole summed head-pair table with the rows that
  rose, and the decline listing — parent (`target/heather_parent`) against the
  change (`target/heather_ia`).
- `ia_gate.sh` — job 3, detached: the route split under
  `probes/cb_count.patch` (re-applied as an instrument and reverted after),
  the x86 rails inside the **default** fuel, the full `scripts/test`, and the
  `--save`/apply/`--check` bench dance.
- `ia_walk.sh` — job 4: the one assertion the first full suite failed on. The
  new axis test asserted an **empty** emission walker; this prints what it
  actually finds (eight `App` `dom`/`cod` slots carrying the boxed
  `El[0](«Nat»)` literal — the quote layer's standing residue,
  `issues/emission-walker-residual-sites`), which is why the assertion is now
  "`«Nat»` is the only quote in any finding" plus a named-argument control.
- `ia_final.sh` — job 5: the final verification, the plain full `scripts/test`.
- `t_ia1.hthr` / `t_ia3.hthr` — one reproducer per arm, ≤ 20 lines: a
  `Certified<ATok,Nat>` read that declines with `identity-match-El/Nat`, and a
  `Result<Certified…,Failure…>` through `result::fold` that carries the
  `hole-match-Sigma/El` and `hole-match-Sum/Sigma` rows.

**The decline listing's large rows are the matcher being *asked*.** `List
hole-match-Wf/Sigma` is 27 881 on a nineteen-line probe: `instance_match` is
answering "is this type a `List<?>`" about a type that is not one, and
declining is the right answer. The rows this round is about are the ones
`project_field` pays for, and they are found by the `project_field …
instance-args` lines beside them — two on `t_ia1`, one on `t_ia3`, none for
`Result` or `Cursor`.

## Round: the sharing-preserving readback (2026-09-16, implementation pass for `docs/projected-tuple-tower-design.md` §6)

The spike (§9 items 1–3) is local, one process per file, release with
`--features value-metrics`, `--kernel-workers 1`, no `--cache`; the
parent-against-change slice is one furnace job.

- `rb_slice.sh` — the curve (`t_qt2`/`t_qt1`/`t_cp9`/`t_qt3`/`t_qt4`/`t_cp1`/
  `t_cp18`/`t_qt5`), the parked-parent control on `t_cp9`, the showcase serial
  and at the default width, the per-item join and the summed head-pair table.
  One binary, two behaviours: `HEATHER_RB` unset is the parent's code path,
  `HEATHER_RB=fire` reads `build_ctor`'s components out of the **value**.
- `crates/elab/src/rbcount.rs` (`HEATHER_RB=count`) — the spike's instrument.
  One walk over the whnf value's graph produces both columns: the **naive**
  count (the tree a readback that expands every closure would write, computed
  over the graph by memoizing `count = 1 + Σ count(children)`) and the
  **graph** count (the memo's population). It then prints, per threshold `T`,
  how many sub-values would be **named** and how many nodes the emitted
  spelling then has — `T` is the saved-node bar a shared sub-value must clear
  to be worth a Ψ definition. `codes=` is the same table restricted to values
  that are types or type *encodings*; it is the round's negative (see the
  design doc's §11).
- `crates/elab/src/rbemit.rs` (`HEATHER_RB=fire`) — the readback itself,
  stage one: value → syntax, memoized on closure identity, **no naming yet**.
  `HEATHER_RB_DIFF=1` prints the rewriter's reduct beside it (bounded
  `Debug`), `HEATHER_RB_NOFOLD=1` drops the kept-folded `El` rule so the
  policy can be measured without it.
- `rb_base/` — pristine `0245b31` copies of the two tracked files the round
  edits (`crates/elab/src/inductive.rs`, `crates/elab/src/lib.rs`).
- The `syntax=` column is the **previous** round's exhaustive syntax node
  counter (`tt_D.patch`'s `count_ty`), carried into `rbcount.rs` with its
  redex columns dropped. The declined simplifier that patch also holds is
  *not* in this tree; `tt_D.patch` still applies to it if it is wanted.

Everything is inert with `HEATHER_RB` unset — the slice's `off` side is the
parent's code path, and the parked binary is the control that says so.

## Round: the naming half of the readback (2026-09-16, step 0 of the implementation pass for `docs/projected-tuple-tower-design.md` §11.4)

The spike the brief puts before any commit-path edit: **the mints in a scratch
world, counted**. `crates/elab/src/rbname.rs` is the device — the naming, as
pure syntax, over the `Rc` graph `rbemit.rs` hands back — and
`HEATHER_RB=name` runs it at `build_ctor` and **discards** the answer, so the
item still checks against the rewriter's reduct and nothing on the commit path
moves.

- `rn_spike.sh` — job 1: §11.1's counts re-confirmed (`HEATHER_RB=count`),
  then the naming counted per reduct on `t_qt2`/`t_qt1`/`t_cp9`/`t_qt3` and
  the whole showcase, with `HEATHER_RB_TYPE=1` inferring each mint's
  statement.
- `rn_types.sh` — jobs 2 and 3 (the second after frames learned to compare
  structurally, which changed none of the counts): the two questions job 1
  raised. `HEATHER_RB_TYCODE=1`
  re-runs the *arithmetic* with shared **type** nodes counted as nameable —
  what a device that minted a type's **code** (`crates/elab/src/code.rs`'s
  `code_of`, already in the tree) and spelled the occurrence `El (u^δ)` would
  emit; and the `UNTYPED` lines say which mints `typing::infer_term` refuses,
  with their context length, node count and a bounded `Debug`.
- `rn_merge.sh` — job 4: the experiment that decides whether §11.2's price was
  ever the emitter's. `rbcount.rs` memoizes a 0-binder closure on its identity
  alone, merging its occurrences at every depth; `rbemit.rs` keys on
  `(CloId, d)`, because the readback of a closure one binder down is different
  syntax. `HEATHER_RB_MERGE=1` keys the emitter the counter's way — **unsound
  syntax**, counted and discarded, and only under `HEATHER_RB=name`. It also
  re-asks the refused mints with sixteen times the fuel.
- `rn_suite.sh` — job 5: the `T0` column asked with a big enough reserved
  block (`HEATHER_RB_CAP=4096`; the default 256 truncates it), the control
  that says whether the readback's **own** answer types
  (`HEATHER_RB_CHECK=1`), and the plain full `scripts/test`.
- Both jobs pass `--timings` so `stats::current_item()` names the item on
  every line; job 1's lines all read `item=-::-` for want of it.
- The instrument's line ends with a threshold sweep,
  `T<n>=<names>/<emitted>|ty=…|min=…`, priced on **one** walk: bare is the
  device as §11.4 describes it, `ty=` counts shared **type** nodes as nameable
  (a minted code, spelled `El (u^δ)`), `min=` additionally gives each mint the
  *minimal* Δ its body reaches into. The last two are arithmetic: the rebuild
  leaves those nodes inline.
- Everything is inert with `HEATHER_RB` unset, `rbname.rs` included: the
  default path is byte-identical to the parent's.
- `rn_base/` — pristine `a760416` copies of the four tracked files the round
  edits (`crates/elab/src/inductive.rs`, `lib.rs`, `rbcount.rs`, `rbemit.rs`);
  `crates/elab/src/rbname.rs` is new. The parked parent binary is
  `target/heather_parent`, copied on the box before the first build.

## Round: one name per value (2026-09-16, the design pass after `docs/projected-tuple-tower-design.md` §12)

`docs/name-per-value-design.md` is the product; these are its two jobs. The
instrument is one new mode on the value-graph counter — `HEATHER_RB=fv` in
`crates/elab/src/rbcount.rs` — and the **only** source change in the pass.
`HEATHER_RB=count`'s line is unchanged, so §11.1's and §12.3's runs are still
reproducible from the same tree, and everything is inert with `HEATHER_RB`
unset.

What the mode adds, per graph node: its exact **free-variable set** (the
`Head::Var` identities reachable through the value, less the ones it opened
itself), what is in scope at it on **every** path to it and on **some** path,
and the emitted count under "one mint per value, `Δ = fv`, a reference costing
`1 + |fv|`". Columns: `thr` values clearing T = 64, `bad` of those whose scope
is missing a free variable, `badc` the same restricted to values with no
contaminated ancestor, `unb`/`solo` the instrument's own self-test (a free
variable no path binds), `closed` those with `|fv| = 0`, `decl` nodes of a
class `rbemit.rs` declines, and `T<n>=<names>/<emitted>|ideal=…|flat3=…`.

Three keyings, and **the one to read is `split`**:

- `HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1` — the **emitter's** keying:
  `(CloId, d)` per sub-structure and no memo at all on an out-of-line forced
  value, which is what `rbemit.rs`'s `shared` does. The check that this is
  the emitter's graph is that `naive` reproduces §12.3's column to the unit
  (293 908 / 1 056 154 / 4 006 444 / 1 584 491).
- default (unique binder identities) — every opening takes its identity from a
  counter, so a scope test is exact rather than positional; depths alias.
- `HEATHER_RB_FVDEPTH=1` alone — §11.1's graph to the unit (332 848 / 26 043,
  1 304 352 / 61 181, 4 967 022 / 80 519, 1 957 109 / 62 058).

The difference between the first and the third is the round's own finding:
the counter memoizes an out-of-line forced value on its **address alone** and
so merges it across depths where the emitter would not, which is where the
merged graph's one-to-three cross-length shared values per reduct come from —
and hence where §11.2's 80 477 came from.

- `nv_table.sh` — job 1: the four probes (`t_qt1`/`t_cp9`/`t_qt3` plus the
  library's `complete_post`) in all three keyings. ~30–55 s per run, local,
  under `(ulimit -v 8388608 -t 1800; …)`; the counts are node counts and are
  machine-independent.
- `nv_showcase.sh` — job 2: the whole showcase in the split and depth
  keyings, summed — 8 092 reducts, 344 values clearing the threshold, `bad`
  0, 336 mints in 16 items.
- `HEATHER_RB_FVDUMP=<n>` prints the largest failing nodes with their free
  variables, the **sources** of any contamination, and the child chain down to
  where a missing identity is written (`rb fvbad` / `rb fvsrc` / `rb fvpath`).
  That is how §3 of the design doc attributed the merged keying's failures.
- Both jobs pass `--timings` so `stats::current_item()` names the item on
  every line.

## Round: one name per value — the implementation pass (2026-09-16)

The pass that was to build §4's mint and put it on the default path. It stops
in **step 0**, and `docs/name-per-value-design.md` §8 is the product; these
are its four jobs, in order. Nothing on the commit path moved, and the only
source change is three columns on the free-variable instrument
(`crates/elab/src/rbcount.rs`), inert with `HEATHER_RB` unset.

- `np0.sh` — job 0: build with `value-metrics`, park the parent binary
  (`target/heather_parent`), and re-run `nv_table.sh`'s three keyings. Note
  its `row` helper reports the **largest `naive`** line of a run, which is
  `complete_post` on every one of them — which is why job 0b exists.
- `np0b.sh` — job 0: §6 items 1–3 and 5 per item (`qt_pure`, `cp_andt`,
  `qt_deep`, `complete_post`), and the first of the new columns.
- `np0c.sh` — the four probes and the **whole showcase** with the sort split:
  `tynode=` (how many threshold-clearing values are of the value language's
  *type* sort), `TM<t>=` (§4's mint restricted to terms — the ceiling a Ψ
  `Tm` binding can reach) and `TC<t>=` (that plus §5's type-code device, a
  type occurrence charged the `El` as well).
- `np0d.sh` — the measure of sharing re-asked: `TE<t>=` prices the term-only
  rule with the saving taken over a node's multiplicity **in the tree**
  rather than its in-degree, since a type node that cannot be named passes
  its own multiplicity to the term under it.
- `np0e.sh` — the gate: `scripts/test --fast -p heather-elab`, which is what
  the design pass ran and for the same reason (nothing on the default path
  moved).
- `np0f.sh` — `tyshapes=`, the former of every threshold-clearing shared
  value of the type sort: what §5's `code_of` has to cover, now that §8 puts
  that device on the critical path.
- `np_base/` — pristine `c0d8a58` copies of the elaborator files the pass
  reads.
- A furnace job **must not** be launched while another is running: the remote
  checkout is one rsync, and the second job's sync clobbers the first's
  binary (it happened here — a run silently re-measured the previous build).
  `np0d.sh` names its own binary and prints the stray-process count for that
  reason.

## Round: one name per value — the implementation (2026-09-16, second pass)

The pass that builds `docs/name-per-value-design.md` §4's mint and puts it on
the default path, in **both spellings** (§8.3: a shared term is a Ψ term
definition referenced `u^δ`, a shared type is a Ψ term definition of its
**code** referenced `El l (u^δ)`). The device is `crates/elab/src/mint.rs`,
installed at `build_ctor` and **on by default**; every instrument of the two
design docs still runs, because the device stands down whenever `HEATHER_RB`
names one of them.

- `nm0.sh` — job 0: the brief's step 0. Build with `value-metrics`, park the
  parent binary (`target/heather_parent`, HEAD's), re-read §8.1/§8.2's
  per-item columns in the split keying, and read the **new** `tycode_no=` /
  `tycode_lost=` columns on `crates/elab/src/rbcount.rs` — step 0 item 2, of
  the threshold-clearing **type** nodes, how many `code_of` cannot quote at
  all. The test is over the whole type subtree and not the root former,
  because quoting recurses through type children.
- `nm0_agg.py` — sums the instrument's `rb fv` lines over a whole run.
- `nm_slice.sh` — job 1: parent against the device on the curve
  (`t_qt2`/`t_qt1`/`t_cp9`/`t_qt3`/`t_qt4`/`t_qt5`/`t_cp1`/`t_cp2`/`t_cp18`)
  and on the showcase, for **both stages** — the term mint alone
  (`HEATHER_RB_TERMS_ONLY=1`) and the two spellings together. It kills strays,
  refuses to run if `cp` of the fresh binary fails, smoke-tests the whole
  library under the device before spending anything on measurement, and
  prints the per-item join itself, because furnace outputs are not synced
  back.
- `nm_agg.py` / `nm_join.py` — one row per item out of a `--timings` TSV, and
  the 944-row parent-against-changed join on misses, queries and steps.
- `nm_kill.sh` — the stray-killer. A furnace job killed locally leaves its
  `heather_mint` running remotely; the next job's `cp` then fails with "Text
  file busy" and it silently re-measures the previous binary. That happened
  here, once.
- `HEATHER_RB_MINT=1` installs the device; `HEATHER_RB_T=<n>` is its
  threshold, 1 024 by default. `HEATHER_RB_MINT=1 HEATHER_RB_T=64` on `t_qt1`
  plus `HEATHER_RB_NOROOTGATE=1` (which drops §9.3's whole-answer typing gate,
  the one that declines those very items) is the one run that reproduces
  `docs/name-per-value-design.md` §9.5's two tables; `HEATHER_RB=off` on the same file is the parent column and
  `HEATHER_RB=fire` is stage one's.
- `HEATHER_RB_TERMS_ONLY=1` is the term mint alone, the first of the two
  stages.
- `HEATHER_RB_MINTS=1` prints one `rb mint` line per fired `build_ctor`: the
  naive tree, the emitted count, the graph and its shared nodes, the names
  taken in each spelling, `|Δ|`'s sum and maximum, and every decline class.
