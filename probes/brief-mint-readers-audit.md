# Brief: what may a name hide — the mint's readers audit (attribution pass, fixes only if attributed)

Repo: /home/minus/Kairos/Code/heather, branch master. HEAD is the commit that
lands the opt-in mint (`crates/elab/src/mint.rs`; `git log -1`). Tree clean
except the untracked `probes/`. Read CLAUDE.md first and obey it: scripts/test
only (never bare or filtered cargo test), never `cargo fmt`, ulimit-wrap every
heather run, match surrounding style by hand.

## Where we are

Read: `docs/name-per-value-design.md` §4, §8.3, **§9 in full** (§9.3 the
gate and its two declines, §9.4 the threshold debt, §9.5 the three failures,
§9.6); `crates/elab/src/mint.rs` (all), `rbemit.rs` (the readback and its
two spelling rules), `rbcount.rs` (`fv_report`); `crates/elab/src/dispatch/member.rs`
`record_of_at` (~270) and the `unspell_here` fallback added there;
`crates/elab/src/lib.rs` `Elaborator::whnf` (~7212, the two rules a readback
answer must respect), `unspell_here`, `unspell_sum_components`;
`crates/kernel/src/typing.rs` `infer_term`/`infer_type` and the App rule's
dom/cod checks (~700–770); `docs/closed-argument-and-parameter-domain-spelling-design.md`
§3 (the recognizers see through names — the precedent for "a reader must see
through a mint as through `D#payloadₖ`"); `probes/README.md`'s last round
section (`nm*.sh`, the two operational traps).

State: with `HEATHER_RB_MINT=1` at threshold 64 the device reaches its priced
column and the kernel columns follow (`complete_post` gate 6.58 → 1.65 s,
queries 3.70 M → 0.78 M). It does not land because three things break, and
§9.5 says they are one question — **what may a name hide from a structural
reader, and from the kernel's own conversion?**

1. **T = 64, `lib/std/relation.hthr` `compose_assoc`**: a mint hides a record
   from `dispatch/member.rs`'s `record_of_at`; an `unspell_here` fallback
   there was not enough.
2. **T = 256, the showcase calculator**: `leb(2, 2)` no longer converts
   against `leb(2, len_append(…))` (an elaborator-side conversion, or the
   kernel's? say which).
3. **`lib/std/arch/x86_64` `fetched_executes`: a kernel `NotConvertible`** —
   the emitted term is rejected at the declaration's gate. A well-typed mint
   whose *occurrence* carries the statement `infer_term` chose, where the site
   wants another. The whole-answer `infer_type` gate that turns it into a
   decline also declines `complete_post` and `qt_pure` — so the same
   spelling question is what refuses the round's own items.

## What this pass does

**Attribute each of the three to a mechanism, with a reproducer, before
fixing anything.** Then fix only what the attribution names, measure, and
stop.

1. **(3) first, because it is a kernel rejection of an elaborator-emitted
   term.** With the device on at T = 64 and the failing item isolated
   (`heather check` on the x86 model module, or the smallest probe that
   reproduces it), get the kernel's first-difference excerpt: which mint's
   occurrence, what its statement is (`infer_term`'s), what the site expects,
   and where they first differ. Hypotheses to test, not claims: (a) the mint's
   statement is a *spelling* the site's expected type does not syntactically
   match and the kernel's conversion cannot bridge within the gate (a glued
   global unfolded vs the inline lowering — then the fix is to spell the
   statement through `emit_ty`/the two whnf rules, the same obligation every
   emitter discharges); (b) the mint's Δ types or δ are wrong at that
   occurrence (an indexing bug: the free-variable set is right but an entry's
   type was spelled at the wrong depth — then `bad = 0` was measuring the
   set, not the types); (c) the occurrence's level annotations disagree. The
   excerpt decides. Then say why `infer_type` on the *named root* of
   `complete_post` refuses too: is it the same difference?
2. **(1)**: which reader, which shape it expects (`record_of_at` wants a
   record's lowering; a mint at that position is a `GlobalTm`/`El(GlobalTm)`),
   and whether the fix is the reader seeing through a mint (the precedent in
   the closed-argument design §3: `unspell_here` for registered references)
   or the mint declining at positions a structural reader will read (a
   position-aware choice: never name a node that is the *receiver* of a
   projection or the *scrutinee* of a match). Both are legitimate; argue,
   pick, measure.
3. **(2)**: reproduce in ≤ 20 lines, say whether it is the elaborator's
   `unify`/`whnf` or the kernel, and attribute as in 1.
4. Then: at the threshold the fixes allow, re-run `probes/nm0.sh`'s counts
   and the `t_qt1` kernel columns (§9.5's table) with the device on, and the
   full `scripts/test` with the device **on** (`HEATHER_RB_MINT=1` in the
   suite's environment) as well as off. If green on, propose the default
   threshold and say what the pre-gate on the value graph (§9.5's cost
   item) needs — but do not build the pre-gate in this pass unless it is
   one call.

## Bar and rules

- No default-path change unless the audit is fully discharged; if it is, the
  landing needs the whole gate set (parent vs changed on the curve with
  steps and the showcase, the per-item join with no item regressing, the x86
  rails at two sizes, `WALK_RESIDUE` shrink-only, fixtures, bench dance, full
  `scripts/test`). Otherwise the device stays opt-in and the pass's product is
  the attribution and whatever fixes are measured.
- Every claim in the doc from a run in this pass. Amend
  `docs/name-per-value-design.md` with §10 (the three attributions, the
  fixes, the tables). No commits, no `cargo fmt`, no issue edits; tree left
  dirty for review.
- Furnace: one job at a time (`furnace run -- pgrep -af heather` first);
  `furnace run -- bash probes/ma_x.sh` (no shebangs; abort on build failure;
  name the binary; `== MARKER done`); build outside any `ulimit -v`; wrap
  every heather run; runs over ~8 min detached with a bounded wait; the
  x86 model modules are bundled under harness names — see the probe-loop
  notes in `probes/README.md`. Local runs are fine for small probes under
  `(ulimit -v 8388608 -t 900; …)`.
- Report: the three attributions (mechanism, one line each), what was fixed
  and its numbers, the suite lines on and off, whether the device can land
  and at what threshold, surprises. Short; the doc is the product.
