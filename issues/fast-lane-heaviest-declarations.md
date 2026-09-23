---
title: The fast lane's wall clock is guarded_read's four layout declarations (6–13 s each, all kernel gate)
status: open
labels: [performance,testing,x86,kernel]
created: 2026-09-23
updated: 2026-09-23
---

The fast lane's wall clock is one test, and that test is four declarations.
Per-test times (runner, 2026-09-23) and the suite-wide declaration rows
(`HEATHER_SUITE_DECLS=1`) show:

- The fast lane runs in ~70 s wall at 7-way parallelism;
  `function_ir_guarded_read::selected_bounds_read_checks_and_executes` alone
  takes 68 s, so it is the critical path.
- Of its 68 s, 67 s is inside declarations, and most of that is four
  generated layout declarations, all ~99 % kernel gate:

| declaration | seconds |
|---|---|
| `identity_selected::whole_layout` | 13.5 |
| `identity_selected::branch_layout` | 12.4 |
| `masked_selected::branch_layout` | 10.3 |
| `masked_selected::whole_layout` | 5.8 |

(`x86_64_structured_block` re-elaborated in it is another 2.3 s —
[[suite-tests-reelaborate-library-modules]].)

The next heaviest single declarations in the lane, for scale:
`ir_v1::constant_match_fusion_letcon_law_probe` 10.1 s (one test),
`x86_64_access_code::access_sequence` 4.9 s over two tests.

Question before any fix: the layouts are proofs about concrete byte
sequences of the guarded-read branch (`AccessFragment::branch` in the test) —
is the gate evaluating the whole encoded layout per proof (so cost ∝ bytes ×
something), and do `whole_layout` and `branch_layout` re-derive the same
facts? Same shape as [[x86-block-linked-conditional-evaluation-cost]]
(millions of steps, genuine evaluation, few misses) — check the step and
miss columns in the per-test table
(`target/suite-decls-fast/function_ir_guarded_read.*.tsv`, readable with
`scripts/timings`).

Payoff: halving these four roughly halves the fast lane's wall clock, since
the next-longest test is ~35 s (`showcase::cli_tier_showcases_check`).

## Log

- 2026-09-23: **Diagnosed — a spelling cost in `AccessFragment`'s layout emission, not evaluation of the bytes.** Probe dir built from the test's own generated modules (dumped with a temporary patch, reverted), checked at width one with the release CLI; counters reproduce the suite's exactly (`branch_layout` 3,275,110 steps, `whole_layout` 3,876,504).

  - The encoding is not the cost: `whole_encoding` (`refl` over `access_bytes`) is 45 K steps / ~0.1 s. The two branch-target λs stated alone over the *named* `yes_code()` are 2 K and 32 K steps; the children tuple over named layouts 62 K. The pieces sum to well under the whole.
  - What the whole pays for: `AccessFragment::{sequence,branch}` (`crates/elab/src/function_ir_x86_lower/access.rs`) emit the layout as one nested anonymous tuple checked against `AccessLayout(branch_code())`. The elaborator fills `trans`'s implicits from the unfolded expected type, so the emitted term spells the **reduct** of the code tree — raw `supf`/`inl@`/`pair@` constructor values of `AccessCode`/`StructuredCode` whose annotations carry the inline lowering of `Instruction`/`Gpr`/`BitVec`. Every such node misses the reflexivity shortcut against the named `El(D#tycode^δ)` and walks the whole type. Miss trace of `branch_layout` (value-metrics build, `HEATHER_CONV_MISS_TRACE`): `El^δ`/`Sum` 84 queries, `Vec`/`Σ` 40, `El^δ`/`Wf` 40 — ~85 % of the traced miss time; the rest of the 812 misses go through the `Sel` path, which the trace does not see.
  - Not app@: a throwaway build with `emits_at_forms` switched off makes these ×5.5 *worse* (`branch_layout` 18.1 M steps, `whole_layout` 21.9 M). The @ forms already helped here.
  - **The fix shape, probed:** a library lemma `access_branch_layout(register, fd, jd, yes, no, fd_ok, jd_ok, yes_ok, no_ok) : AccessLayout(AccessBranch(…))` (body `⟨fd_ok, ⟨jd_ok, ⟨yes_ok, no_ok⟩⟩⟩`) and `access_sequence_layout`, with the generator applying them to named codes and layouts. `branch_layout`'s statement proved that way: **35 K steps / 63 ms** (named-code variant 3.7 K / 7 ms), against 3.27 M / ~6.3 s; guard ⨟ branch via the sequence lemma 113 K / 0.3 s against 3.88 M. The lemma itself is 1.3 M steps, once, in the library. `structured_cert.rs` already follows this pattern (per-node `{n}_false_target`, `{n}_layout()` by name; those layouts are 30 steps each) — only the newer access composition inlines.
  - Side finding, same root: any constructor value whose declaration's fields reach `Instruction` costs ~13.5 K steps per constructor in the kernel (`inductive H1 { KH(x: Instruction) }`; `KH(x)` 13,536 steps, `match h { KH(x) => x }` 13,528, a `Gpr` field 766) — one `Σ`/`El^δ` and one `El^δ`/`Sum` miss walking `Instruction`'s inline lowering. It is why `yes_code`/`whole_code` (bare constructor trees) are 183 K–348 K steps. Logged on [[elaborator-canonical-type-spelling]].
  - Unexplained, for whoever measures after: `identity_selected::whole_layout` and `masked_selected::whole_layout` have identical counters and 13.5 s vs 5.8 s in the suite run (8.9 s standalone). Seconds under 7-way load; the counters are the datum.
- 2026-09-23: **Fixed (generator side).** `x86_64_access_code` gains `access_sequence_layout` and `access_branch_layout`; `AccessFragment::{sequence,branch}` state their layouts by applying them to the children's codes and layouts instead of a nested tuple against the literal tree. Suite rows for the test (width one, `HEATHER_TIMINGS_DIR`), before → after: the four layouts 3.88 M / 3.27 M / 3.27 M / 3.88 M steps → 700 K / 403 K / 403 K / 700 K, ~42 s → ~4.2 s gate; the two `yes_layout`s 437 K → 185 K; the lemmas themselves 1.34 M and 102 K steps, once. The test: 68 s → 21 s standalone. What is left in the layouts is mostly the per-constructor walk of [[elaborator-canonical-type-spelling]] (the codes are still spelled as constructor trees in the lemma arguments). Full `scripts/test`: 2905 passed, 0 failed.
