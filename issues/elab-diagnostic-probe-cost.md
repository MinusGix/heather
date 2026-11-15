---
title: Diagnostic notes run their conversion on every declaration, not only on the ones that fail
status: closed
labels: [elaboration,performance,diagnostics]
created: 2026-09-11
updated: 2026-09-11
---

`Elaborator::note_check_mismatch` and `Elaborator::note_refl_mismatch`
(`crates/elab/src/lib.rs`) exist to turn the gate's crisp `NotConvertible` at a
whole declaration into a message that names the two sides. Each one **runs its
conversion first**, to find out whether there is anything worth saying — and it
runs it on every candidate, whether or not the declaration goes on to check.
On a run where nothing fails, every one of those conversions produces a note
that is never read.

Named for the first time by the `diag_note` column added on 2026-09-11
(`docs/infrastructure/instrumentation-design.md` §5). It is essentially the whole of what used
to be the elaborator's unattributed `other` bucket, and it is the largest
serial cost left on the certificate workload now that the kernel gate is
parallel: on `reused_callee` `build-x86` at one worker, 20.3 s of the 109.6 s
summed over the 3474 certificate item rows — 18.5%, against 78.6 s of kernel
gate — from 33 019 notes, none of which was printed. On
`heather check lib/std/tactic/omega.hthr` it is 0.79 s of 10.2 s from 24 142 notes.
See the numbers in [[perf-instrumentation-consolidation]]'s 2026-09-11 log.

The `refl` note is the expensive half by construction: the certificate is
thousands of `refl` pins whose two sides are large, and `note_refl_mismatch`
runs a budgeted conversion on every one of them before deciding it has nothing
to add. `note_check_mismatch` runs an unbudgeted `convert_type` at each
checking site whose types are not syntactically equal.

## What to try

- **Defer the probe to the verdict.** Record the candidate sides (spans and
  terms) while elaborating and run the conversion only if the declaration is
  actually rejected. The note already only *reads* on rejection; this makes it
  only *cost* on rejection. The price is keeping the candidates alive for the
  length of one declaration attempt, dropped on success — and a decision about
  which candidate to keep, since today the first note to fill the slot wins and
  a deferred list would have to reproduce that order.
- **Ask the gate's verdict instead of recomputing it.** The gate's own
  conversion has already decided the same question; what the note adds is a
  *span* and a pair of spellings, not a new judgement.
- Careful: `note_check_mismatch` fires at checking sites *inside* a body, at
  spans the declaration-level failure cannot name; that span is the whole point
  of the note and must survive whatever replaces the eager probe.

## Acceptance

- `diag_note` near zero on a successful `reused_callee` `build-x86` and on
  `heather check lib/std/tactic/omega.hthr`, measured the way
  [[perf-instrumentation-consolidation]]'s 2026-09-11 entry measured it.
- Byte-identical diagnostics on the failing fixtures that own these messages
  (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`, the
  `display-inductive-type-arguments` look-alike filter, and the mutation
  controls that read `NotConvertible` at a named declaration).

## What it assumes from elsewhere

- **[[perf-instrumentation-consolidation]]** owns the column that found this.
  Assumed here: only that `diag_note` keeps meaning "conversion run for a
  message".
- **[[parallel-kernel-gate]]** owns the width. Assumed here: that the
  elaborator's serial half is what the 2.88x ceiling is made of, so shrinking
  this moves the ceiling.

## Log

- 2026-09-11: Implemented "defer the probe to the verdict". `note_check_mismatch` and
`note_refl_mismatch` now only **record** a candidate — span, the cloned `Cx`,
the two sides, the level — into `DeclAttempt::check_notes` / `refl_notes`, with
no conversion and no spelling. The probe moved to `probed_check_note` /
`probed_refl_note`, driven by `pending_mismatch()` / `pending_refl_note()`,
which iterate the recording order and stop at the first candidate that has
something to say — exactly reproducing the old "first note to fill the slot
wins". Both are called only from `kernel_error`, the one reader, and only on
`NotConvertible`. Under the parallel gate the join reports `note: None`,
discards its pass and replays serially (parallel-kernel-gate-design §5.1), so
every rejection is reported from `kernel_error` on the serial path and the
candidates are always in hand; a new test asserts both notes and both inner
spans at W=1 and W=4. The `refused_decide` deferred probe was the template.

Two record-time filters, both decisions rather than probes: `refl`'s existing
`lhs == rhs`, and a new `got == expected` on the checking side. That is why
`diag_candidates` (15116 on the certificate) is *below* the old `diag_notes`
(33019): 17903 of the eager conversions were on syntactically identical types.

Measured on the furnace (EPYC 9J14), release, warm image cache, discarding the
run after each rebuild. `reused_callee` `build-x86` at `HEATHER_KERNEL_WORKERS=1`,
run row, seconds:

  column        before    after
  total         131.310  107.265
  kernel_gate    88.350   86.839
  diag_note      21.426    0.000
  diag_notes      33019        0
  diag_candidates     —    15116
  decl_type       1.866    1.586
  decl_body       5.674    5.051
  decl_emit       1.671    1.424
  elab_whnf       1.057    1.042
  other           0.320    0.414
  wall          131.84s  107.79s
  peak RSS       986 MB   994 MB

`heather check lib/std/tactic/omega.hthr -L lib/std` at W=1:

  total           9.775    8.674
  kernel_gate     6.805    6.354
  diag_note       0.771    0.000
  diag_notes      24142        0
  diag_candidates     —    11654
  decl_body       0.620    0.629
  decl_emit       0.600    0.541
  other           0.141    0.296
  wall            9.84s    8.74s
  peak RSS       198 MB   220 MB

Total falls by what `diag_note` was and nothing else rises: `other` gains
0.09 s (certificate) / 0.16 s (omega), which is the untimed record-time
bookkeeping — the `Cx` clone per candidate — and is the whole price. Memory is
the other price: +0.8% peak RSS on the certificate, +11% (22 MB) on omega, from
holding one declaration attempt's candidates alive. No cap was added.

The number the round is for — the same build at the **default eight workers**,
wall only: 46.89 s / 46.45 s before, 26.91 s / 26.82 s after. 1.73x, and the
serial elaborator that bounded the parallel gate's ceiling is that much
shorter.

`diag_note`/`diag_notes` keep meaning "conversion run for a message" and now
read zero on a module that checks; a nonzero value means a declaration was
refused. `diag_candidates` counts what was recorded instead. Both documented in
instrumentation-design §5, and the instrumentation test flipped from
"a successful proof still paid for a diagnostic probe" to asserting
`diag_notes == 0` and `diag_note_ns == 0` with `diag_candidates > 0`.

`furnace run -- scripts/test --fast`: == suite: 2436 passed, 0 failed, 5 ignored ==.
`scripts/bench --check` on the furnace: shape-only, 18 comparisons within
thresholds, 88 skipped for the desktop-recorded baseline's env mismatch, no
slope flagged — `crates/kernel` is byte-identical in this diff. Full
`scripts/test` left to the coordinator; not committed.
- 2026-09-11: 2026-09-11: landed — both helpers record candidates and the probe runs only from kernel_error on NotConvertible, in recording order, first fill wins; the two width fixtures and all ten check_reports_mismatch fixtures are byte-identical. diag_note 21.4 s -> 0 on the certificate (33 019 eager conversions -> 15 116 recorded candidates, of which none probed on success), 0.77 s -> 0 on omega. reused_callee build-x86: W=1 wall 131.8 -> 107.8 s; W=8 wall 46.9 -> 26.9 s. Full lane 2575 passed, tests 164 s. Closing; the gate-verdict-reuse idea for the refl note stays unbuilt because deferral left it nothing to buy.
