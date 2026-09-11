---
title: Diagnostic notes run their conversion on every declaration, not only on the ones that fail
status: open
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
(`docs/instrumentation-design.md` §5). It is essentially the whole of what used
to be the elaborator's unattributed `other` bucket, and it is the largest
serial cost left on the certificate workload now that the kernel gate is
parallel: on `reused_callee` `build-x86` at one worker, 20.3 s of the 109.6 s
summed over the 3474 certificate item rows — 18.5%, against 78.6 s of kernel
gate — from 33 019 notes, none of which was printed. On
`heather check lib/std/omega.hthr` it is 0.79 s of 10.2 s from 24 142 notes.
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
  `heather check lib/std/omega.hthr`, measured the way
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
