---
title: One computed weakest precondition over every Asm item
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
blocked-by: [native-linux-spec]
created: 2026-10-20
updated: 2026-10-20
---

Round P2 of `docs/native-program-logic-design.md` (§4, §5): one computed
weakest precondition over every `Asm` item.

## Scope

- `Asm` gains `Syscall` and `Proved(bytes, len, measured, contract)` with
  `Contract<M>` (pre, relational post, placement-independent runs).
- `View<M, V>`: the page view (`Stretch`'s) and the frame view
  (`Straight`'s), with their load and store arms.
- `Wp` carrying the spec position and the `passed` flag, and `wp_runs` /
  `wp_sound` proved once. `stretch_runs` and `straight_runs` become
  instances or are deleted with their callers moved.
- **Probe first** (design §8): move one frame phase (`loop_last`) and one
  page stretch (the filter's byte load) onto `Wp` and compare with
  `scripts/perf ab` before moving anything else. If the view record or the
  two extra continuation arguments cost the elaborator, specialise to two
  monomorphic wps sharing the soundness proof.
- Decide whether `Runs` stays as notation (design §10, question 5).

## What it assumes from elsewhere

- **[[native-linux-spec]]** owns `Spec`, `Requests`, `answered` and `Sim`.
- **[[elab-whnf-copies-straight-continuations]]** owns the elaborator cost
  of computed continuations. Assumed here: only that it is unchanged; a fix
  there makes this round cheaper, not different.
