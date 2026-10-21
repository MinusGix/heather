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

Round S2 of `docs/native-program-logic-design.md` (§6.1, §6.3): one computed
weakest precondition over every `Asm` item, the target-side tool the
compiler's per-construct lemmas are proved with.

## Scope

- `Asm` gains `Syscall` and `Proved(bytes, len, measured, contract)` with a
  relational, placement-independent contract.
- `View<M, V>`: the page view (`Stretch`'s) and the frame view
  (`Straight`'s), with their load and store arms.
- `Wp` carrying the tree and the `passed` flag; `wp_runs` and `wp_sound`
  proved once.
- **Probe first** (design §6.3): one frame run and one page run on `Wp`
  against their `Straight`/`Stretch` versions with `scripts/perf ab`. If the
  view record or the extra continuation arguments cost the elaborator,
  specialise to two monomorphic wps sharing the soundness proof.
- `Stretch`/`Straight` are not migrated callers: their callers burn in
  [[native-burn-process-stack]]. They are deleted once `Wp` covers them.

## What it assumes from elsewhere

- **[[native-linux-spec]]** owns `Sim`, `Requests`, `answered` and `next`.
- **[[wp-obligation-tactic]]** owns a tactic for these obligations, if the
  compiler rounds turn out to need one.
- **[[elab-whnf-copies-straight-continuations]]** owns the elaborator cost of
  computed continuations.
