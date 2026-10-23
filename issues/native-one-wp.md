---
title: One computed weakest precondition over every Asm item
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
blocked-by: [native-linux-spec]
created: 2026-10-20
updated: 2026-10-21
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

## Log

- 2026-10-21: LANDED: `Asm` has `Syscall` and `Proved(index, bytes, len, measured)`; `Wp` (`lib/std/os/linux/linux_x86_64_wp.hthr`) covers every item, carries the tree and `passed`, and `wp_runs`/`wp_sound` are proved once over any sound `View`; the page and frame views are `lib/linux_x86_64_views.hthr`. Differences from the design (contract table for `Proved`, `wp_reach` for landings both ways, Linux's leftovers through the view's `Stores`) are design §6.4. The probe: no monomorphic split; the cost is the syscall continuation's respelling, logged on [[elab-whnf-copies-straight-continuations]]. `Stretch`/`Straight` were already deleted by B1, so there was no A/B against them; the probe compares each control's elaboration against its own gate. Follow-ups: [[asm-landing-both-ways]]; PR #106's new `Asm` items (calls, stack forms) need `Wp` arms: `wp_item` leaves them at its catch-all `False`, but `wp_item_goes` matches every item, so whichever of the two PRs merges second adds the soundness arms (`False` ones at least). #106 merged first; the merge added `False` arms, and real ones are [[wp-stack-items]].
