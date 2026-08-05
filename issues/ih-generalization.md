---
title: IH generalization: recursion whose non-decreasing arguments vary
status: open
labels: [frontend,elaboration,design]
created: 2026-07-31
updated: 2026-08-05
---

Promoted from [[match-recursion]]'s deferred note (2026-07-24: "the one
real limitation") to its own jumpable issue, because it now has a named
customer waiting: `fuel_monotone` — [[ir-simulate-design]] section 11
item 3, the keystone of the converges interface — is an induction on fuel
whose motive must quantify env/ir/the equation, i.e. exactly this.

The mechanism, as the deferred note already sketched: M(z) = Pi over the
varying params; arm bodies lambda-wrap; self-calls become `ih(e)` at the
varied arguments; the match is forced to the body root. The MVP is the
empty-generalized-set case, so this is additive.

What the ir_v1 round adds to the picture:

- The WORKAROUND exists and is load-bearing today: return a function
  (`lookup(env) -> Nat -> OptVal`, fuel-curried `eval`). Fine for
  programs; for PROOFS it contorts statements, and fuel_monotone wants
  the theorem stated over the applied form.
- The manual route also exists — explicit motive
  (`match fuel as λ f => (env: Val) -> ...`) with the `Succ(k, ih)`
  arm spelling — so this issue's feature is "the elaborator computes
  that motive", not new power. A session-sized proof either way; the
  feature removes the motive-writing, not the case analysis.
- Cost coupling: generalized motives are bigger terms at every arm, and
  [[simulate-conversion-cost]] bills term size per conversion step —
  worth measuring on the fuel_monotone prototype rather than assuming.

## Log

- 2026-07-31: **The named customer landed, by the manual route, and the cost
  it asked for is measured.** `fuel_monotone` is proved in `lib/ir_v1.hthr`
  (both the `+ k` and the `<=` shape), together with `refines` and a
  ∀-arguments `equiv`; four explicit motives in total (`step_mono`'s case
  tree over `Ir`, `eval_mono_succ`'s induction on fuel, `le_add`'s induction
  on `n` with `m` generalized, `add_loop_runs`'s induction on the loop
  counter with the accumulator generalized). The feature is still wanted —
  writing the motive out is exactly the tax this issue names — but it is no
  longer a blocker for anything.

  **The cost datum this issue asked for.** The release `heather check` of
  `lib/ir_v1.hthr` goes **1.31s / 14.2 MB → 26.9s / 18.6 MB**, and ~18s of
  that is `step_mono` alone (1.79s → 19.8s when that one theorem is added).
  Its debug elab test went 9.2s → 165 CPU-seconds against `scripts/test`'s
  300-second rail. Three things the number says:

  - The tax is **term size at each arm**, not reduction: peak memory moved by
    4 MB while time moved by 20×, and the expensive theorem is the one whose
    motive forces `step` to unfold once per `Ir` constructor with *two*
    interpreters in scope. [[simulate-conversion-cost]]'s "term size is billed
    per conversion step" is confirmed at the shape this issue predicted.
  - It does **not** contradict [[nbe-conversion-round]]'s demotion of the
    single-ih discipline ([[ir-simulate-design]] doc §13 note 4). A duplicated
    *ih occurrence* is now free because it evaluates to a shared value; a
    *generalized motive* is a different object — it is bigger before anything
    evaluates.
  - So the feature's payoff is now quantified rather than aesthetic: an
    elaborator-computed motive would not make the terms smaller, but it is the
    only lever that stops a proof author from paying this by hand at every
    such induction, and the next `step_mono`-shaped theorem in that file has
    ~135 CPU-seconds of budget left before the rail.

  One surface change was needed to make the manual route usable at all, and it
  is landed: a **motive body is parsed with the type grammar**, so
  `match fuel as λ f => (env: Val) -> …` parses. Before this round it did not
  — `->` is not in the expression grammar — so the "manual route exists"
  claim above was true of the kernel and false of the surface.
  (`crates/syntax/src/parser.rs`, one-shot `motive_body` flag;
  `ExprKind::TyLit`; tests in `crates/elab/tests/motives.rs`.) Backwards
  compatible: the type grammar falls through to the expression grammar for
  equations, names and applications, which is every motive that parsed before.
- 2026-08-05: The call-site half of the workaround got cheaper: [[call-site-overapplication]] landed (2026-08-05), including over-applying an induction hypothesis, so a curried-return fn is called nth(t, k) everywhere. The definition-site motive computation remains this issue's scope, cost warning unchanged.
