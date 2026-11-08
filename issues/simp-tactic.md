---
title: simp: a directed simplifier with conditional lemmas, unfolding, registered lemma sets and a residual goal
status: open
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-11-08
updated: 2026-11-08
---

Heather has no simplifier. The tactics that touch equations are:

- `rewrite`, which follows Lean's `rw`: one law, its first instance, one walk
  per instance ([[rewrite-every-instance]]);
- `grind`, which only closes goals: an equation goal, or a goal that follows
  from a contradiction (`docs/grind-design.md`);
- the deciders (`omega`, `ring`, `linarith`, `norm_num`), each for its own
  theory.

None of them turns a goal into a simpler goal and hands it on. That is what
the hand chains in the library do most often. They read over writes
(`Valuation::set_here`/`set_other` are cited 183 times in `lib/`), they push
`len`/`filter`/`map` through appends, and they unfold a definition one step
so that the next tactic (`omega`, `bv_omega`, a lemma) can read the goal.
`grind` closes such a chain only when every step is in the graph, and it
cannot leave a residue for `omega`.

Wanted: `simp`, a directed rewriter to a normal form.

- **Engine.** One bottom-up walk that matches every node against the lemma
  set, re-matching a node after its arguments are rewritten, until nothing
  fires. This is [[rewrite-every-instance]]'s walk with a set of laws
  instead of one. Each step is proved by the lemma instance and congruence,
  and the steps are chained by `trans`, so the kernel checks an ordinary
  term.
- **Conditional lemmas.** A lemma with premises (`set_other`'s `query ≠ id`)
  fires only when a discharger proves the premise at the instance. The
  default discharger is a local, then `decide`/`norm_num` on a closed
  premise. The caller can name another tactic, as
  [[grind-premise-tactic]] wants for grind.
- **Unfolding.** `simp([loop_finish, Fun::post])` unfolds the named
  definitions one δβ step at a time and never unfolds an `interface fn`
  body ([[interface-definitions]]).
- **Lemma sets.** Lemmas come from the call, plus a default set that
  modules register (`@[simp]`-like). Registration is
  [[automation-lemma-registries]]'s mechanism, and selection is
  [[lemma-selection-and-search]]'s language. Without a default set, every
  call spells out its lemma list, as `grind_using` calls do today.
- **Residue.** On an equation goal `simp` closes it by `refl` when both
  sides meet. Otherwise it returns the simplified goal for the next tactic.
  That needs a goal model in which a tactic can leave a goal, which
  [[proof-scripts-as-tac-blocks]] decides. Until then, a closing form
  `simp_then(lemmas, t)` runs `t` on the residue.
- **Hypotheses.** `simp_at(h, …)` rewrites a local's type the same way.
- **Termination.** A lemma whose right side matches its own left side
  (commutativity) is refused as a simp lemma, or is ordered by a term
  order. This is the design question [[rewrite-every-instance]] already
  raises.

Written in Heather over the host interface, like `grind`. It shares
`grind`'s `Spine`/`View` readers and its pattern matcher
(`EGraph::ematch`'s `Pattern<Q>` matching against a single term rather
than modulo classes).

Done when `rt_loop`'s `Fun::post_left`, `Fun::post_exhausted` and
`Fun::state_kept` close by
`simp([loop_finish, Fun::post], ["Valuation::set_here", "Valuation::set_other", …])`
(plus `branch_false`/`branch_true`), and an append/`len` chain from
`lib/native` closes by a registered default set with no lemma named at
the call.

## What it assumes from elsewhere
- **[[rewrite-every-instance]]** owns the one-walk engine. Assumed here:
  only that the walk can take a list of laws.
- **[[proof-scripts-as-tac-blocks]]** owns the goal model. Assumed here:
  only that a tactic can return a residual goal.
- **[[automation-lemma-registries]]** owns registration.
