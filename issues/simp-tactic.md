---
title: simp: a directed simplifier with conditional lemmas, unfolding, registered lemma sets and a residual goal
status: open
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-11-08
updated: 2026-11-11
---

Heather has no simplifier. The tactics that touch equations are:

- `rewrite`, which follows Lean's `rw`: one law, its first instance, one walk
  per instance ([[rewrite-every-instance]]);
- `grind`, which only closes goals: an equation goal, or a goal that follows
  from a contradiction (`docs/tactics/grind-design.md`);
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

## Log

- 2026-11-10: Minus, after the foundational-mathematics ranking (`docs/roadmap.md` log, 2026-11-10): `simp` "would be great", and it should be tunable and wrappable. Software is cheap now, so a variant written to be more powerful for one case is acceptable, as is a domain tactic that wraps `simp` with its own lemma set and side-condition discharger. Design consequence: the simplifier's loop takes its lemma set, its discharger and its pre/post procedures as arguments, so `set`-, substitution- (sigma calculus, [[generic-binding-syntax]]), `ZMod`- and Kleene-algebra-specific simplifiers are instances, not forks. The five new mathematics milestones are each mostly directed equation sets and raise this issue's priority.
- 2026-11-11: Design proposal written after Minus asked for the design in depth, with departures from the usual simplifier where they pay for AI authors (`docs/tactics/simp-design.md`, nothing built). Proposed: a non-closing call states its result and `simp` proves the two ends join (closing and stated calls are one operation; a bare residue is exploration only and prints the statement to paste); no global default set, sets are named registered values owned by a type; a set is checked at registration as a rewrite system (orientation refused, unjoined overlaps reported with the lemma that would join them); relations from the first round with sets; failure reports name the next action (blocked premises, near misses, the gap as a lemma); the walk and proof in the host over `rewrite`'s relation walk, policy in Heather. Five decisions are Minus's (§0). Rounds in §8; round 1 closes [[rewrite-every-instance]].
- 2026-11-11: Round 1 built, relations included (Minus: "more fully than `=` only"): `simp_only(r₁, …, rₙ)` and `simp_show(…)` are term forms like `rewrite` (`crates/elab/src/rewrite/simp.rs`), a driver over the existing steps: the first law with an instance fires at every occurrence of that instance, then the list restarts, until none fires. Laws conclude `=` (the `J` step) or a designated relation (the relation walk, which now also crosses inductive constructor values with registered evidence). A closing call compares the two normal forms and stops as soon as the sides are one term; `then := e` proves what is left, `using := h` normalises a fact to the same statement; a side condition is a hypothesis in scope, a `let`, or `discharge := e`. Calls at constructors compute before matching, a structural recursion with its recursive calls kept as calls (`goal_combinators::recursion_at_constructor`, from the refolded reduct walk). The report gives the route (`law: lhs ⟶ rhs` per step), the laws blocked at the normal form with their unmet condition, and a loop at its first repeat instead of at the 256-step budget. Probes: `lib/_tests/std/tactic/simp_tests.hthr`. First adoption: `Regex::simp_same` is three one-line arms, `Regex::deriv_simp_same` one `simp_only` per case. Not built yet: named sets and per-type defaults (§3, §3.1), registration checks (§4), `by simp(…)` policy in Heather, unfolding by name, `--json`. Gaps filed: [[simp-iff-laws]], [[simp-under-binders]], [[case-split-unfolds-the-goals-relation]]. The driver is one walk per step, so [[rewrite-every-instance]] stays open as its cost.
- 2026-11-11: Sets and per-type defaults built (Minus's amendment, design §3.1; doc §11): `SimpSet` is a registered record (`lib/std/tactic/simp_laws.hthr`, `simp_default(name, name_of(T), laws)` / `simp_set(name, laws)`), and `by simp()` (`lib/std/tactic/simp.hthr`) takes the default sets of every type a value in the goal has, plus `extra := […]`; `by simp_with([S])` names sets, `defaults := False` leaves the defaults out. The run is a new host request, `Simp(laws, goal)` (tag 35), over the `simp_only` driver, so policy is Heather and the walk is the host. Defaults: `Nat::arith`, `List::shape`, `Regex::same`. A refusal lists the sets used and the type that brought each. `Regex::simp` is renamed `Regex::simplify`: a free `simp` makes `e.simp()` ambiguous. Left: the registration checks (§4), `--json`, unfolding by name, and the three filed gaps.
- 2026-11-11: Set checks built as a run, not as an order (doc §11): `by simp_check([S, …])` (host request `SimpCheck`, tag 36, `Simps::check_terms`) normalises each law's own statement, binders as fresh variables, by the whole list. A loop refuses the list; two sides that do not meet are an overlap that does not join, reported with the two normal forms. The defaults carry their checks as theorems of `True` (`simp_nat_arith_checked`, `simp_list_shape_checked`, `simp_core_defaults_checked`, `Regex::simp_regex_same_checked`). Open against §4: no termination order (tested at generic instances, not proved); two-sided critical pairs (associativity against a unit) need unification of left sides; a registered set is not forced to have a check.
- 2026-11-11: `P ↔ Q` laws built (docs/tactics/simp-design.md §12, simp-iff-laws closed): statement positions, congruences for `↔` in `logic`, equations carried into connectives and below `∀`, `List::mem_append_iff` in `List::shape`. Next: `∃` bodies and λ bodies (simp-under-binders), case-split-unfolds-the-goals-relation, unfolding by name, `--json`.
- 2026-11-11: Under binders built (docs/tactics/simp-design.md §13, simp-under-binders closed): `∃` bodies by `iff_exists_congr`; λ bodies by walking an equation as a step of `RelId` with the consumer's pointwise evidence (`list_pointwise`: map, filter, count). No funext in Heather, so each higher-order function brings its own. Filed: view-of-value-parameterised-record, type-arguments-under-a-binder-print-elided.
- 2026-11-11: 2026-11-11: `by simp()` collects default sets inside an `∃` (the host's view of a value-parameterised record presents its value arguments); pointwise evidence for `foldr`, `foldl`, `any_bit`, `all_bit`, `find`, `split_by`, `update` and sums along `=`. New: `simp-unfolded-call-loses-spelling`.
- 2026-11-14: What the native proofs still do by hand, and what a default discharger would need: [[simp-adoption-native-gaps]].
