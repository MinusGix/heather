---
title: Constructor equations in scope: a clash closes the case, an injection substitutes
status: open
thread: Make compiler correctness proofs elegant
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-11-16
updated: 2026-11-16
---

Proofs about a partial compile spend most of their arms on two facts about constructors: `None = Some(c)` is absurd, and `Some(x) = Some(c)` means `c` is `x`. Both are written out each time:

```
None => λ none => absurd(none),
Some(capacity) => λ same => j(Option::some_inj(p.reads(…), c, same), λ x _ => p.Within(x.prog), p.within_reads(…)),
```

`native_compile*.hthr` has 154 of the first and 81 `some_inj` transports with a written motive. Probed on the mini-model in `/mnt/project-files/compile-proofs/` (2026-11-16):

1. **`subst` does not look under a constructor.** `subst(Option::some_inj(x, c, same), e)` works today and already replaces the `j` and its motive. `subst(same, e)` with `same: Some(x) = Some(c)` is refused: "neither side is a local variable". Wanted: `subst` injects through matching constructors (a record's too: `Compiled(a, b) = c`) and substitutes each local it reaches; a clash closes the goal.
2. **`induct`'s default leaf does not close a case whose hypothesis is a clash.** `induct St::emits(s, p, names)` with `e: s.emits(p, names) = Some(c)` leaves `Leaf::False` (where `e` reads `None = Some(c)`) to `known`, which reports that it found no `Within(p, c.code)`. Every such arm is then written `Leaf::False => absurd(e)`. Wanted: `known` (so `induct`'s default and `all_goals { known }`) closes a goal from a hypothesis that equates two different constructors.
3. **`split_all` leaves the injection undone and unnamed.** At `same: Leaf(w).emits(p, names) = Some(c)` it closes the `False` case itself and leaves the `True` case with `__split_all_x7 : Some(Out(Cons(w, p), names)) = Some(c)`, listed twice, a name a proof cannot write, and `c` not substituted in the goal. Wanted: an equation between constructor applications left by a split is injected, and where a side is a local, substituted, so the leaf's goal is `Within(p, Cons(w, p))`.
4. `known` does not prove `True` (seen while probing: "`known` found no hypothesis `True`").

[[derive-record-injectivity-congruence]] derives the lemmas; this is the steps using them without being told.

## Done when

On the model, the six non-recursive cases of `emits_extends` need no arm for a refused test, and an arm that succeeds is written at `c` already replaced. In `native_compile_correct.hthr` no arm reads `λ none => absurd(none)` and no `j` has `some_inj` as its equation.

## Log

- 2026-11-16: Items 1–4 built. `subst` injects through an equation of one
  constructor's applications down to fields with a local side, substitutes
  them one at a time (reading `h` again in each case), and closes the goal on
  a clash (`LocalSubsts::inject`, `crates/elab/src/subst_local.rs`;
  `docs/tactics/equation-rewrite-design.md` §8). `known` proves `True` and
  closes a goal from a hypothesis whose sides, or fields, are different
  constructors (`Tested::known`), so `induct`'s default leaf closes a refused
  test's case. `split_all` substitutes through the equations its splits
  leave (`injected_hypothesis`, `docs/tactics/goal-combinators.md`). Probes:
  `lib/_tests/std/tactic/constructor_equation_tests.hthr`. Left for the
  "Done when": `native_compile_correct.hthr` in the new forms (its
  `subst(Option::some_inj(x, c, same), e)` become `subst(same, e)` in the
  cleanup thread's branch), and the `λ none => absurd(none)` arms, which go
  when those proofs are by `induct` (induct-through-result-matches). The
  leaf's context report still lists the shadowed binders a split re-bound
  (induct-case-goal-report's subject).
