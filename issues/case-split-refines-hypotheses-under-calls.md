---
title: A case split refines a hypothesis that reaches the test through a call, and match h: refines the context
status: open
thread: Make compiler correctness proofs elegant
labels: [elaborator,matching,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-16
updated: 2026-11-16
---

A case split in a proof refines the goal through a call's unfolding (`docs/elaborator/goal-motive-synthesis-design.md` §4.5): `match h: test` finds the test under the function's call. A hypothesis already in scope does not get the same treatment. On the mini-model in `/mnt/project-files/compile-proofs/` (2026-11-16), with `same: Leaf(w).emits(p, names) = Some(c)` a parameter of the theorem:

```
// refused: `absurd` needs both sides of the equation to be constructor applications
match fits(w) { False => absurd(same), True => … }
```

`same` mentions `fits(w)` only after `emits` unfolds, so it is not refined. Two cases, measured separately:

1. **The test is under a call in the hypothesis.** Not refined, with the plain `match` and with `match h:`. The goal side reads the reduced goal; the hypothesis side reads only what is written ([[match-refines-computed-scrutinee]], closed, is syntactic occurrence).
2. **The test is written in the hypothesis and the match is `match fit: fits(w)`.** Not refined either, though the plain `match fits(w)` on the same hypothesis is. The named form loses the refinement of the context.

The workaround is everywhere in the native compiler's proofs: the hypothesis is taken as an arrow of the goal with a written motive, each arm re-introduces it, and the match is applied to it at the end,

```
(match layout.words_fit([fd, at, len, result]) as λ b => layout.words_fit([fd, at, len, result]) = b → (match b {
        False => None,
        True => match layout.capacities.nth(buf) { None => None, Some(capacity) => Some(p.reads(…)) },
    }) = Some(c) → c.prog.Within(t.program) → … → t.RunsK(Invoke(Reads(fd, buf, at, len, result)), …) {
    False => λ _ none => absurd(none),
    True => λ fit => …
})(refl)
```

which restates the callee's body in the motive: what [[goal-motive-by-scrutinee-abstraction]] removed for goals. `native_compile*.hthr` and `native_structured*.hthr` have 204 written `as λ` motives; in `native_compile_correct.hthr` most of the 84 are this. `Region::paired` is fifty lines of it for a three-line function.

## Wanted

- A hypothesis whose type is stuck on the scrutinee after reduction is reverted and refined with the goal, under the same budget and the same rule as §4.5 (and as `induct` reverts the locals that mention a varying argument).
- `match h: test` refines the context as the plain form does.
- [[split-all-revise-hypotheses]] is the same gap in `split_all`'s own motive; one mechanism should serve both.

## Done when

Both probes above check with `False => absurd(same)`, and `Region::paired`, `Prog::laid_of` and the four `Invoke` arms of `Stmt::emits_runs` are written with motive-free matches and no `(…)(refl, emitted)` application.
