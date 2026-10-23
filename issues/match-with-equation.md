---
title: "Match remembers its scrutinee: the equation arm binding"
status: closed
labels: [frontend, syntax, elaboration, design]
created: 2026-08-01
updated: 2026-08-05
---

The `fuel_monotone` round's only proof device is the "remember" idiom, and
it is the scariest thing in `lib/certgen/ir_v1.hthr` (`step_mono`, four times):

```heather
match ev1(cs, find_fun(prog)(callee)) as λ r =>
    r = ev1(cs, find_fun(prog)(callee))
    -> k_bind(ev1, env, rest, r) = Out(vs)
    -> … {
    Stuck => λ e q => absurd(q),
    Out(ws) => λ e q => …,   // e : Out(ws) = ev1(…)
}(refl)
```

The motive carries `r = scrutinee`, the match is applied to `refl`, and each
arm receives the equation specialized to its pattern. This is Coq's
`destruct … eqn:` / Lean's `match h : e with` — and computing that motive is
purely mechanical: it is the convoy pattern, `λ r => r = e -> P`, applied to
`refl`. The feature is the elaborator writing it, not new power — the same
relationship [[ih-generalization]] has to its manual route, and plausibly the
same motive-synthesis machinery.

Sketch (spelling open): `match e as r with h { … }` or `match h : e { … }` —
binds the scrutinee's value as `r` where a motive would, and `h : e = pat`
inside each arm (direction to match `j`'s taste; `step_mono` wanted `sym` of
it, so measure which direction the consumers actually take).

Design space, from the same round (the "only one branch is non-absurd"
observation): most uses scrutinize a `Res` under a hypothesis
`… = Out(vs)` that makes every arm but `Out` absurd. Two candidate homes for
that pattern, not exclusive:

- **let-else sugar**: `let Out(ws) with h := e else b => absurd(…)` — one
  non-absurd branch, equation included. Degenerate case of this feature.
- **Inversion lemmas in the library**: `k_bind(ev, env, rest, r) = Out(vs)
  -> exists ws. r = Out(ws) × …` — the reusable answer, but it needs a
  value-indexed Σ, which is [[surface-existential]]'s missing former. This
  issue owns the syntax; that one owns the statement.

Cost note: the idiom's tax is motive size per arm ([[ih-generalization]]'s
2026-07-31 datum: `step_mono` alone is 18 s of the file's 27 s). Elaborator
synthesis reproduces the same term, so this feature changes who writes it,
not what it costs; the cost lever is separate.

## Log

- 2026-08-01: **Motivation strength: down, but not out.** [[surface-existential]]
  landed value parameters, and with them `BindInv` — an inversion record for
  `k_bind` proved *once* and consumed by `let { ws, hr, hk } = …`. That retires
  **three of the four** remember-idiom convoys this issue was filed against
  (`lib/certgen/ir_v1.hthr`'s `LetMatch`, `LetLoop`, `LetCall` arms), and it does so
  without any syntax change: the inversion lemma's own proof cases on the
  answer with the *target* varying in the motive, so it does not need the
  idiom either.

  What that changes here: the idiom is no longer the thing a reader of
  `step_mono` meets four times, and the cost this issue cited is now measured
  as recoverable by a *library* device rather than a *language* one (−12.6% on
  the file). What it does not change: the fourth convoy (`LoopIter`, through
  `k_iter`) is still written out, and every *new* proof that scrutinizes a
  sub-region still writes the idiom until someone factors an inversion record
  for that shape too. So this issue is now about the ergonomics of writing the
  first such lemma, not about writing one at every use site — a real
  demotion in urgency, and an argument that the eventual syntax should be
  measured against "how hard is the inversion lemma" rather than against the
  old four-copies baseline.
- 2026-08-05: Landed as `match h : e { … }` (managed round; docs/match-equation-split-design.md §3). Three corrections to this issue's own text: (1) the direction note was evidence *for* `scrutinee = pattern`, not against — the hand-written `step_mono` convoy bound `pattern = scrutinee` and paid `sym(e)` at its only use, a tax the landed direction removes (pinned by a test whose flipped variant is rejected). (2) The guessed coupling to [[ih-generalization]]'s motive-synthesis machinery overstated it: the feature needs no synthesis, only *decoration* — one Π around whatever motive exists, one surface λ per arm, one App to refl — and it composes with an explicit `as λ` motive unchanged, which the `LoopIter` rewrite uses. (3) Refused on indexed/forded families **permanently**, with a message: an arm's index varies with its constructor, so `e = pat` would be heterogeneous and this kernel's Id is not; the honest form of that request is the family's inversion principle, where the 2026-08-01 demotion already pointed. The `LoopIter` rewrite is +7/−8 and time-neutral (69.6/67.8 → 69.7/64.9 s capped), confirming the cost note: the feature changes who writes the term, not what it costs. The let-else degenerate case is re-homed to [[let-else-sugar]] (it desugars the same way and is now cheaper); this issue closes.
