---
title: A match's motive is synthesized from syntactic occurrences only, so the author restates the callee's body
status: closed
labels: [frontend,elaboration,proofs,ergonomics]
created: 2026-08-17
updated: 2026-10-10
---

Ranked **#1** by waves L2′/L3 ([[std-list-l2-prime-laws]],
[[std-list-mem-and-perm]]), by count and by line-cost: **seven** of the round's
declarations write an inner motive whose only content is the body of the
function the goal already mentions.

The elaborator does abstract the scrutinee when it occurs in the goal
*syntactically* — `std/list`'s `take_append_drop` and `len_zip` both split an
argument with no motive and their goals mention it — so this is not "motives are
never synthesized". It is that the goal is not put in weak head normal form
first. When the scrutinee's occurrence is one unfolding away, nothing is found,
the arms are checked against a constant motive, and the kernel refuses.

## The shape

`filter(Cons(h, t), p)` whnf's to `match p(h) { True => Cons(h, filter(t, p)),
False => filter(t, p) }`. To split on `p(h)` the author has to write that
`match` out, in the motive, by hand:

```heather
theorem filter_append<A>(xs, ys: List<A>, p: A -> Bool):
    filter(append(xs, ys), p) = append(filter(xs, p), filter(ys, p))
{
    match xs {
        Nil => {},
        Cons(h, t) => match p(h) as λ b =>
            (match b { True => Cons(h, filter(append(t, ys), p)),
                       False => filter(append(t, ys), p) })
            = append(match b { True => Cons(h, filter(t, p)),
                               False => filter(t, p) }, filter(ys, p))
        {
            True => cong_cons(h, filter_append(t, ys, p)),
            False => filter_append(t, ys, p),
        },
    }
}
```

Six of the eight lines are the motive; the mathematics is the two arms. The
motive is *derivable*: whnf the expected type, abstract every occurrence of the
scrutinee, done — which is exactly what the syntactic case already does one
step earlier.

**Control, run 2026-08-17:** the same theorem with the inner `as λ b => …`
deleted is refused, `the kernel rejected 'fa_no_motive': NotConvertible`, no
arm and no subterm named. Same control on `filter_filter`, same message.

## The seven sites

`lib/std/data/list.hthr`: `filter_append`, `filter_filter`, `filter_map`,
`mem_filter`. `lib/lang/list_algos.hthr`: `count_insert`, `len_insert`,
`mem_insert` — these three restate `or_pick(d, …, …)` rather than `filter`'s
`match`, which is the same tax at a *decided* scrutinee. Three that landed
earlier pay it too (`std/list`'s `len_filter`, from wave L2; `list_algos`'s
`le_head_insert` and `insert_sorted`, from the sortedness half), so the live
count in the two files is **ten**.

## What it is not

- Not [[match-with-equation]], which landed and works: `match e : p(h)` binds
  the scrutinee's equation in one token. That feature answers "what does this
  arm know", this issue answers "what is this arm proving". `filter_filter`
  needs both and they compose.
- Not [[congruence-by-anti-unification]], which owns the *other* half of
  `filter_filter`: rewriting the second, unreachable `p(h)` still costs a
  hand-written `j` motive. Distinct because that one is a rewrite under a
  context and this one is a case analysis's own motive.
- Not [[match-arg-of-polymorphic-callee-needs-motive]] (closed): that one gave a
  *constant* motive to a match in inference position. Here the motive must be
  non-constant, and the arms disagree precisely because it is not.

## What it assumes from elsewhere

- **[[decided-case-convoy]]** owned the combined "convoy plus hoisted branch"
  tax. Assumed here: only its 2026-08-17 measurement — the hoisting half never
  appeared and the convoy half is one token, so this is the residue.

## Acceptance

`filter_append` and `filter_map` in `lib/std/data/list.hthr` lose their inner
`as λ b => …` motive and still check; the negative control is a `match` whose
arms genuinely disagree, which must still be refused.

## Log

- 2026-08-17: Verified after the diagnostics pair landed and all three of the day's rounds were merged (2026-08-17): this class is NOT localized by [[check-fallback-discards-expected-type]]'s fix. The four-line Box repro still reports exactly `the kernel rejected 'ddb_id': NotConvertible` at the declaration's span, because the arm's proof is `refl`, which has its own checking arm and is one of that round's own deliberate controls (a `refl` at a false equation stays a kernel rejection). So the control quotes in this issue remain accurate, and the diagnostics round did not reduce the cost of finding this defect — only the cost of reading a goal hole once you suspect it ([[le-diagnostics-print-raw-el]] is what both rounds actually used to localize it). Bearing on scheduling: the two motive issues are now the strongest-evidenced open items and nothing that landed today weakens the case.
- 2026-08-17: Fixed 2026-08-17, with issues/nested-match-on-field-binder-motive.md, in one function: docs/goal-motive-synthesis-design.md. Verdict on the one-defect hypothesis: ONE function, TWO mechanisms, and neither fix subsumes the other. This issue's half is mechanism A — the goal names the scrutinee one unfolding later — and "whnf the goal, then abstract syntactically" is NOT enough for it: reduction respells. Unfolding filter(append(Cons(h,t),ys),p) rebuilds the cons cell, so the p(h) the LEFT side is blocked on is p applied to a projection of a literal pair, one Sigma-beta from the p(h) the elaborator built, while the RIGHT side (whose Cons is the original) spells it exactly. Measured: syntactic abstraction over the reduced filter_append goal hits the right side and misses the left, which is worse than missing both — the arms then face a goal specialized on one side and stuck on the other. The landed rung therefore matches by CONVERSION at the positions the reduced goal is stuck on (an eliminator scrutinee that could not fire, recursively; capped candidate set, one conv call each), and abstracts everything that converts in a single pass so all spellings become the same z. Reduction is the last rung and nothing that checks today reaches it. Collected: all ten sites lose their motives — std/list's len_filter, filter_append, filter_filter, filter_map, mem_filter; list_algos' le_head_insert, insert_sorted, count_insert, len_insert, mem_insert. filter_filter keeps its 'match e : p(h)' and its j and loses nine lines of motive, so the two features compose as the design predicted. New kernel op Type::abstract_local/_with/_any on the existing Mapper traversal (one new default-None hook, pre_tm); new tests in crates/elab/tests/motive_synth.rs including the disagreeing-arms control and a split on a decision the goal is NOT blocked on (still refused).
- 2026-10-10: A related defect in hypotheses rather than the goal is filed as [[elab-match-refines-hypothesis-kernel-rejects]]: the elaborator checks an arm as if a hypothesis bound before the match were refined, and the kernel rejects the term.
