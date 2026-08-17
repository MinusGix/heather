---
title: A match's motive is synthesized from syntactic occurrences only, so the author restates the callee's body
status: open
labels: [frontend,elaboration,proofs,ergonomics]
created: 2026-08-17
updated: 2026-08-17
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

`lib/std/list.hthr`: `filter_append`, `filter_filter`, `filter_map`,
`mem_filter`. `lib/list_algos.hthr`: `count_insert`, `len_insert`,
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

`filter_append` and `filter_map` in `lib/std/list.hthr` lose their inner
`as λ b => …` motive and still check; the negative control is a `match` whose
arms genuinely disagree, which must still be refused.
