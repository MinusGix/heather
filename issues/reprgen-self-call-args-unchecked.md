---
title: reprgen: a self-call's non-recursion arguments are not checked
status: open
labels: [compiler,generator]
created: 2026-08-15
updated: 2026-08-15
---

Found while landing the repr-typed-result stage ([[datarepr-separation]], 2026-08-15); not fixed drive-by.

`reprgen`'s fragment check reads a self-call only through its **last**
argument (the recursive child it descends on) — `self_calls` in
`crates/elab/src/reprgen.rs`, and the image-spine reader the same way. A
self-call that passes something *else* at one of the other parameters, e.g.

```heather
fn replace_all(k: Tok, l: List<Tok>) -> List<Tok> {
    match l { Nil => Nil, Cons(h, t) => Cons(k, replace_all(h, t)) }   // `h`, not `k`
}
```

is not a fold over the anchor — the fold's accumulator carries one value per
recursive child and nothing varies the other parameters down the recursion.
The generator transcribes it anyway, replacing the whole call by the
accumulator, and the emission then **fails to check**: the closing lemma's
inductive hypothesis is at the outer parameters and the goal is at the inner
ones. So this is a wrong-emission, never a wrong certificate — the trust story
holds — but a decline with a reason is what the boundary is supposed to give
(§3.3's "an honest syntactic predicate"), and a failed emission reads to a
user like a generator bug.

A sibling case with the same root (coordinator note, 2026-08-15): both
readers take the *last* argument as the recursive child, but the fragment now
admits an `S` parameter anywhere in the signature (the declaration-order fix,
same round). A self-call in such a fn has its child at the `S` parameter's
position, so the last-arg read picks up an ordinary parameter instead — safe
(the `fragment` check rejects it as "not a recursive child of the arm", no
panic, no wrong emission) but the reason string blames non-structural
recursion when the fn is fine. Read the child at the recursion parameter's
index instead of `last()`, in both readers.

Fix shape: in the fragment check, require every non-recursion argument of a
self-call to be the corresponding parameter, spelled identically; decline
otherwise. Both the plain and the image-spine readers go through the same
check, reading the child at the recursion parameter's index. Small; the
reason string is the work.

Not urgent: nothing in the suite spells one, and the failure mode is loud.
