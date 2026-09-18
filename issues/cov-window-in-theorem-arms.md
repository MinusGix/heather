---
title: Course-of-values window in a theorem: a goal with a hypothesis on the scrutinee is refused, a chain match under a λ gets the outer goal
status: open
labels: [frontend,elaboration,recursion,proofs]
created: 2026-09-18
updated: 2026-09-18
---

Found closing [[utf8-encode-decode-strictness]] (2026-09-18). The strictness
proof wanted to recurse on the byte list the way `utf8::decode` does — the
`Cons` arm, a nested `match` on the tail to depth three, the induction
hypothesis at each depth — and the window of
[[list-course-of-values-recursion]] did not carry it in the shapes a theorem
needs. Probes on `skip2(xs)` (sum every other element of a `List<Nat>`; the
decoder's shape at depth two), all with the self-call at `r2`, the child of
the child:

1. **A goal with a hypothesis that mentions the scrutinee is refused.**
   `theorem skip2_le(xs): (n: Nat) → skip2(xs) = n → n <= list_len(xs)`,
   `Cons(a, r) => match r { …, Cons(c, r2) => λ n q => … skip2_le(r2, skip2(r2), refl) … }`:
   "recursive call to `skip2_le` must descend … A window of earlier values
   exists for chain-shaped declarations … and this one is not" — the
   `cov: None` text, and wrong on its face (`List` is chain-shaped). The same
   nesting with the goal `Nat → skip2(xs) <= list_len(xs)` and the call
   `skip2_le(r2, 0)` **checks**, so neither the `λ` arms nor the extra
   argument is what the window objects to; the hypothesis `skip2(xs) = n` is.
2. **A chain `match` under a `λ` gets the outer goal back.**
   `Cons(a, r) => λ z => match r { Nil => trivial, … }` against
   `Nat → skip2(xs) <= list_len(xs)`: the `Nil` arm is checked against
   `Nat → Le(…)`, the un-applied goal — the convoy rebuilds its codomain from
   the OUTER motive (`docs/list-course-of-values-design.md` §7.3), so the
   binder the `λ` introduced is dropped from the arm's obligation.
3. A written dependent motive on the chain `match` is refused with the same
   message as 1; logged on [[convoyed-window-vs-written-motive]], which owns
   the diagnostic.

The proof landed on a `Nat` bound on the byte count instead
(`utf8::strict_below`, `Bounded(k)`), with the per-depth hypotheses as plain
function arguments and `nat::le_of_lt` once per byte stepped over — exactly
the arithmetic-between-call-and-hypothesis the list design says the window
exists to remove, small here but the datum is the shape, not the size.

To decide: whether the window should carry theorem-shaped goals — a Π whose
hypotheses mention the scrutinee (1), and a chain `match` under binders (2) —
or the design doc should say the window is for the `fn` shapes it was built
for and a proof over such a function takes a measure. If the former, (1)
looks like the convoy's codomain construction (§7.3) not abstracting the
scrutinee out of the hypotheses, and (2) like it ignoring the binders between
the arm and the nested `match`; both are in `wf_chain_convoy` / `WfConvoy`
(`crates/elab/src/wf.rs`). Either way the message in (1) should not say
"not chain-shaped" about a `List`.

## What it assumes from elsewhere
- **[[list-course-of-values-recursion]]** owns the window and its convoy.
  Assumed here: only that the convoy's codomain is built from the enclosing
  recursion's motive (its design §7.3).
