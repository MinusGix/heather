---
title: omega inside a match arm: the neutral constructor value, unspellable facts, measure candidates
status: open
labels: [omega,proofs,display,inductives]
created: 2026-09-27
updated: 2026-09-27
---

Found while closing [[tier1-arm-binder-has-no-spelling]] (2026-09-27). Arm
binders now spell by name. `omega` inside a `match` arm still fails in three
related ways. Together they are why `lib/elf64_read_loop.hthr` keeps
`eof_room`, a Nat-only lemma, instead of an inline `omega`.

1. **The arm's constructor value does not spell.** The motive is
   instantiated at the *neutral* summand (issues/absurd-on-branch-scrutinee.md),
   so `ctor_value` (`crates/elab/src/display.rs`) shows `Cons(…)`. Since this
   round, the source flavour declines on it instead of handing `omega` the `…`.
   A fact like `counted: carry + spec(eof_input(Cons(chunk, rest))) = total`
   therefore does not spell. The fields *are* the arm's aliases. A payload
   field is `fst(snd^(k+1)(payload))`, which can be matched structurally with
   annotations ignored. A recursive child is an `nth` over the children tuple
   in the Wf lowering, and a Σ projection in the tier-1 one. Recognising
   these would let `ctor_value` write `Cons(chunk, rest)`.
2. **One unspellable fact refuses the whole call.** `local_facts` feeds every
   fact to reflection, and a spelling failure is an error, even for a fact
   the relevance filter ([[omega-relevant-facts-only]]) would drop. Skipping
   a fact is sound. The cost is a worse message when the skipped fact was the
   one needed, so a stuck report should name what it skipped.
3. **Measure reduction has no candidates in an arm.** `Cons(x, rest).len()`
   reduces to the Wf eliminator applied to the arm's children. The
   candidates (`recursive_field_candidates`, `crates/elab/src/omega_cert.rs`)
   come from `children_fields`, which reads a literal pair only. So
   `len(rest)` is never proposed, and
   `ok: Cons(x, rest).len() <= 4096 ⊢ rest.len() <= 4096` is stuck inside an
   arm, although it closes outside one. The candidates would be the arm's
   recursive-child aliases. Using them needs a way to know an alias is one,
   with the right type, since `convert_term` must not see ill-typed terms.

Reproducers are in the 2026-09-27 log of
[[tier1-arm-binder-has-no-spelling]]. (1) and (2) together are enough to
inline `eof_room`. (3) is the same design's §2 with a neutral argument.

## Acceptance

- `eof_room` is replaced by `{ omega }` at its one use.
- `theorem t(xs: List<Nat>): (xs.len() <= 4096) → Nat` matching `Cons(x, rest)`
  closes `rest.len() <= 4096` by `omega`, at a concrete and at an open element
  type.
- A control: a fact about a *shadowed* arm binder still does not spell under
  its old name.
