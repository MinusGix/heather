---
title: omega inside a match arm: the neutral constructor value, unspellable facts, measure candidates
status: closed
labels: [omega,proofs,display,inductives]
created: 2026-09-27
updated: 2026-09-28
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

## Implementation log

- 2026-09-28: Added a shared tuple-field reader for literal and neutral
  constructor tuples. Neutral projections match typed aliases without their
  annotations; Wf `nth` aliases are reduced under the bounded spelling budget
  before matching. Constructor printing and recursive measure candidates both
  use it. Printed binders account for weakening and avoid capturing aliases.
- Ordinary arithmetic reflection skips unspellable facts, rolls back partially
  interned atoms, and names skipped facts in a stuck diagnostic. A shadowed
  field still cannot be spelled using its old name.
- Removed `eof_room` and replaced its one use with `{ omega }`.
- Regressions in `omega_measure_reduction.rs` cover neutral constructor facts,
  concrete and open list-tail bounds, an open tree with two recursive children
  interleaved with a payload field, skipped shadowed facts, rollback after a
  partially reflected fact, and constructor spelling under a lambda.

## Validation

- `scripts/test --fast -p heather-elab --test omega_measure_reduction`:
  18 passed, including the concrete/open tail bounds and shadowing controls.
- `scripts/test -p heather-elab --test display_surface`: 9 passed.
- `scripts/test -p heather-elab --test read_loop_process read_loop_library_checks`:
  passed with the inline `omega` proof.
- Final plain `scripts/test`: 3,037 passed, zero failed, **incomplete** because
  the combined `read_loop_process` group reached the 300 CPU-second rail.
  The native read-loop and read-print checks passed. The direct library check
  above verifies the changed process theorem independently of that group.
