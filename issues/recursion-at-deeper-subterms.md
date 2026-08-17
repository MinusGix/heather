---
title: Structural recursion at a subterm deeper than the immediate predecessor
status: open
labels: [frontend,elaboration,kernel,design]
code: crates/elab/src/lib.rs:4609 @ 18c4931
created: 2026-08-17
updated: 2026-08-17
---

The evidence [[match-recursion]] asked for before widening. That issue chose
the strict rule deliberately — "self-calls only on the immediate predecessor
variable(s) bound by the enclosing match, and widen only with evidence" — and
this is the first library round to be stopped by it rather than inconvenienced.

`half` written the way anyone writes it:

```
fn half(n: Nat) -> Nat {
    match n {
        Zero => 0,
        Succ(k) => match k { Zero => 0, Succ(l) => Succ(half(l)) },
    }
}
```

```
error: recursive call to `half` must descend: argument `n` has to be `k`,
       the predecessor bound by the enclosing `match`
  |         Succ(k) => match k { Zero => 0, Succ(l) => Succ(half(l)) },
  |                                                              ^
```

`l` *is* structurally smaller than `n` — it is the predecessor of the
predecessor — so the message reads like a checker being needlessly strict.

## It is not the guard being too strict

That reading is wrong, and it is the main thing this issue exists to record.
A `fn`'s recursion is compiled into the kernel's **`ElimNat`**
(`elab_match_nat`, ~`crates/elab/src/lib.rs:4197` @ 18c4931): the `Succ(k)` arm
is the recursor's step, and the induction hypothesis it binds is `M[k/z]` —
the value at the immediate predecessor, because that is the only thing a
recursor *has*. Inside the nested `match k { Succ(l) => … }` the enclosing IH
is still the value at `k`, i.e. at `l + 1`. The value at `l` is not in scope
and cannot be derived from the value at `l + 1`.

So relaxing the comparison at `crates/elab/src/lib.rs:4557` would only move
the failure: the guard would accept the call and the elaborator would have no
term to emit for it. **This is an elaboration-strategy gap wearing a guard
message.** Whatever else this issue produces, the message should stop implying
a one-line fix — a reader who trusts it goes looking in the wrong file.

## The fix, costed

**Course-of-values by tupling.** A recursion whose deepest self-call is at
depth `d` is elaborated into one `ElimNat` computing the *last `d` values* as a
Σ-tuple, with the source function projected out of it:

    F(0)      = (f(0), …, f(1-d))          -- the declared base arms
    F(Succ k) = (step(π₀F(k), …, π_{d-1}F(k)), π₀F(k), …, π_{d-2}F(k))
    f(n)      = π₀ F(n)

The transformation on the *body* is local, which is the part that makes this
tractable: the nested `match` the source wrote stays exactly as written, and a
self-call at depth `d` becomes the `(d-1)`-th **projection of the tuple IH**.
For `half`, `d = 2`, `F(n) = (half(n), half(n-1))`:

    F(0)      = (0, 0)                        -- the `Zero` arm, and half(-1) := 0
    F(Succ k) = (match k { Zero    => 0       -- the source's `Succ(Zero)` arm
                         ; Succ(l) => Succ(π₁ F(k)) },   -- was `Succ(half(l))`
                 π₀ F(k))

`half(l)` became `π₁ F(k)` and nothing else moved. Note the base arms the
source already wrote (`Zero`, and `Succ(Zero)` inside the nested match) are
exactly what `F(0)` and the step's `Zero` case need — the information is
present in every well-written two-step recursion.

What it needs:

1. **A syntactic condition, and the source already meets it**: a depth-`d`
   recursion must supply base arms at every depth below `d`. `half` writes the
   `Zero` and `Succ(Zero)` arms explicitly; a recursion that does not write
   them has no `F(0)` and is refused, with a message that says which arm is
   missing.
2. **Σ in the emitted term.** Available — the branching-inductives round put
   Σ-tuple children in the kernel already ([[wf-former]],
   `docs/branching-inductives-choice.md`), so this is a new *use*, not a new
   former.
3. **Guard changes**: `GuardKind::Nat` records one `pred_pos`/`ih_pos` pair;
   it would record the chain of nested predecessors and which projection each
   depth's call resolves to.
4. **Reduction must survive.** The emitted term is still one `ElimNat`, so
   closed arguments still compute — `half(7) = 3 { refl }` has to keep
   working, and that is the acceptance test that matters, because it is the
   property `lib/std/nat.hthr` is written to keep throughout.

**The alternative — a kernel-level `fix` with a structural checker — is the
bigger change and pulls against the kernel's design** (eliminator-based, and
the checker would become trusted). Tupling keeps the trust boundary where it
is: a wrong analysis produces a term the kernel rejects, which is
[[match-recursion]]'s stated safety property.

## The workaround, probed and REJECTED

It works, so it is recorded here to stop it being rediscovered (it cost an
hour): a curried accumulator makes both blocked shapes one-step.

```
fn half2(n: Nat) -> Bool -> Nat {          // half2(n)(b) is (n + b) / 2
    match n {
        Zero => λ (b: Bool) => 0,
        Succ(k) => λ (b: Bool) =>
            match b { True => Succ(half2(k)(False)), False => half2(k)(True) },
    }
}
fn Parity(n: Nat) -> Bool -> Type {        // a SELECTOR between two types
    match n {
        Zero => λ (b: Bool) => match b { True => True, False => False },
        Succ(k) => λ (b: Bool) => Parity(k)(not(b)),
    }
}
```

Both check, both reduce (`half(7) = 3` and `Even(4)` are `refl`/`trivial`),
and `Even(n) → Odd(Succ n)` is even definitional. It was rejected anyway
(user, 2026-08-17): the library's job in this push is to *rank* language
features (`issues/std-api-waves.md`, "what hurts is the ranking function over
open issues"), and an encoding that works erases the datum. The flag is not
part of the notion of halving — unlike `Le`'s and `sub`'s currying, which is
forced by [[ih-generalization]] but leaves the concept's shape alone.

## Customers

- [[nat-parity-and-half]] — `half`, `Even`/`Odd`, blocked on this and carrying
  the intended spellings as a ready-made acceptance test.
- `fib`, the other classic two-step recursion.
- `log2`, binary representations, and anything digit-wise.
- `div`/`mod`/`gcd` want **well-founded** recursion rather than deep structural
  descent, so they are not customers of this fix — see [[termination-measures]].
  Worth deciding together, since a `Nat` division kit is what `Int` (wave I of
  [[std-api-waves]]) will reach for.

## What it assumes from elsewhere

- **[[match-recursion]]** (closed) owns the guarded-self-call design. Assumed
  here: only its stated strictness rule and its safety property — a wrong
  analysis is a kernel rejection, never a soundness hole.
- **[[termination-measures]]** owns non-structural termination (measures,
  mutual recursion, callee postconditions). Assumed here: nothing. This issue
  is strictly smaller — the descent is structural, just not by one.

## Acceptance

The `half`, `Even` and `Odd` spellings in [[nat-parity-and-half]] check as
written; `half(7) = 3` is `refl` and `Even(4)` is `trivial`; and a genuinely
non-descending self-call is still refused, with a message that names the
missing base arm when that is the actual problem.
