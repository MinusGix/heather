---
title: "Method calls put the receiver last, which inverts every two-premise lemma"
status: open
labels: [frontend, syntax, elaboration, design]
created: 2026-07-27
updated: 2026-07-27
---

`x.f(a, b)` desugars to `f(a, b, x)` — the receiver is the **last** argument.
For a one-premise lemma that reads correctly; for a two-premise one it
inverts:

```heather
theorem trans<A>({a: A}, {b: A}, {c: A}, p: a = b, q: b = c): a = c

// given p: a = b and q: b = c, proving a = c —
q.trans(p)    ⇒  trans(p, q)    ✓   the receiver is the SECOND premise
p.trans(q)    ⇒  trans(q, p)    ✗   NotConvertible
```

So you write the *later* step as the receiver, which reads backwards against
every intuition `p.sym()` builds. Rust and Lean both put the subject first.

**The stated justification does not distinguish the two.** `parser.rs` said
the receiver is last "so with stage-2 implicit endpoints the earlier implicit
parameters are inferred from it (`p.sym()` ⇒ `sym(p)`,
`add_succ(n, k).sym()` ⇒ `sym(add_succ(n, k))`)". Both examples are **unary**,
where first and last are the same position — and the reason given is true of
receiver-first too, since implicit insertion is name-directed and does not
care about explicit-argument order. The convention was chosen on cases that
cannot tell the two apart, and the case that can was never written until
[[surface-records]]' regression suite wrote one.

## Why "just flip it" is not the whole answer

`cong` is a counterexample to *both* orders:

```heather
theorem cong(f: Nat -> Nat, {a}, {b}, p: a = b): f(a) = f(b)

p.cong(Succ)   receiver-last  ⇒ cong(Succ, p)   ✓
p.cong(Succ)   receiver-first ⇒ cong(p, Succ)   ✗
```

`trans` wants first, `cong` wants last. Neither position is right, because the
real property is **which parameter is the subject**, and that is a fact about
the *declaration*. Rust says it structurally (`self`); Lean gets it by
convention (subject first).

So a flip is really two things: the mechanism (receiver-first) **and** a
convention that lemmas are declared subject-first, with `cong`'s function
argument moving last.

## What the prototype measured (2026-07-27)

Flipped `resolve_dot` to `args.insert(0, recv)` and ran the suite.

**Mechanism: 5 small edits.** The desugaring itself, plus the argument
patterns of the four built-in special forms keyed on position (`map`, `fold`,
container-`cong`, `inj`).

**Real declarations: 1 test.** Only `constructor_values::cong_at_succ_by_name`
broke, and only because it declares `cong` function-first; re-declaring it
subject-first fixed it. `trans` needed **no change at all** — the prelude
already declares it `(p, q)`, so `p.trans(q)` ⇒ `trans(p, q)` reads forward
immediately. `sym`, `cong_succ` and `absurd` are unary and indifferent.

**Special forms: 8 tests, and this is the actual obstacle.** Every failure was
`inj`, and all for one reason: `inj` has a *documented direct-call spelling*
whose order was chosen to suit receiver-last.

```heather
inj(1, p)    // the direct spelling (tier-0 §6.3), index first
p.inj(1)     // the method spelling
```

Under receiver-last both arrive as `[k, arg]`. Under receiver-first the method
spelling arrives as `[arg, k]` while the direct spelling still means
`[k, arg]`, and they can no longer share one handler. `map`, `fold` and
container-`cong` have the same shape but no direct-call tests, so they merely
would have gone quietly wrong.

Three ways out, none free:

- **Flip the direct spellings too** — `inj(p, 1)`, `map(xs, f)`,
  `fold(xs, z, f)`. `map`/`fold` genuinely read *better* this way. `inj(p, 1)`
  reads worse than `inj(1, p)`, and it is documented syntax in a scheme
  document.
- **Make the special forms order-tolerant** (find the numeral). Hacky, and the
  hack would outlive the reason for it.
- **Wait for them to stop being special forms.** `inj`, `map` and `fold` are
  Rust that emits kernel terms, and [[generators-in-the-language]] says they
  belong in the meta layer. Once they are ordinary declarations they follow
  whatever convention ordinary declarations follow, and this dissolves.

## A hypothesis, tested and falsified

Worth recording so nobody re-derives it. I expected receiver-first to *also*
fix [[surface-operators]]' deferred `.cong(Wrap)` — the case
`docs/constructor-function-values.md` §5 leaves open — on the reasoning that
arguments elaborate left to right, so putting the informative receiver first
would let the constructor argument *check* against a known type instead of
*infer* against an unsolved meta.

**It does not.** Under the flip:

```heather
inductive Box { Wrap(v: Nat) }
theorem cong<A, B>({a: A}, {b: A}, p: a = b, f: A -> B): f(a) = f(b)
theorem method(n: Nat, m: Nat, p: n = m): Wrap(n) = Wrap(m) { p.cong(Wrap) }
// ERR: `Wrap` takes 1 argument(s), found 0     — both spellings, both orders
```

The proof `p` determines `A`, `a` and `b`. It says **nothing about `B`**,
which only `f` itself determines — so `f`'s expected type is `El A -> El B`
with `B` still a meta whichever order they are elaborated in, and
`build_ctor_value` cannot read a field layout off it. The blocker is
postponement ([[elab-unifier-completeness]]), exactly as
`constructor-function-values` logged it. Argument order is **orthogonal**.

## Recommendation

Receiver-first plus subject-first is the better convention and the prototype
says the *declaration* side of it is nearly free. It is gated on the special
forms, not on the idea.

Two orders to do it in:

1. **Now, taking the direct-spelling churn.** Flip, move `cong`'s function
   argument last, and decide `inj`'s direct spelling. Small, and it stops the
   surface teaching a convention that will be reversed.
2. **After [[generators-in-the-language]]**, when `inj`/`map`/`fold` are
   ordinary declarations and the obstacle is gone.

Leaning (1), because the convention is user-visible and every method call
written before the flip has to be rewritten after it — the cost grows with
delay, unlike the obstacle, which shrinks.

Either way, the end state is probably neither: an explicit receiver marker in
the declaration (`self`-style) makes the receiver **not positional at all**,
which is the same observation [[named-arguments]] makes one layer up. If that
is where this lands, subject-first is the right convention to be sitting on
when it arrives.

## Related

- [[named-arguments]] — the general form of "stop deciding this by position".
- [[generators-in-the-language]] — what removes the special-form obstacle.
- [[elab-unifier-completeness]] — the `.cong(Wrap)` blocker this is *not*.
- [[surface-records]] — where the inversion was first written down
  (docs/surface-records.md §11.3).

## Log

- 2026-07-27: Filed after prototyping the flip against the full suite. The
  prototype is not committed; its measurements are above. The headline is that
  the convention change is cheap for declarations (1 test, and `trans` needed
  nothing) and awkward only for the four built-in special forms keyed on
  argument position — and that the inference bonus I expected does not exist.
