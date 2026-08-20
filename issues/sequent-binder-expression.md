---
title: Checking-position sequent binders
status: closed
labels: [frontend,syntax,proofs,ergonomics]
created: 2026-08-19
updated: 2026-08-19
---

Proofs of implications and negations are functions, but the ordinary lambda
spelling foregrounds function construction where a proof often reads more
naturally as a judgment under an extended context. Add a checking-position
sequent binder:

```heather
theorem not_lt_of_ge(a, b: Int, h: a <= b): ¬ (b < a) {
    back ⊢ lt_irrefl(a, lt_of_le_of_lt(a, b, a, h, back))
}
```

`x ⊢ body` is exactly `λ x => body`: it introduces the domain of the
expected Pi under the requested name and checks `body` at the codomain. It is
term syntax, not a tactic command or a second goal state. The ASCII spelling is
`x |- body`, sharing the turnstile token contextual code types already use.

Several binders peel the expected Pi telescope in order:

```heather
hz hab ⊢ false_elim(hz)
```

An annotation is a checked assertion about the expected domain, not a source
of an unrelated inferred function type:

```heather
(back: b < a) ⊢ body
```

The turnstile has very low, right-associative precedence, so it needs no extra
block in a match arm:

```heather
Zero => bad ⊢ false_elim(bad),
Succ(k) => good ⊢ good,
```

At the head of a block it scopes over the remaining statements, allowing a
long proof without nested braces:

```heather
{
    back ⊢
    let cycle = lt_of_le_of_lt(a, b, a, h, back);
    lt_irrefl(a, cycle)
}
```

The parser lowers both forms to the existing `ExprKind::Lam`; the long form's
body is the existing transparent block expression. Dependent codomains,
annotations, checking behavior, and kernel terms therefore remain owned by the
lambda path.

## Acceptance

- One and several bare binders work in theorem bodies and match arms.
- `(x: A)` is checked against the corresponding expected domain.
- Dependent later domains and codomains see earlier binders.
- A sequent header scopes over the remaining `let`s and result of its block.
- A non-Pi goal and explicit/implicit mismatches use the lambda diagnostics.
- The emitted term is definitionally equal to the corresponding lambda.
- The parser accepts both `⊢` and `|-`, with `⊢` preferred in source.

## What it assumes from elsewhere

- **[[argument-slot-sections]]** owns anonymous, point-free introduction. This
  issue assumes only that named introduction should compose with it later.
- **[[surface-proof-automation]]** owns actual goal-transforming commands. A
  sequent binder deliberately adds none.

## Log

- 2026-08-19: Filed after rejecting `intro x;` as the default surface. The
  turnstile and an ordinary lambda have identical term meaning but different
  reading direction: `λ good => good` constructs a function; `good ⊢ good`
  reads as a judgment under the assumption `good`.
- 2026-08-19: Landed as parser lowering to `ExprKind::Lam`; the elaborator and
  kernel have no sequent case. `⊢` joins the existing `|-` token, binder runs
  and checked annotations mirror lambdas, and the form is the loosest,
  right-running expression so match arms need no braces. At a block result the
  header captures the remaining `let`s/result in a transparent lambda-body
  block while `on` discharges remain declaration-scoped. Seven acceptance
  tests pin Unicode/ASCII, dependent telescopes, annotations, arm precedence,
  long blocks, terminal `split`, goal discharge, definitional equality, and
  the inherited non-function refusal. The motivating Nat/Int arms and
  `not_lt_of_ge` now exercise the spelling. Full suite: 1943 passed.
